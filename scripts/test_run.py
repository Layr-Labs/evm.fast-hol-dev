"""Score mapping and fail-closed checks for scripts/run.py, with the verifier mocked."""
from __future__ import annotations

import errno
import hashlib
import io
import json
import lzma
from pathlib import Path
import stat
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import zipfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run  # noqa: E402

REPO = Path(__file__).resolve().parent.parent

ROM = b"\x13\x00\x00\x00"
ARTICLE = b"1\n2\nnil\n" * 1000


def zip_bytes(entries, compression=zipfile.ZIP_DEFLATED) -> bytearray:
    """entries: (name, data, unix mode or None)."""
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w", compression) as archive:
        for name, data, mode in entries:
            info = zipfile.ZipInfo(name)
            info.compress_type = compression
            if mode is not None:
                info.external_attr = mode << 16
            archive.writestr(info, data)
    return bytearray(buffer.getvalue())


def patch_entry(data: bytearray, fmt: str, local_offset: int, central_offset: int, value) -> bytearray:
    """Sets one field in the first entry's local header and its central directory record."""
    struct.pack_into(fmt, data, local_offset, value)
    struct.pack_into(fmt, data, data.find(b"PK\x01\x02") + central_offset, value)
    return data


class Harness(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "scripts").mkdir()
        self.candidate = self.root / "candidate"
        self.candidate.mkdir()
        (self.candidate / "rom.bin").write_bytes(ROM)
        (self.candidate / "claim.json").write_text('{"K":"infinity"}')
        (self.root / "benchmark.json").write_bytes((REPO / "benchmark.json").read_bytes())
        self.patches = [patch.object(run, "ROOT", self.root), patch.object(run, "CANDIDATE", self.candidate),
                        patch.object(run, "TOOLS", self.root / "work")]
        for p in self.patches:
            p.start()
            self.addCleanup(p.stop)
        self.score = self.root / "scripts" / "score.json"

    def verifier(self, report, returncode=0, stdout=None):
        completed = subprocess.CompletedProcess([], returncode, stdout=stdout if stdout is not None else json.dumps(report))

        def fake(command, **kwargs):
            self.assertTrue(command[1].endswith("verifier/verify.py"))
            self.assertEqual(command[command.index("--timeout") + 1:command.index("--timeout") + 4],
                             [str(run.TIMEOUT_SECONDS), "--memory-gib", str(run.MEMORY_GIB)])
            submission = Path(command[command.index("--local") + 1])
            self.submitted = {p.name: p.read_bytes() for p in submission.iterdir()}
            return completed
        return patch.object(run.subprocess, "run", fake)

    def run_main(self, report, **kwargs):
        with self.verifier(report, **kwargs), patch.object(run.subprocess, "check_output", return_value="abc123\n"):
            run.main()
        return json.loads(self.score.read_text())

    def report(self, K):
        return {"status": "verified", "K": K, "rom_bytes": 4, "rom_sha256": "r" * 64, "proof_sha256": "p" * 64}

    def test_infinity_scores_max_safe_integer(self):
        (self.candidate / "certificate.art").write_bytes(ARTICLE)
        result = self.run_main(self.report("infinity"))
        self.assertEqual(result["score"], 2**53 - 1)
        self.assertEqual(result["metrics"], {"claim": "infinity", "finite": False, "prover": "hol",
                                             "verification": "article", "romSha256": "r" * 64,
                                             "proofSha256": "p" * 64, "contractCommit": "abc123"})
        self.assertEqual(self.submitted["certificate.art"], ARTICLE)

    def test_finite_k_is_the_score(self):
        (self.candidate / "certificate.art").write_bytes(ARTICLE)
        for K in [0, 123, run.FINITE_LIMIT - 1]:
            result = self.run_main(self.report(K))
            self.assertEqual((result["score"], result["metrics"]["claim"], result["metrics"]["finite"]), (K, K, True))

    def test_k_at_rounding_limit_fails_closed(self):
        (self.candidate / "certificate.art").write_bytes(ARTICLE)
        for K in [run.FINITE_LIMIT, 2**53 - 1, 2**64, -1, True, "7", 1.5]:
            self.score.write_text("stale")
            with self.assertRaises(SystemExit):
                self.run_main(self.report(K))
            self.assertFalse(self.score.exists())

    def test_rejection_deletes_stale_score(self):
        (self.candidate / "certificate.art").write_bytes(ARTICLE)
        for report, kwargs in [({"status": "rejected", "reason": "x"}, {"returncode": 1}),
                               ({"status": "incomplete"}, {"returncode": 2}),
                               (None, {"stdout": "not json"}),
                               (None, {"stdout": "[]"}),
                               (self.report("infinity"), {"returncode": 1})]:
            self.score.write_text("stale")
            with self.assertRaises(SystemExit):
                self.run_main(report, **kwargs)
            self.assertFalse(self.score.exists())

    def test_xz_certificate_is_expanded(self):
        (self.candidate / "certificate.art.xz").write_bytes(lzma.compress(ARTICLE))
        self.run_main(self.report("infinity"))
        self.assertEqual(self.submitted["certificate.art"], ARTICLE)
        self.assertEqual(set(self.submitted), {"rom.bin", "claim.json", "certificate.art"})

    def invalid(self):
        self.score.write_text("stale")
        with self.assertRaises(SystemExit), self.verifier(self.report(1)):
            run.main()
        self.assertFalse(self.score.exists())

    def test_disk_full_is_reported_as_such(self):
        class FullDisk:
            def __init__(self, handle):
                self.handle = handle

            def __enter__(self):
                return self

            def __exit__(self, *exc):
                self.handle.close()

            def write(self, data):
                raise OSError(errno.ENOSPC, "No space left on device")

        real_open = Path.open

        def open_full(path, mode="r", *args, **kwargs):
            handle = real_open(path, mode, *args, **kwargs)
            return FullDisk(handle) if "x" in mode and path.name == "certificate.art" else handle

        for name, data in (("certificate.art", ARTICLE), ("certificate.art.zip", bytes(zip_bytes([("certificate.art", ARTICLE, None)])))):
            for other in run.CERTIFICATES:
                (self.candidate / other).unlink(missing_ok=True)
            (self.candidate / name).write_bytes(data)
            self.score.write_text("stale")
            with patch.object(run.Path, "open", open_full), self.verifier(self.report(1)):
                with self.assertRaises(SystemExit) as raised:
                    run.main()
            self.assertIn("out of disk space", str(raised.exception.code))
            self.assertNotIn("Invalid candidate", str(raised.exception.code))
            self.assertFalse(self.score.exists())

    def test_xz_bomb_truncation_and_trailing_data_rejected(self):
        packed = lzma.compress(ARTICLE)
        for data, limit in [(packed, len(ARTICLE) - 1), (packed[:-8], 1 << 30), (packed + b"x", 1 << 30),
                            (b"not xz", 1 << 30)]:
            (self.candidate / "certificate.art.xz").write_bytes(data)
            with patch.object(run.verify, "PROOF_LIMIT", limit):
                self.invalid()

    def write_zip(self, data):
        (self.candidate / "certificate.art.zip").write_bytes(bytes(data))

    def test_zip_certificate_is_expanded(self):
        # zip(1) records S_IFREG|0644, Python's zipfile 0o600 with no type, some tools nothing.
        for compression, mode in ((zipfile.ZIP_DEFLATED, stat.S_IFREG | 0o644), (zipfile.ZIP_STORED, 0o600),
                                  (zipfile.ZIP_DEFLATED, 0)):
            self.write_zip(zip_bytes([("certificate.art", ARTICLE, mode)], compression))
            self.run_main(self.report("infinity"))
            self.assertEqual(self.submitted["certificate.art"], ARTICLE)
            self.assertEqual(set(self.submitted), {"rom.bin", "claim.json", "certificate.art"})

    def test_zip_must_hold_only_certificate_art(self):
        for entries in ([("certificate.art", ARTICLE, None), ("extra", b"x", None)],
                        [("proof.art", ARTICLE, None)],
                        [("certificate.art/", b"", stat.S_IFDIR | 0o755)],
                        [("certificate.art", b"/etc/passwd", stat.S_IFLNK | 0o777)],
                        [("certificate.art", b"", stat.S_IFIFO | 0o644)],
                        [("../certificate.art", ARTICLE, None)]):
            self.write_zip(zip_bytes(entries))
            self.invalid()

    def test_zip_encryption_and_other_methods_rejected(self):
        self.write_zip(patch_entry(zip_bytes([("certificate.art", ARTICLE, None)]), "<H", 6, 8, 0x1))
        self.invalid()
        for method in (9, 12, 14):  # Deflate64, bzip2, lzma
            self.write_zip(patch_entry(zip_bytes([("certificate.art", ARTICLE, None)]), "<H", 8, 10, method))
            self.invalid()

    def test_zip_bombs_rejected(self):
        packed = zip_bytes([("certificate.art", ARTICLE, None)])
        self.write_zip(packed)
        with patch.object(run.verify, "PROOF_LIMIT", len(ARTICLE) - 1):
            self.invalid()  # declared size over the limit
        # Declares 10 bytes but inflates to the whole article: output stops at the declared size
        # and the CRC check fails, and a limit below the real size is never exceeded.
        self.write_zip(patch_entry(bytearray(packed), "<I", 22, 24, 10))
        with patch.object(run.verify, "PROOF_LIMIT", 100):
            self.invalid()
        self.invalid()

    def test_zip_truncation_and_crc_mismatch_rejected(self):
        packed = zip_bytes([("certificate.art", ARTICLE, None)])
        for data in (packed[:-10], packed[:len(packed) // 2], b"not a zip at all"):
            self.write_zip(data)
            self.invalid()
        crc = struct.unpack_from("<I", packed, 14)[0]
        self.write_zip(patch_entry(bytearray(packed), "<I", 14, 16, crc ^ 1))
        self.invalid()

    def test_zip_entry_count_checked_before_parsing(self):
        packed = zip_bytes([("certificate.art", ARTICLE, None)])
        end = packed.rfind(b"PK\x05\x06")
        struct.pack_into("<HH", packed, end + 8, 50000, 50000)
        self.write_zip(packed)
        with patch.object(run.zipfile, "ZipFile", side_effect=AssertionError("parsed")):
            self.invalid()
        many = zip_bytes([(f"f{index}", b"", None) for index in range(65536)], zipfile.ZIP_STORED)
        self.assertNotEqual(many.rfind(b"PK\x06\x06"), -1)  # zip64 end record
        with open(self.root / "many.zip", "wb") as handle:
            handle.write(many)
        with run.open_regular(self.root / "many.zip") as handle:
            self.assertEqual(run.zip_entry_count(handle), 65536)

    def test_only_one_certificate_form(self):
        self.write_zip(zip_bytes([("certificate.art", ARTICLE, None)]))
        (self.candidate / "certificate.art.xz").write_bytes(lzma.compress(ARTICLE))
        self.invalid()
        (self.candidate / "certificate.art.xz").unlink()
        (self.candidate / "certificate.art").write_bytes(ARTICLE)
        self.invalid()

    def test_bad_candidate_layouts_rejected(self):
        (self.candidate / "certificate.art").write_bytes(ARTICLE)
        (self.candidate / "extra.sml").write_text("")
        self.invalid()
        (self.candidate / "extra.sml").unlink()
        (self.candidate / "certificate.art.xz").write_bytes(lzma.compress(ARTICLE))
        self.invalid()
        (self.candidate / "certificate.art.xz").unlink()
        (self.candidate / "claim.json").unlink()
        self.invalid()
        (self.candidate / "claim.json").symlink_to(self.root / "scripts")
        self.invalid()

    def test_symlinked_certificate_rejected(self):
        outside = self.root / "outside.art"
        outside.write_bytes(ARTICLE)
        (self.candidate / "certificate.art").symlink_to(outside)
        self.invalid()

    def pointer(self, name, data):
        pointer = {"bytes": len(data), "path": f"candidate/{name}", "sha256": hashlib.sha256(data).hexdigest(),
                   "slot": "certificate", "yukonLargeFile": 1}
        (self.candidate / f"{name}.yukon-ref.json").write_bytes(run.large_files.canonical(pointer))

    def test_missing_certificate_rejected(self):
        self.invalid()

    def test_pointer_with_its_file_is_used_and_not_submitted(self):
        packed = bytes(zip_bytes([("certificate.art", ARTICLE, None)]))
        self.write_zip(packed)
        self.pointer("certificate.art.zip", packed)
        self.run_main(self.report("infinity"))
        self.assertEqual(set(self.submitted), {"rom.bin", "claim.json", "certificate.art"})
        self.assertEqual(self.submitted["certificate.art"], ARTICLE)

    def test_only_pointers_for_declared_slot_paths_are_skipped(self):
        manifest = json.loads((self.root / "benchmark.json").read_text())
        manifest["tracks"][0]["largeFiles"][0]["paths"].remove("candidate/certificate.art")
        (self.root / "benchmark.json").write_text(json.dumps(manifest))
        (self.candidate / "certificate.art.zip").write_bytes(bytes(zip_bytes([("certificate.art", ARTICLE, None)])))
        (self.candidate / "certificate.art.yukon-ref.json").write_text("{}")
        with self.assertRaises(SystemExit) as raised, self.verifier(self.report(1)):
            run.main()
        self.assertIn("unexpected entry candidate/certificate.art.yukon-ref.json", str(raised.exception.code))

    def test_pointer_without_its_file_or_with_another_file_rejected(self):
        packed = bytes(zip_bytes([("certificate.art", ARTICLE, None)]))
        self.pointer("certificate.art.zip", packed)
        with self.assertRaises(SystemExit) as raised, self.verifier(self.report(1)):
            run.main()
        self.assertIn("yukon setup --track hol", str(raised.exception))
        self.write_zip(zip_bytes([("certificate.art", ARTICLE + b"x", None)]))
        self.invalid()  # file differs from its pointer
        (self.candidate / "certificate.art.zip").unlink()
        (self.candidate / "certificate.art").write_bytes(ARTICLE)
        self.invalid()  # a different format than the pointer names
        (self.candidate / "certificate.art").unlink()
        self.write_zip(packed)
        (self.candidate / "certificate.art.zip.yukon-ref.json").write_text('{"bytes": 1}')
        self.invalid()  # not a canonical pointer


class BaselinePins(unittest.TestCase):
    def test_baseline_pointer_names_upstream_zip(self):
        compression = json.loads((REPO / "artifacts" / "baseline" / "certificate-compression.json").read_text())
        manifest = json.loads((REPO / "artifacts" / "baseline" / "manifest.json").read_text())
        verification = json.loads((REPO / "artifacts" / "baseline" / "verification.json").read_text())
        self.assertEqual(run.large_files.pointers(REPO), [{
            "bytes": compression["zip_bytes"], "path": "candidate/certificate.art.zip",
            "sha256": compression["zip_sha256"], "slot": "certificate", "yukonLargeFile": 1}])
        self.assertEqual(compression["sha256"], verification["result"]["proof_sha256"])
        self.assertEqual(hashlib.sha256((REPO / "candidate" / "rom.bin").read_bytes()).hexdigest(),
                         manifest["files"]["rom.bin"]["sha256"])
        self.assertEqual(json.loads((REPO / "candidate" / "claim.json").read_text()), {"K": "infinity"})


if __name__ == "__main__":
    unittest.main()
