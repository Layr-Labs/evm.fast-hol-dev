"""Score mapping and fail-closed checks for scripts/run.py, with the verifier mocked."""
from __future__ import annotations

import hashlib
import json
import lzma
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run  # noqa: E402

ROM = b"\x13\x00\x00\x00"
ARTICLE = b"1\n2\nnil\n" * 1000


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
        self.baseline_article = self.root / "work" / "baseline" / "certificate.art"
        pins = {"rom_sha256": hashlib.sha256(ROM).hexdigest(),
                "proof_sha256": hashlib.sha256(ARTICLE).hexdigest(), "proof_bytes": len(ARTICLE)}
        self.patches = [patch.object(run, "ROOT", self.root), patch.object(run, "CANDIDATE", self.candidate),
                        patch.object(run, "TOOLS", self.root / "work"),
                        patch.object(run.baseline, "ARTICLE", self.baseline_article),
                        patch.object(run.baseline, "expected", lambda: pins)]
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

    def test_xz_bomb_truncation_and_trailing_data_rejected(self):
        packed = lzma.compress(ARTICLE)
        for data, limit in [(packed, len(ARTICLE) - 1), (packed[:-8], 1 << 30), (packed + b"x", 1 << 30),
                            (b"not xz", 1 << 30)]:
            (self.candidate / "certificate.art.xz").write_bytes(data)
            with patch.object(run.verify, "PROOF_LIMIT", limit):
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

    def test_baseline_uses_published_article(self):
        self.baseline_article.parent.mkdir(parents=True)
        self.baseline_article.write_bytes(ARTICLE)
        self.run_main(self.report("infinity"))
        self.assertEqual(self.submitted["certificate.art"], ARTICLE)

    def test_baseline_fallback_requires_exact_rom_claim_and_article(self):
        self.invalid()  # article not published
        self.baseline_article.parent.mkdir(parents=True)
        self.baseline_article.write_bytes(ARTICLE + b"x")
        self.invalid()  # article does not match the pinned hash and size
        self.baseline_article.write_bytes(ARTICLE)
        (self.candidate / "claim.json").write_text('{"K":5}')
        self.invalid()
        (self.candidate / "claim.json").write_text('{"K":"infinity"}')
        (self.candidate / "rom.bin").write_bytes(ROM + b"\x00")
        self.invalid()


if __name__ == "__main__":
    unittest.main()
