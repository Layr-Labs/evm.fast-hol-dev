"""Score a Yukon submission with the pinned hol-init-e verifier, which runs unchanged.

candidate/ holds rom.bin, claim.json and one of certificate.art, certificate.art.xz (one xz
stream) or certificate.art.zip (one stored or deflated entry named certificate.art); compressed
forms are expanded here under the verifier's 3 GiB article limit. It is copied into a fresh
three-file submission for `verifier/verify.py --local`. Yukon keeps the certificate out of Git:
the branch carries `<name>.yukon-ref.json`, the workflow fetches the file it names
(scripts/large_files.py), and the file must match its pointer before anything is copied.
"""
from __future__ import annotations

import errno
import json
import lzma
import os
from pathlib import Path
import stat
import struct
import subprocess
import sys
import uuid
import zipfile
import zlib

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
sys.path.insert(0, str(ROOT / "scripts"))
import large_files  # noqa: E402
import verify  # noqa: E402

CANDIDATE = ROOT / "candidate"
TOOLS = ROOT / "work"
CERTIFICATES = ("certificate.art", "certificate.art.xz", "certificate.art.zip")
CHUNK = 1 << 20
# Yukon scores are doubles and come back with 15 significant digits, so this sentinel reads back as
# 9007199254740990, as does every value from FINITE_LIMIT up. A finite K must stay below FINITE_LIMIT
# to remain distinguishable from infinity.
INFINITY_SCORE = 2**53 - 1
FINITE_LIMIT = 9_007_199_254_740_985
# The baseline replay took 8,973 s and peaked at 90.4 GiB RSS under 21,600 s and 112 GiB (an 84 GiB
# Poly/ML heap) on the author's host. The verifier applies the timeout to both CPU and wall time;
# match the author's limit so a slower runner CPU still fits.
TIMEOUT_SECONDS = 21_600
MEMORY_GIB = 112


class Invalid(ValueError):
    pass


def open_regular(path: Path):
    return os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW), "rb")


def copy_bounded(src, dst, limit: int, label: str) -> None:
    """Copies the stream in chunks, failing before more than limit bytes are written."""
    size = 0
    while chunk := src.read(CHUNK):
        size += len(chunk)
        if size > limit:
            raise Invalid(f"{label} exceeds {limit} bytes")
        dst.write(chunk)


def copy(source: Path, target: Path, limit: int) -> None:
    with open_regular(source) as src, target.open("xb") as dst:
        copy_bounded(src, dst, limit, source.name)


def expand_xz(source: Path, target: Path, limit: int) -> None:
    decompressor = lzma.LZMADecompressor(format=lzma.FORMAT_XZ, memlimit=2 * 1024**3)
    with open_regular(source) as src, target.open("xb") as dst:
        size = 0
        while not decompressor.eof:
            chunk = b""
            if decompressor.needs_input:
                chunk = src.read(CHUNK)
                if not chunk:
                    raise Invalid("certificate.art.xz is truncated")
            data = decompressor.decompress(chunk, max_length=16 * CHUNK)
            size += len(data)
            if size > limit:
                raise Invalid(f"certificate.art.xz expands beyond {limit} bytes")
            dst.write(data)
        if decompressor.unused_data or src.read(1):
            raise Invalid("certificate.art.xz has data after its xz stream")


def zip_entry_count(src) -> int:
    """Entries the end of central directory declares, read before zipfile parses the directory."""
    size = src.seek(0, os.SEEK_END)
    tail_size = min(size, 65535 + 22)
    src.seek(size - tail_size)
    tail = src.read(tail_size)
    end = tail.rfind(b"PK\x05\x06")
    if end < 0 or len(tail) - end < 22:
        raise Invalid("certificate.art.zip is not a zip archive")
    entries = struct.unpack_from("<H", tail, end + 10)[0]
    if entries != 0xFFFF:
        return entries
    locator = end - 20
    if locator < 0 or tail[locator:locator + 4] != b"PK\x06\x07":
        raise Invalid("certificate.art.zip has a damaged zip64 end record")
    src.seek(struct.unpack_from("<Q", tail, locator + 8)[0])
    record = src.read(56)
    if len(record) != 56 or record[:4] != b"PK\x06\x06":
        raise Invalid("certificate.art.zip has a damaged zip64 end record")
    return struct.unpack_from("<Q", record, 32)[0]


def expand_zip(source: Path, target: Path, limit: int) -> None:
    with open_regular(source) as src:
        if zip_entry_count(src) != 1:
            raise Invalid("certificate.art.zip must contain exactly one entry")
        src.seek(0)
        with zipfile.ZipFile(src) as archive:
            entries = archive.infolist()
            if len(entries) != 1:
                raise Invalid("certificate.art.zip must contain exactly one entry")
            info = entries[0]
            if info.filename != "certificate.art" or info.is_dir():
                raise Invalid("certificate.art.zip must contain only a file named certificate.art")
            if info.flag_bits & 0x1:
                raise Invalid("certificate.art.zip must not be encrypted")
            if info.compress_type not in (zipfile.ZIP_STORED, zipfile.ZIP_DEFLATED):
                raise Invalid("certificate.art.zip must be stored or deflated")
            # Python's zipfile records permission bits only (0o600); any recorded type must be a file.
            kind = stat.S_IFMT(info.external_attr >> 16)
            if kind and kind != stat.S_IFREG:
                raise Invalid("certificate.art.zip must hold a regular file")
            if info.file_size > limit:
                raise Invalid(f"certificate.art.zip declares more than {limit} bytes")
            # The declared size is not trusted: output is counted, and zipfile checks CRC-32 at the end.
            with archive.open(info) as stream, target.open("xb") as dst:
                copy_bounded(stream, dst, limit, "certificate.art expanded from certificate.art.zip")


def materialize(candidate: Path, destination: Path) -> str:
    """Copy candidate/ into a fresh submission directory; return how the article was supplied."""
    large_files.verify(ROOT)
    entries = {}
    pointers = {Path(path).name + large_files.POINTER_SUFFIX
                for slot in large_files.slots(ROOT) for path in slot["paths"] if (ROOT / path).parent == candidate}
    with os.scandir(candidate) as listing:
        for entry in listing:
            if entry.name in pointers:
                continue  # checked against its file by large_files.verify above
            if entry.name not in {"rom.bin", "claim.json", *CERTIFICATES}:
                raise Invalid(f"unexpected entry candidate/{entry.name}")
            if not entry.is_file(follow_symlinks=False):
                raise Invalid(f"candidate/{entry.name} must be a regular file")
            entries[entry.name] = Path(entry.path)
    if missing := {"rom.bin", "claim.json"} - entries.keys():
        raise Invalid(f"candidate/ is missing {', '.join(sorted(missing))}")
    if sum(name in entries for name in CERTIFICATES) > 1:
        raise Invalid("supply only one of certificate.art, certificate.art.xz and certificate.art.zip")
    destination.mkdir(mode=0o700)
    copy(entries["rom.bin"], destination / "rom.bin", verify.ROM_LIMIT)
    copy(entries["claim.json"], destination / "claim.json", 65536)
    article = destination / "certificate.art"
    if "certificate.art" in entries:
        copy(entries["certificate.art"], article, verify.PROOF_LIMIT)
        return "article"
    if "certificate.art.xz" in entries:
        expand_xz(entries["certificate.art.xz"], article, verify.PROOF_LIMIT)
        return "xz"
    if "certificate.art.zip" in entries:
        expand_zip(entries["certificate.art.zip"], article, verify.PROOF_LIMIT)
        return "zip"
    raise Invalid("candidate/ has no certificate.art, certificate.art.xz or certificate.art.zip")


def run_verifier(submission: Path, work: Path) -> dict:
    polyml = TOOLS / "polyml"
    env = dict(os.environ, PATH=f"{polyml / 'bin'}{os.pathsep}{os.environ.get('PATH', '')}",
               LD_LIBRARY_PATH=os.pathsep.join(filter(None, [str(polyml / "lib"), os.environ.get("LD_LIBRARY_PATH")])))
    # --progress sends stages and any heap preparation to stderr; the JSON report stays on stdout.
    command = [sys.executable, str(ROOT / "verifier" / "verify.py"), "--local", str(submission),
               "--trusted", str(ROOT), "--hol", str(TOOLS / "HOL"), "--work", str(work),
               "--timeout", str(TIMEOUT_SECONDS), "--memory-gib", str(MEMORY_GIB), "--progress"]
    process = subprocess.run(command, stdout=subprocess.PIPE, text=True, cwd=ROOT, env=env)
    try:
        report = json.loads(process.stdout)
    except ValueError:
        return {"status": "failed", "reason": "verifier printed no JSON report", "returncode": process.returncode}
    if not isinstance(report, dict):
        return {"status": "failed", "reason": "malformed verifier report", "returncode": process.returncode}
    if process.returncode != 0 and report.get("status") == "verified":
        return dict(report, status="failed", reason=f"verifier exited {process.returncode}")
    return report


def main() -> None:
    score_path = ROOT / "scripts" / "score.json"
    score_path.unlink(missing_ok=True)
    work = TOOLS / "yukon" / uuid.uuid4().hex
    work.mkdir(parents=True)
    try:
        source = materialize(CANDIDATE, work / "submission")
    except (OSError, ValueError, EOFError, lzma.LZMAError, zipfile.BadZipFile, zlib.error,
            large_files.LargeFileError) as exc:
        if isinstance(exc, OSError) and exc.errno in (errno.ENOSPC, errno.EDQUOT):
            raise SystemExit(f"Runner ran out of disk space preparing the candidate: {exc}")
        raise SystemExit(f"Invalid candidate: {exc}")
    print(f"Certificate supplied as: {source}", file=sys.stderr)
    report = run_verifier(work / "submission", work / "replay")
    print(json.dumps(report, sort_keys=True))
    if report.get("status") != "verified":
        raise SystemExit(f"Verifier did not accept the submission: {report.get('status')}")
    claim = report.get("K")
    if claim == "infinity":
        score = INFINITY_SCORE
    elif type(claim) is int and 0 <= claim < FINITE_LIMIT:
        score = claim
    else:
        raise SystemExit("K exceeds Yukon's exact integer range")
    contract = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True, cwd=ROOT).strip()
    metrics = {"claim": claim, "finite": claim != "infinity", "prover": "hol", "verification": "article",
               "romSha256": report["rom_sha256"], "proofSha256": report["proof_sha256"],
               "contractCommit": contract}
    temporary = score_path.with_suffix(".tmp")
    temporary.write_text(json.dumps({"score": score, "metrics": metrics}) + "\n")
    temporary.replace(score_path)


if __name__ == "__main__":
    main()
