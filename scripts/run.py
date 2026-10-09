"""Score a Yukon submission with the pinned hol-init-e verifier, which runs unchanged.

candidate/ holds rom.bin, claim.json and either certificate.art or certificate.art.xz (one xz
stream, expanded here under the verifier's 2 GiB article limit). It is copied into a fresh
three-file submission for `verifier/verify.py --local`. Only the unchanged baseline ROM with
the infinity claim may omit the certificate; it then uses the operator-published baseline
article that scripts/setup.sh fetched and checked against artifacts/baseline/verification.json.
"""
from __future__ import annotations

import json
import lzma
import os
from pathlib import Path
import subprocess
import sys
import uuid

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
sys.path.insert(0, str(ROOT / "scripts"))
import baseline  # noqa: E402
import verify  # noqa: E402

CANDIDATE = ROOT / "candidate"
TOOLS = ROOT / "work"
CERTIFICATES = ("certificate.art", "certificate.art.xz")
CHUNK = 1 << 20
# Yukon scores are doubles and come back with 15 significant digits, so this sentinel reads back as
# 9007199254740990, as does every value from FINITE_LIMIT up. A finite K must stay below FINITE_LIMIT
# to remain distinguishable from infinity.
INFINITY_SCORE = 2**53 - 1
FINITE_LIMIT = 9_007_199_254_740_985
# The baseline replay took 8,727 s and peaked at 90.54 GiB RSS under 10,800 s and 112 GiB on the
# author's host. The verifier applies the timeout to both CPU and wall time; leave room for a
# slower runner CPU.
TIMEOUT_SECONDS = 14_400
MEMORY_GIB = 112


class Invalid(ValueError):
    pass


def open_regular(path: Path):
    return os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW), "rb")


def copy(source: Path, target: Path, limit: int) -> None:
    with open_regular(source) as src, target.open("xb") as dst:
        size = 0
        while chunk := src.read(CHUNK):
            size += len(chunk)
            if size > limit:
                raise Invalid(f"{source.name} exceeds {limit} bytes")
            dst.write(chunk)


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


def materialize(candidate: Path, destination: Path) -> str:
    """Copy candidate/ into a fresh submission directory; return how the article was supplied."""
    entries = {}
    with os.scandir(candidate) as listing:
        for entry in listing:
            if entry.name not in {"rom.bin", "claim.json", *CERTIFICATES}:
                raise Invalid(f"unexpected entry candidate/{entry.name}")
            if not entry.is_file(follow_symlinks=False):
                raise Invalid(f"candidate/{entry.name} must be a regular file")
            entries[entry.name] = Path(entry.path)
    if missing := {"rom.bin", "claim.json"} - entries.keys():
        raise Invalid(f"candidate/ is missing {', '.join(sorted(missing))}")
    if all(name in entries for name in CERTIFICATES):
        raise Invalid("supply certificate.art or certificate.art.xz, not both")
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
    claim = json.loads((destination / "claim.json").read_bytes())
    if baseline.sha256(destination / "rom.bin") != baseline.expected()["rom_sha256"] or claim != {"K": "infinity"}:
        raise Invalid("candidate/ has no certificate; only the unchanged baseline ROM claiming infinity may omit it")
    if not baseline.article_matches(baseline.ARTICLE):
        raise Invalid("the baseline article is unavailable: scripts/setup.sh fetches it from the URL in "
                      "scripts/baseline-article.json")
    copy(baseline.ARTICLE, article, verify.PROOF_LIMIT)
    return "baseline"


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
    except (OSError, ValueError, lzma.LZMAError) as exc:
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
