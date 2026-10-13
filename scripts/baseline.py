"""The operator-published baseline article, pinned by upstream's verification record."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
ARTICLE = ROOT / "work" / "baseline" / "certificate.art"


def expected() -> dict:
    record = json.loads((ROOT / "artifacts" / "baseline" / "verification.json").read_text())
    return {"rom_sha256": record["result"]["rom_sha256"], "proof_sha256": record["result"]["proof_sha256"],
            "proof_bytes": record["proof_bytes"]}


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def article_matches(path: Path) -> bool:
    pins = expected()
    return (path.is_file() and not path.is_symlink() and path.stat().st_size == pins["proof_bytes"]
            and sha256(path) == pins["proof_sha256"])


if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[1] != "check":
        raise SystemExit("usage: baseline.py check ARTICLE")
    if not article_matches(Path(sys.argv[2])):
        raise SystemExit("baseline article missing or does not match artifacts/baseline/verification.json")
