"""Large candidate files that Yukon stores outside Git.

A slot path in benchmark.json `largeFiles` holds either the real file or, beside it, a canonical
pointer `<path>.yukon-ref.json` with its size and SHA-256. `fetch` (the workflow step) downloads
each pointer's file through Yukon using the run's GitHub OIDC token; `verify` (called by run.py)
requires every pointer to have a matching real file. No storage credentials or URLs live in this
repository or in workflow inputs: Yukon hands out a ten-minute download URL per object.
"""
from __future__ import annotations

import hashlib
import http.client
import json
import os
from pathlib import Path
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
TRACK = "hol"
POINTER_SUFFIX = ".yukon-ref.json"
POINTER_MAX_BYTES = 1024
DOWNLOAD_SUFFIX = ".yukon-download"
ALLOWED_APIS = ("https://api.yukon.org", "https://api-dev.yukon.org")
AUDIENCE = re.compile(r"yukon:large-files:[a-z0-9][a-z0-9._-]{0,63}")
SHA256 = re.compile(r"[0-9a-f]{64}")
CHUNK = 1 << 20
ATTEMPTS = 4


class LargeFileError(Exception):
    pass


class Transient(LargeFileError):
    pass


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    # A redirect would carry the bearer token to another origin; treat it as an error instead.
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


OPENER = urllib.request.build_opener(_NoRedirect())


def slots(root: Path = ROOT) -> list[dict]:
    manifest = json.loads((root / "benchmark.json").read_text())
    track = next(track for track in manifest["tracks"] if track["name"] == TRACK)
    return track.get("largeFiles", [])


def canonical(pointer: dict) -> bytes:
    fields = {"bytes": pointer["bytes"], "path": pointer["path"], "sha256": pointer["sha256"],
              "slot": pointer["slot"], "yukonLargeFile": 1}
    return (json.dumps(fields, separators=(",", ":"), ensure_ascii=False) + "\n").encode()


def read_pointer(root: Path, slot: dict, repo_path: str) -> dict | None:
    try:
        fd = os.open(root / (repo_path + POINTER_SUFFIX), os.O_RDONLY | os.O_NOFOLLOW)
    except FileNotFoundError:
        return None
    with os.fdopen(fd, "rb") as stream:
        raw = stream.read(POINTER_MAX_BYTES + 1)
    where = repo_path + POINTER_SUFFIX
    if len(raw) > POINTER_MAX_BYTES:
        raise LargeFileError(f"{where} is larger than {POINTER_MAX_BYTES} bytes")
    try:
        value = json.loads(raw)
    except ValueError:
        raise LargeFileError(f"{where} is not JSON") from None
    if not isinstance(value, dict) or sorted(value) != ["bytes", "path", "sha256", "slot", "yukonLargeFile"]:
        raise LargeFileError(f"{where} must have exactly bytes, path, sha256, slot and yukonLargeFile")
    if (value["yukonLargeFile"] != 1 or value["path"] != repo_path or value["slot"] != slot["name"]
            or type(value["bytes"]) is not int or not 1 <= value["bytes"] <= slot["maxBytes"]
            or not isinstance(value["sha256"], str) or not SHA256.fullmatch(value["sha256"])
            or canonical(value) != raw):
        raise LargeFileError(f"{where} is not a canonical pointer for slot {slot['name']}")
    return value


def pointers(root: Path = ROOT) -> list[dict]:
    found = []
    for slot in slots(root):
        in_slot = [p for p in (read_pointer(root, slot, path) for path in slot["paths"]) if p is not None]
        if len(in_slot) > 1:
            raise LargeFileError(f"slot {slot['name']} has more than one pointer")
        found.extend(in_slot)
    return found


def file_matches(path: Path, pointer: dict) -> bool:
    if path.is_symlink() or not path.is_file() or path.stat().st_size != pointer["bytes"]:
        return False
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest() == pointer["sha256"]


def verify(root: Path = ROOT) -> None:
    for pointer in pointers(root):
        target = root / pointer["path"]
        if not target.exists() and not target.is_symlink():
            raise LargeFileError(f"{pointer['path']} is missing; run `yukon setup --track {TRACK}` to download it")
        if not file_matches(target, pointer):
            raise LargeFileError(f"{pointer['path']} does not match {pointer['path']}{POINTER_SUFFIX}; "
                                 "delete one of them")


def _request(url: str, headers: dict, timeout: float):
    try:
        return OPENER.open(urllib.request.Request(url, headers=headers), timeout=timeout)
    except urllib.error.HTTPError as error:
        error.close()
        if error.code >= 500 or error.code in (408, 429):
            raise Transient(f"HTTP {error.code}") from None
        raise LargeFileError(f"HTTP {error.code}") from None
    except (urllib.error.URLError, TimeoutError, ConnectionError) as error:
        raise Transient(type(error).__name__) from None


def _json(url: str, headers: dict) -> dict:
    with _request(url, headers, 60) as response:
        value = json.loads(response.read(64 * 1024))
    if not isinstance(value, dict):
        raise LargeFileError("unexpected response")
    return value


def oidc_token(audience: str, environ) -> str:
    url, bearer = environ.get("ACTIONS_ID_TOKEN_REQUEST_URL"), environ.get("ACTIONS_ID_TOKEN_REQUEST_TOKEN")
    if not url or not bearer:
        raise LargeFileError("no GitHub OIDC token available; the workflow needs `permissions: id-token: write`")
    parts = urllib.parse.urlsplit(url)
    query = urllib.parse.urlencode([*urllib.parse.parse_qsl(parts.query), ("audience", audience)])
    token = _json(urllib.parse.urlunsplit(parts._replace(query=query)), {"Authorization": f"bearer {bearer}"}).get("value")
    if not isinstance(token, str) or not token:
        raise LargeFileError("GitHub returned no OIDC token")
    return token


def download(url: str, target: Path, pointer: dict) -> None:
    partial = target.with_name(target.name + DOWNLOAD_SUFFIX)
    partial.unlink(missing_ok=True)
    digest, size = hashlib.sha256(), 0
    try:
        with _request(url, {}, 120) as response, partial.open("xb") as out:
            while chunk := response.read(CHUNK):
                size += len(chunk)
                if size > pointer["bytes"]:
                    raise LargeFileError(f"{pointer['path']}: download is larger than {pointer['bytes']} bytes")
                digest.update(chunk)
                out.write(chunk)
        if size != pointer["bytes"]:
            raise Transient(f"{pointer['path']}: download ended after {size} of {pointer['bytes']} bytes")
        if digest.hexdigest() != pointer["sha256"]:
            raise LargeFileError(f"{pointer['path']}: downloaded bytes do not match the pointer's sha256")
        partial.replace(target)
    except (OSError, http.client.HTTPException) as error:
        raise Transient(f"{pointer['path']}: {type(error).__name__}") from None
    finally:
        partial.unlink(missing_ok=True)


def fetch(config_text: str, root: Path = ROOT, environ=os.environ, allowed=ALLOWED_APIS,
          allow_http_loopback: bool = False, sleep=time.sleep) -> list[str]:
    """Downloads every pointed-to file that is not already present; returns their paths."""
    if not config_text.strip():
        return []
    try:
        config = json.loads(config_text)
    except ValueError:
        raise LargeFileError("yukon_large_files is not JSON") from None
    if not isinstance(config, dict) or config.get("version") != 1:
        raise LargeFileError("yukon_large_files must be version 1")
    api, audience = config.get("api"), config.get("audience")
    if api not in allowed:
        raise LargeFileError(f"yukon_large_files api must be one of {', '.join(allowed)}")
    if not isinstance(audience, str) or not AUDIENCE.fullmatch(audience):
        raise LargeFileError("yukon_large_files audience is invalid")
    pending = [p for p in pointers(root) if not file_matches(root / p["path"], p)]
    if not pending:
        return []
    token = oidc_token(audience, environ)
    for pointer in pending:
        for attempt in range(1, ATTEMPTS + 1):
            try:
                grant = _json(f"{api}/api/internal/large-files/{pointer['sha256']}", {"Authorization": f"Bearer {token}"})
                if grant.get("sha256") != pointer["sha256"] or grant.get("bytes") != pointer["bytes"]:
                    raise LargeFileError(f"{pointer['path']}: Yukon describes a different object")
                url = grant.get("url")
                scheme_ok = isinstance(url, str) and (url.startswith("https://") or (
                    allow_http_loopback and url.startswith("http://127.0.0.1:")))
                if not scheme_ok:
                    raise LargeFileError(f"{pointer['path']}: Yukon returned an unusable download URL")
                download(url, root / pointer["path"], pointer)
                break
            except Transient as error:
                if attempt == ATTEMPTS:
                    raise LargeFileError(f"{pointer['path']}: giving up after {ATTEMPTS} attempts ({error})") from None
                sleep(min(2 ** attempt, 30))
    return [pointer["path"] for pointer in pending]


def main() -> None:
    if sys.argv[1:] != ["fetch"]:
        raise SystemExit("usage: large_files.py fetch")
    try:
        fetched = fetch(os.environ.get("YUKON_LARGE_FILES", ""))
    except LargeFileError as error:
        raise SystemExit(f"large-file fetch failed: {error}")
    print(f"fetched {len(fetched)} large file(s): {', '.join(fetched) or 'none needed'}")


if __name__ == "__main__":
    main()
