"""scripts/large_files.py against a local stand-in for GitHub's token service, Yukon and storage."""
from __future__ import annotations

import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
from pathlib import Path
import sys
import tempfile
import threading
import unittest
import urllib.parse

sys.path.insert(0, str(Path(__file__).resolve().parent))
import large_files  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
DATA = b"certificate bytes " * 4096
AUDIENCE = "yukon:large-files:dev"


class Server:
    """Routes: /token (GitHub), /api/internal/large-files/<sha> (Yukon), /object (storage)."""

    def __init__(self):
        self.requests: list[tuple[str, dict]] = []
        self.api_responses: list[tuple[int, dict | None, dict]] = []
        self.object_bodies: list[bytes] = []
        self.grant: dict = {}
        server = self

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, *args):
                pass

            def send(self, status, body=b"", headers=None):
                self.send_response(status)
                for name, value in (headers or {}).items():
                    self.send_header(name, value)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def do_GET(self):
                url = urllib.parse.urlsplit(self.path)
                server.requests.append((url.path + ("?" + url.query if url.query else ""), dict(self.headers)))
                if url.path == "/token":
                    self.send(200, json.dumps({"value": "oidc-token"}).encode())
                elif url.path.startswith("/api/internal/large-files/"):
                    status, body, headers = server.api_responses.pop(0) if server.api_responses else (200, server.grant, {})
                    self.send(status, json.dumps(body).encode() if body is not None else b"", headers)
                elif url.path == "/object":
                    body = server.object_bodies.pop(0) if len(server.object_bodies) > 1 else server.object_bodies[0]
                    # Declares the real size, then may send fewer bytes (a dropped connection).
                    self.send_response(200)
                    self.send_header("Content-Length", str(len(DATA) if len(body) < len(DATA) else len(body)))
                    self.end_headers()
                    self.wfile.write(body)
                else:
                    self.send(404)

        self.httpd = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.origin = f"http://127.0.0.1:{self.httpd.server_address[1]}"
        threading.Thread(target=self.httpd.serve_forever, daemon=True).start()

    def paths(self, prefix):
        return [(path, headers) for path, headers in self.requests if path.startswith(prefix)]

    def close(self):
        self.httpd.shutdown()
        self.httpd.server_close()


class Fetch(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "benchmark.json").write_bytes((REPO / "benchmark.json").read_bytes())
        (self.root / "candidate").mkdir()
        self.server = Server()
        self.addCleanup(self.server.close)
        self.pointer = self.write_pointer("certificate.art.zip", DATA)
        self.server.object_bodies = [DATA]
        self.server.grant = {"url": f"{self.server.origin}/object", "sha256": self.pointer["sha256"],
                             "bytes": len(DATA), "expiresAt": "2026-01-01T00:00:00Z"}
        self.environ = {"ACTIONS_ID_TOKEN_REQUEST_URL": f"{self.server.origin}/token?api-version=2.0",
                        "ACTIONS_ID_TOKEN_REQUEST_TOKEN": "runtime-token"}
        self.sleeps: list[float] = []

    def write_pointer(self, name, data, slot="certificate"):
        pointer = {"bytes": len(data), "path": f"candidate/{name}", "sha256": hashlib.sha256(data).hexdigest(),
                   "slot": slot, "yukonLargeFile": 1}
        (self.root / "candidate" / f"{name}.yukon-ref.json").write_bytes(large_files.canonical(pointer))
        return pointer

    def config(self, **overrides):
        return json.dumps({"version": 1, "api": self.server.origin, "audience": AUDIENCE, **overrides})

    def fetch(self, config=None, **kwargs):
        return large_files.fetch(self.config() if config is None else config, root=self.root, environ=self.environ,
                                 allowed=(self.server.origin,), allow_http_loopback=True,
                                 sleep=self.sleeps.append, **kwargs)

    def target(self):
        return self.root / "candidate" / "certificate.art.zip"

    def assert_no_file(self):
        self.assertFalse(self.target().exists())
        self.assertEqual(list((self.root / "candidate").glob("*.yukon-download")), [])

    def test_fetches_and_verifies_with_the_runs_oidc_token(self):
        self.assertEqual(self.fetch(), ["candidate/certificate.art.zip"])
        self.assertEqual(self.target().read_bytes(), DATA)
        [(token_path, token_headers)] = self.server.paths("/token")
        self.assertEqual(urllib.parse.parse_qs(urllib.parse.urlsplit(token_path).query),
                         {"api-version": ["2.0"], "audience": [AUDIENCE]})
        self.assertEqual(token_headers["Authorization"], "bearer runtime-token")
        [(api_path, api_headers)] = self.server.paths("/api/")
        self.assertEqual(api_path, f"/api/internal/large-files/{self.pointer['sha256']}")
        self.assertEqual(api_headers["Authorization"], "Bearer oidc-token")
        [(_, object_headers)] = self.server.paths("/object")
        self.assertNotIn("Authorization", object_headers)
        large_files.verify(self.root)

    def test_nothing_to_do_without_input_or_when_the_file_is_present(self):
        self.assertEqual(self.fetch(config=""), [])
        self.target().write_bytes(DATA)
        self.assertEqual(self.fetch(), [])
        self.assertEqual(self.server.requests, [])

    def test_rejects_unlisted_origins_and_malformed_input_before_any_request(self):
        for config in (self.config(api="https://evil.example"), self.config(version=2), self.config(audience="other"),
                       self.config(audience="yukon:large-files:"), "not json", "[]"):
            with self.assertRaises(large_files.LargeFileError):
                self.fetch(config=config)
        with self.assertRaises(large_files.LargeFileError) as raised:
            large_files.fetch(self.config(), root=self.root, environ=self.environ, sleep=self.sleeps.append)
        self.assertIn("https://api.yukon.org", str(raised.exception))
        self.assertEqual(self.server.requests, [])

    def test_requires_the_id_token_permission(self):
        self.environ = {}
        with self.assertRaises(large_files.LargeFileError) as raised:
            self.fetch()
        self.assertIn("id-token: write", str(raised.exception))

    def test_hash_mismatch_and_oversized_downloads_fail_without_a_file(self):
        corrupted = bytearray(DATA)
        corrupted[0] ^= 1
        for body, message in ((bytes(corrupted), "do not match"), (DATA + b"x", "larger than")):
            self.server.object_bodies = [body]
            with self.assertRaises(large_files.LargeFileError) as raised:
                self.fetch()
            self.assertIn(message, str(raised.exception))
            self.assert_no_file()
        self.assertEqual(self.sleeps, [])

    def test_truncated_downloads_and_server_errors_are_retried(self):
        self.server.object_bodies = [DATA[:100], DATA]
        self.server.api_responses = [(503, None, {}), (200, self.server.grant, {})]
        self.assertEqual(self.fetch(), ["candidate/certificate.art.zip"])
        self.assertEqual(len(self.sleeps), 2)
        self.assertEqual(self.target().read_bytes(), DATA)

    def test_gives_up_after_the_attempt_limit(self):
        self.server.object_bodies = [DATA[:100]]
        with self.assertRaises(large_files.LargeFileError) as raised:
            self.fetch()
        self.assertIn(f"after {large_files.ATTEMPTS} attempts", str(raised.exception))
        self.assertEqual(len(self.server.paths("/object")), large_files.ATTEMPTS)
        self.assert_no_file()

    def test_refusals_are_not_retried_and_redirects_are_not_followed(self):
        self.server.api_responses = [(403, {"error": {"code": "large_file_forbidden"}}, {})]
        with self.assertRaises(large_files.LargeFileError):
            self.fetch()
        self.server.api_responses = [(302, None, {"Location": f"{self.server.origin}/token-thief"})]
        with self.assertRaises(large_files.LargeFileError):
            self.fetch()
        self.assertEqual(self.server.paths("/token-thief"), [])
        self.assertEqual(self.sleeps, [])

    def test_rejects_grants_for_another_object_or_with_unusable_urls(self):
        for grant in ({**self.server.grant, "bytes": len(DATA) + 1}, {**self.server.grant, "sha256": "0" * 64},
                      {**self.server.grant, "url": "http://example.com/object"}, {**self.server.grant, "url": None}):
            self.server.api_responses = [(200, grant, {})]
            with self.assertRaises(large_files.LargeFileError):
                self.fetch()
        self.assertEqual(self.server.paths("/object"), [])


class Verify(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "benchmark.json").write_bytes((REPO / "benchmark.json").read_bytes())
        (self.root / "candidate").mkdir()

    def write(self, name, content: bytes):
        (self.root / "candidate" / name).write_bytes(content)

    def pointer_bytes(self, name, data, **overrides):
        return large_files.canonical({"bytes": len(data), "path": f"candidate/{name}",
                                      "sha256": hashlib.sha256(data).hexdigest(), "slot": "certificate",
                                      **overrides})

    def test_pointer_needs_its_matching_file(self):
        self.write("certificate.art.zip.yukon-ref.json", self.pointer_bytes("certificate.art.zip", DATA))
        with self.assertRaises(large_files.LargeFileError) as raised:
            large_files.verify(self.root)
        self.assertIn("yukon setup --track hol", str(raised.exception))
        self.write("certificate.art.zip", DATA + b"x")
        with self.assertRaisesRegex(large_files.LargeFileError, "does not match"):
            large_files.verify(self.root)
        self.write("certificate.art.zip", DATA)
        large_files.verify(self.root)

    def test_symlinked_file_does_not_satisfy_a_pointer(self):
        outside = self.root / "outside"
        outside.write_bytes(DATA)
        self.write("certificate.art.zip.yukon-ref.json", self.pointer_bytes("certificate.art.zip", DATA))
        (self.root / "candidate" / "certificate.art.zip").symlink_to(outside)
        with self.assertRaises(large_files.LargeFileError):
            large_files.verify(self.root)

    def test_tampered_pointers_are_rejected(self):
        good = self.pointer_bytes("certificate.art.zip", DATA)
        value = json.loads(good)
        for content in (good.replace(b",", b", "), json.dumps({**value, "extra": 1}).encode(),
                        self.pointer_bytes("certificate.art.zip", DATA, path="candidate/certificate.art"),
                        self.pointer_bytes("certificate.art.zip", DATA, slot="other"),
                        self.pointer_bytes("certificate.art.zip", b"x" * 10, bytes=314572801),
                        b"{" + b" " * 1100 + b"}", b"not json"):
            self.write("certificate.art.zip.yukon-ref.json", content)
            with self.assertRaises(large_files.LargeFileError):
                large_files.verify(self.root)

    def test_one_pointer_per_slot(self):
        self.write("certificate.art.zip.yukon-ref.json", self.pointer_bytes("certificate.art.zip", DATA))
        self.write("certificate.art.xz.yukon-ref.json", self.pointer_bytes("certificate.art.xz", DATA))
        with self.assertRaisesRegex(large_files.LargeFileError, "more than one pointer"):
            large_files.verify(self.root)

    def test_python_and_yukon_agree_on_the_canonical_form(self):
        committed = REPO / "candidate" / "certificate.art.zip.yukon-ref.json"
        [pointer] = large_files.pointers(REPO)
        self.assertEqual(large_files.canonical(pointer), committed.read_bytes())


if __name__ == "__main__":
    unittest.main()
