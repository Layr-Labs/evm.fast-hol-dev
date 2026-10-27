"""Score mapping and fail-closed checks for scripts/run.py, with the verifier mocked."""
from __future__ import annotations

import contextlib
import hashlib
import io
import itertools
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run  # noqa: E402

REPO = Path(__file__).resolve().parent.parent

RUNNER = {"name": "blacksmith-1", "cpuModel": "AMD EPYC 9454P 48-Core Processor", "cpuCount": 32}
# The fake clock and rusage advance by 3600.27 s wall and 5388.04 s CPU per verifier run.
TIMING = {"verifySeconds": 3600.3, "verifyCpuSeconds": 5388.0, "verifyRunner": RUNNER}


class FakeProcess:
    def __init__(self, stdout, returncode, timeout=False):
        self.stdout, self.returncode, self.timeout, self.pid = stdout, returncode, timeout, 4242

    def communicate(self, timeout=None):
        if self.timeout and timeout is not None:
            raise subprocess.TimeoutExpired("verify.py", timeout)
        return self.stdout, None


class Harness(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "scripts").mkdir()
        self.candidate = self.root / "candidate"
        cpuinfo = self.root / "cpuinfo"
        cpuinfo.write_text(f"processor\t: 0\nmodel name\t: {RUNNER['cpuModel']}\n\nprocessor\t: 1\nmodel name\t: x\n")
        usage = itertools.cycle([SimpleNamespace(ru_utime=10.0, ru_stime=2.0),
                                 SimpleNamespace(ru_utime=5000.0, ru_stime=400.04)])
        self.clock = patch.object(run.time, "monotonic", side_effect=itertools.cycle([100.0, 3700.27]))
        self.patches = [patch.object(run, "ROOT", self.root), patch.object(run, "CANDIDATE", self.candidate),
                        patch.object(run, "TOOLS", self.root / "work"),
                        patch.object(run, "CPUINFO", cpuinfo), patch.object(run.os, "cpu_count", return_value=32),
                        patch.dict(run.os.environ, {"RUNNER_NAME": "blacksmith-1"}),
                        patch.object(run.resource, "getrusage", side_effect=lambda who: next(usage)), self.clock]
        for p in self.patches:
            p.start()
            self.addCleanup(p.stop)
        self.score = self.root / "scripts" / "score.json"
        self.stderr = io.StringIO()
        redirect = contextlib.redirect_stderr(self.stderr)
        redirect.__enter__()
        self.addCleanup(redirect.__exit__, None, None, None)

    def timing_logged(self):
        lines = [line for line in self.stderr.getvalue().splitlines() if line.startswith("Verifier timing: ")]
        return [json.loads(line.removeprefix("Verifier timing: ")) for line in lines]

    def verifier(self, *lines, returncode=0, stdout=None, timeout=False):
        text = stdout if stdout is not None else "".join(json.dumps(line) + "\n" for line in lines)

        def fake(command, **kwargs):
            self.command = command
            self.assertTrue(command[1].endswith("verifier/verify.py"))
            self.assertTrue(kwargs["start_new_session"])
            return FakeProcess(text, returncode, timeout)
        return patch.object(run.subprocess, "Popen", fake)

    def run_main(self, *lines, **kwargs):
        with self.verifier(*lines, **kwargs), patch.object(run.subprocess, "check_output", return_value="abc123\n"):
            run.main()
        return json.loads(self.score.read_text())

    def fails(self, *lines, **kwargs):
        self.score.write_text("stale")
        with self.assertRaises(SystemExit) as raised:
            self.run_main(*lines, **kwargs)
        self.assertFalse(self.score.exists())
        return str(raised.exception.code)

    @staticmethod
    def replay(K):
        return {"status": "verified", "K": K, "rom_bytes": 4, "rom_sha256": "r" * 64, "proof_sha256": "p" * 64}

    @staticmethod
    def pipeline(K, status="verified"):
        return {"status": status, "verifier_exit": 0 if status == "verified" else 1, "rom_bytes": 4,
                "certificate_bytes": 1000, "source_bytes": 10, "score": K, "work": "/w"}

    def verified(self, K):
        return self.run_main(self.replay(K), self.pipeline(K))

    def test_verifier_command_and_limits(self):
        self.verified("infinity")
        option = {name: self.command[self.command.index(name) + 1] for name in
                  ("--hol", "--author-hol", "--work", "--source-timeout", "--source-memory-gib", "--timeout",
                   "--memory-gib")}
        self.assertEqual(self.command[2], str(self.candidate))
        self.assertEqual(option, {"--hol": str(self.root / "work" / "HOL"),
                                  "--author-hol": str(self.root / "work" / "HOL-export"),
                                  "--work": option["--work"], "--source-timeout": "36000",
                                  "--source-memory-gib": "64", "--timeout": "21600", "--memory-gib": "112"})
        work = Path(option["--work"])
        self.assertEqual(work.parent, self.root / "work" / "yukon")
        self.assertTrue(work.parent.is_dir())
        self.assertFalse(work.exists())  # verify.py requires a new directory

    def test_limits_fit_upstream_run_and_job(self):
        self.assertGreaterEqual(run.SOURCE_TIMEOUT_SECONDS, 28_800)
        self.assertGreaterEqual(run.TIMEOUT_SECONDS, 21_600)
        self.assertLess(39_177, run.TOTAL_SECONDS)
        workflow = (REPO / ".github" / "workflows" / "benchmark.yml").read_text()
        job_minutes = int(re.search(r"timeout-minutes: (\d+)", workflow)[1])
        self.assertLess(job_minutes, 24 * 60)
        self.assertLessEqual(run.TOTAL_SECONDS + 3600, job_minutes * 60)
        self.assertLessEqual(run.MEMORY_GIB, 120)  # 128 GB runner

    def test_infinity_scores_the_exact_infinity_pair(self):
        result = self.verified("infinity")
        self.assertEqual((result["score"], result["scoreExact"]), (1e300, "1" + "0" * 300))
        self.assertEqual(result["metrics"], {"claim": "infinity", "finite": False, "prover": "hol",
                                             "verification": "source", "romSha256": "r" * 64,
                                             "proofSha256": "p" * 64, "contractCommit": "abc123", **TIMING})

    def test_score_file_layout(self):
        self.verified(1234)
        self.assertEqual(self.score.read_text(), json.dumps({
            "score": 12_340_061, "scoreExact": "12340061",
            "metrics": {"claim": 1234, "finite": True, "prover": "hol", "verification": "source",
                        "romSha256": "r" * 64, "proofSha256": "p" * 64, "contractCommit": "abc123",
                        **TIMING}}) + "\n")

    def test_verify_seconds_is_positive_float(self):
        with patch.object(run.time, "monotonic", side_effect=[5.0, 5.26]):
            metrics = self.verified(7)["metrics"]
        self.assertIsInstance(metrics["verifySeconds"], float)
        self.assertEqual(metrics["verifySeconds"], 0.3)
        self.assertIsInstance(metrics["verifyCpuSeconds"], float)
        self.assertGreater(metrics["verifyCpuSeconds"], 0)

    def test_runner_info(self):
        self.assertEqual(run.runner(), RUNNER)
        with patch.object(run, "CPUINFO", self.root / "missing"), patch.dict(run.os.environ, {"RUNNER_NAME": ""}):
            self.assertEqual(run.runner(), {"cpuCount": 32})

    def test_finite_k_is_scored_with_its_minutes(self):
        largest = run.time_score.LARGEST_K
        for K in [0, 123, 2**53 - 1, 10**121, largest]:
            result = self.verified(K)
            self.assertEqual((result["scoreExact"], result["metrics"]["claim"], result["metrics"]["finite"]),
                             (str(K * 10_000 + 61), K, True))
            self.assertEqual(result["score"], float(result["scoreExact"]))
        self.assertEqual(self.verified(123)["score"], 1_230_061)
        self.assertEqual(self.verified(10**121)["score"], 1e125)

    def test_k_beyond_299_digits_fails_closed(self):
        for K in [run.time_score.LARGEST_K + 1, 10**300, -1, True, "7", 1.5]:
            self.fails(self.replay(K), self.pipeline(K))

    def test_rejection_deletes_stale_score(self):
        cases = [((self.replay("infinity"), self.pipeline("infinity", "rejected")), {"returncode": 1}),
                 (({"status": "rejected", "reason": "modified trusted file"},), {"returncode": 1}),
                 (({"status": "source_rejected", "stage": "export", "exit": 1, "work": "/w"},), {"returncode": 1}),
                 ((), {"stdout": "not json"}),
                 ((), {"stdout": "[]"}),
                 ((self.replay("infinity"), self.pipeline("infinity")), {"returncode": 1}),
                 ((self.pipeline("infinity"),), {}),
                 ((self.replay(5), self.pipeline(6)), {}),
                 (({"status": "rejected"}, self.pipeline(5)), {})]
        for lines, kwargs in cases:
            self.fails(*lines, **kwargs)
        self.assertEqual(self.timing_logged(), [TIMING] * len(cases))

    def test_failed_stage_log_tail_is_printed(self):
        def fake(command, **kwargs):
            work = Path(command[command.index("--work") + 1])
            work.mkdir()
            (work / "export.log").write_text("".join(f"line {n}\n" for n in range(100)) + "author stage exit=1\n")
            return FakeProcess(json.dumps({"status": "source_rejected", "stage": "export", "exit": 1}), 1)
        self.score.write_text("stale")
        with patch.object(run.subprocess, "Popen", fake), self.assertRaises(SystemExit) as raised:
            run.main()
        self.assertIn("source_rejected", str(raised.exception.code))
        logged = self.stderr.getvalue()
        self.assertIn("Last lines of the export stage log:", logged)
        self.assertIn("author stage exit=1", logged)
        self.assertNotIn("line 50\n", logged)
        self.assertFalse(self.score.exists())

    def test_timeout_stops_the_verifier_session(self):
        with patch.object(run.os, "killpg") as killpg:
            message = self.fails(self.replay(1), self.pipeline(1), timeout=True)
        killpg.assert_called_once_with(4242, run.signal.SIGKILL)
        self.assertIn("failed", message)


class Repository(unittest.TestCase):
    def test_baseline_candidate_is_upstream_accepted_envelope(self):
        manifest = json.loads((REPO / "artifacts" / "software-guest" / "source-submission-manifest.json").read_text())
        candidate = REPO / "candidate"
        files = {path.relative_to(candidate).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                 for path in candidate.rglob("*") if path.is_file()}
        self.assertEqual(files, manifest["file_sha256"])
        self.assertEqual(manifest["score"], "infinity")
        self.assertEqual((candidate / "rom.bin").read_bytes(),
                         (REPO / "artifacts" / "software-guest" / "rom.bin").read_bytes())
        self.assertEqual(json.loads((candidate / "claim.json").read_text()), {"K": "infinity"})

    def test_manifest_paths(self):
        track, = json.loads((REPO / "benchmark.json").read_text())["tracks"]
        self.assertNotIn("largeFiles", track)
        for path in track["editablePaths"]:
            self.assertTrue((REPO / path).exists(), path)
            self.assertFalse(Path(track["scorePath"]).is_relative_to(path))

    def test_warm_cache_key_matches_benchmark(self):
        workflows = REPO / ".github" / "workflows"
        keys = [re.findall(r"^ +key: (hol-verifier-.*)$", (workflows / name).read_text(), re.M)
                for name in ("benchmark.yml", "warm-cache.yml")]
        self.assertEqual(len(keys[0]), 1)
        self.assertEqual(keys[0], keys[1])


if __name__ == "__main__":
    unittest.main()
