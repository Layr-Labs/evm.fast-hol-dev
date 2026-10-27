"""Score a Yukon submission with the pinned hol-init-e verifier, which runs unchanged.

candidate/ is upstream's source envelope (submission/README.md): rom.bin, claim.json and a flat
experiments/ directory of proof sources plus original-allocation.term. `verifier/verify.py` checks
and freezes it, builds and exports the proof in a Bubblewrap sandbox with the tracing HOL, then
strictly replays the generated article with the standard HOL. Only that replay accepts.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import time_score  # noqa: E402

CANDIDATE = ROOT / "candidate"
TOOLS = ROOT / "work"
CPUINFO = Path("/proc/cpuinfo")
STAGES = ("build", "export", "bind", "package")
LOG_TAIL_LINES = 40
# Upstream's accepted run took 39,177 s end to end with --source-timeout 28800 --source-memory-gib 64
# --timeout 21600 --memory-gib 112: strict replay took 13,128 s and peaked at 90.25 GiB RSS (84 GiB
# Poly/ML heap). Each limit applies to CPU and wall time per stage; the author stages get extra room
# for a slower runner CPU. TOTAL_SECONDS keeps the whole verifier inside the 1,380-minute job.
SOURCE_TIMEOUT_SECONDS = 36_000
SOURCE_MEMORY_GIB = 64
TIMEOUT_SECONDS = 21_600
MEMORY_GIB = 112
TOTAL_SECONDS = 75_600


def runner() -> dict:
    """Non-secret details of the machine that ran the verifier, for comparing verifySeconds."""
    info = {}
    if os.environ.get("RUNNER_NAME"):
        info["name"] = os.environ["RUNNER_NAME"]
    try:
        with CPUINFO.open() as cpuinfo:
            model = next((line.split(":", 1)[1].strip() for line in cpuinfo if line.startswith("model name")), "")
    except OSError:
        model = ""
    if model:
        info["cpuModel"] = model
    info["cpuCount"] = os.cpu_count()
    return info


def children_cpu_seconds() -> float:
    # Counts only waited-for descendants, so it undercounts the author stages inside Bubblewrap
    # (upstream's /usr/bin/time recorded 11,432 s of user time for a 39,177 s run).
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    return usage.ru_utime + usage.ru_stime


def reports(stdout: str) -> list[dict]:
    """The JSON objects the verifier printed: strict replay's report, then the pipeline's."""
    found = []
    for line in stdout.splitlines():
        try:
            value = json.loads(line)
        except ValueError:
            continue
        if isinstance(value, dict):
            found.append(value)
    return found


def log_tail(work: Path, stage: object) -> None:
    if stage not in STAGES:
        return
    try:
        lines = (work / f"{stage}.log").read_text(errors="replace").splitlines()
    except OSError:
        return
    print(f"Last lines of the {stage} stage log:", *lines[-LOG_TAIL_LINES:], sep="\n", file=sys.stderr)


def run_verifier(work: Path) -> tuple[dict, dict]:
    polyml = TOOLS / "polyml"
    env = dict(os.environ, PATH=f"{polyml / 'bin'}{os.pathsep}{os.environ.get('PATH', '')}",
               LD_LIBRARY_PATH=os.pathsep.join(filter(None, [str(polyml / "lib"), os.environ.get("LD_LIBRARY_PATH")])))
    # Strict replay's --progress lines go to stderr; both JSON reports go to stdout.
    command = [sys.executable, str(ROOT / "verifier" / "verify.py"), str(CANDIDATE),
               "--hol", str(TOOLS / "HOL"), "--author-hol", str(TOOLS / "HOL-export"), "--work", str(work),
               "--source-timeout", str(SOURCE_TIMEOUT_SECONDS), "--source-memory-gib", str(SOURCE_MEMORY_GIB),
               "--timeout", str(TIMEOUT_SECONDS), "--memory-gib", str(MEMORY_GIB)]
    cpu = children_cpu_seconds()
    started = time.monotonic()
    # Its own session, so a timeout also stops the HOL processes it started.
    process = subprocess.Popen(command, stdout=subprocess.PIPE, text=True, cwd=ROOT, env=env, start_new_session=True)
    try:
        stdout, _ = process.communicate(timeout=TOTAL_SECONDS)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        stdout, _ = process.communicate()
        stdout += "\n" + json.dumps({"status": "failed", "reason": f"verifier exceeded {TOTAL_SECONDS} s"})
    # The score carries these minutes; official runs then apply the record rule (scripts/time_score.py).
    timing = {"verifySeconds": round(time.monotonic() - started, 1),
              "verifyCpuSeconds": round(children_cpu_seconds() - cpu, 1), "verifyRunner": runner()}
    found = reports(stdout)
    if not found:
        return {"status": "failed", "reason": "verifier printed no JSON report", "returncode": process.returncode}, timing
    report = found[-1]
    if report.get("status") != "verified":
        return report, timing
    replay = found[-2] if len(found) >= 2 else {}
    if process.returncode != 0:
        return dict(report, status="failed", reason=f"verifier exited {process.returncode}"), timing
    if replay.get("status") != "verified" or replay.get("K") != report.get("score"):
        return dict(report, status="failed", reason="no strict replay report for the verified claim"), timing
    return dict(report, K=replay["K"], rom_sha256=replay.get("rom_sha256"), proof_sha256=replay.get("proof_sha256")), timing


def main() -> None:
    score_path = ROOT / "scripts" / "score.json"
    score_path.unlink(missing_ok=True)
    work = TOOLS / "yukon" / uuid.uuid4().hex
    work.parent.mkdir(parents=True, exist_ok=True)
    report, timing = run_verifier(work)
    print(json.dumps(report, sort_keys=True))
    print(f"Verifier timing: {json.dumps(timing)}", file=sys.stderr)
    if report.get("status") != "verified":
        log_tail(work, report.get("stage"))
        raise SystemExit(f"Verifier did not accept the submission: {report.get('status')}")
    claim = report.get("K")
    if claim == "infinity":
        scored = time_score.INFINITY
    elif type(claim) is int and 0 <= claim <= time_score.LARGEST_K:
        scored = time_score.exact_score(time_score.encode(claim, time_score.minutes(timing["verifySeconds"])))
    else:
        raise SystemExit("K must be below 10^295: a Yukon exact score holds at most 299 integer digits, "
                         "four of them verification minutes")
    contract = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True, cwd=ROOT).strip()
    metrics = {"claim": claim, "finite": claim != "infinity", "prover": "hol", "verification": "source",
               "romSha256": report["rom_sha256"], "proofSha256": report["proof_sha256"],
               "contractCommit": contract, **timing}
    temporary = score_path.with_suffix(".tmp")
    temporary.write_text(json.dumps({**scored, "metrics": metrics}) + "\n")
    temporary.replace(score_path)


if __name__ == "__main__":
    main()
