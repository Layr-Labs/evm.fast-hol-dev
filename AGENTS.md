# Agent instructions

- The challenge is described in [README.md](README.md), the verifier boundary in
  [verifier/README.md](verifier/README.md) and the submission format in
  [submission/README.md](submission/README.md). The fixed statement is
  `initChallenge.Certificate submittedBytes submittedScore` (`challenge/initChallengeScript.sml`).
  Those upstream documents are the authority for the challenge; this file covers the Yukon harness.
- `benchmark.json` is schema v2 with one track, `hol`. Pass `--track hol` to `yukon setup`,
  `yukon run` and `yukon submit`. `yukon switch` changes only Yukon's track selection; it keeps
  your Git branch, `HEAD`, index and worktree.
- Yukon submissions on the `hol` track replace only `candidate/`, upstream's source envelope. It
  must contain exactly:
  - `rom.bin`: the submitted bytes, at most 128 MiB.
  - `claim.json`: exactly `{"K":123}` or `{"K":"infinity"}`.
  - `experiments/`: flat regular files named `<Name>Script.sml`, `<Name>Lib.sml` or
    `<Name>Lib.sig`, plus the required `original-allocation.term` (an untrusted register-allocation
    hint that HOL checks). At most 256 files, 16 MiB each and 64 MiB in total. No subdirectories,
    symlinks or build outputs: build elsewhere (see Verification).
- There is no certificate file: the verifier generates the OpenTheory article from your sources.
  The baseline in `candidate/` is upstream's accepted envelope (145 files, 3,045,749 bytes,
  `artifacts/software-guest/source-submission-manifest.json`), and it targets the baseline
  `initBaselineCertificate` theory tree.
- Changes outside `candidate/` are dropped from Yukon submissions.

## Score

- `scripts/run.py` scores the certified step bound `K` from `claim.json` with its verification
  time: `scoreExact = K * 10^4 + verification minutes` (rounded up, at most 9999), so a smaller
  `K` always wins and time only breaks ties at equal `K`; lower is better. Ties do not improve
  the incumbent.
- The track opts in to Yukon's exact scores (`"exactScores": true` in `benchmark.json`).
  `score.json` carries `scoreExact`, a decimal string Yukon compares exactly, and `score`, the
  double nearest it (a plain integer up to 2^53). Minutes count at every size of `K`. `K` must be
  below 10^295, since an exact score holds at most 299 integer digits; larger claims are rejected.
- Official runs then apply the record rule (`scripts/time_score.py`, run by the workflow on the
  host): at equal `K`, read from the record's `currentBestScoreExact`, a submission must verify
  at least 5% faster than the `verifySeconds` of the record read when it finishes; otherwise it
  takes the record's exact score and ties. If the record cannot be read, the minutes are 9999
  and the step logs a warning. A record with no exact score (scored before the opt-in) is matched
  by its `metrics.claim`, and an equal `K` that is not 5% faster gets 9999 minutes.
  `YUKON_API_URL` (repository variable, default `https://api.yukon.org`) names the API. Local runs
  skip this step, so their minutes are only a rough indicator.
- `{"K":"infinity"}` is scored as `scoreExact` `1` followed by 300 zeros (10^300) with `score`
  `1e300`, above every finite score. The initial submission claims infinity, so any accepted
  finite `K` improves it.
- `K = floor(scoreExact / 10^4)`, with the verification minutes in the last four digits.
- A score is written only when the verifier reports `verified` after strict replay; otherwise
  `scripts/run.py` exits nonzero, prints the end of a failed author stage's log and writes no
  score. `metrics` records the claim, the ROM and generated-article SHA-256 and the harness commit.
- `metrics.verifySeconds` is the whole verifier's wall time (build, export, bind, package and
  strict replay), and the minutes come from it. `metrics.verifyCpuSeconds` undercounts work
  inside the author sandbox, and `metrics.verifyRunner` describes the runner.

## Verification

`scripts/run.py` runs `verifier/verify.py candidate --hol work/HOL --author-hol work/HOL-export`
unchanged, with `--source-timeout 36000 --source-memory-gib 64 --timeout 21600 --memory-gib 112`,
and stops it after 75,600 s. The verifier checks the trusted file hashes and the CakeML pin,
freezes the envelope, then runs four author stages (build, export, bind, package) in a Bubblewrap
sandbox: no network, read-only toolchain and repository, a cleared environment, and per-stage
CPU, wall and address-space limits. Your ML runs only there. The generated article (upstream's
baseline: 4,446,682,307 bytes, 8 GiB limit) is then replayed by the standard HOL with the
operator-built heap, which accepts only a closed proof of exactly the fixed Certificate.
Upstream's accepted baseline run took 39,177 s (10 h 53 min) end to end, 13,128 s of it strict
replay, and peaked at 90.25 GiB RSS with an 84 GiB Poly/ML heap.

Run `bash scripts/setup.sh`, then `python3 scripts/run.py` (what `yukon setup --track hol` and
`yukon run --track hol` do). Setup needs Linux, git, curl, a C/C++ toolchain, GMP, Bubblewrap with
unprivileged user namespaces, and Python 3.11 or newer. It builds the pinned Poly/ML, the standard
HOL4 tree and the tracing HOL4 tree (`tools/prepare_exporter.py`) under `work/`, checks out the
pinned CakeML submodule, builds the baseline theories in `.build/` and prepares the verifier heap.
A cold setup takes hours; official runs restore it from a cache that
`.github/workflows/warm-cache.yml` saves on `main`. A baseline-sized run needs about 91 GiB of
RAM. Do not claim verification without a successful run.

To iterate on proofs before a full run, use upstream's author tools
([verifier/README.md](verifier/README.md#author-proof-export)): `tools/build.py --build-dir
<dir> --experiments-dir candidate/experiments` builds your sources outside `candidate/`, and
`tools/export_baseline.py` exports them.

## Notes

- Put reproducible context in the Yukon submission note. Remove secrets and private data first.
- Yukon handles submission pull requests and promotions; do not merge them by hand.
