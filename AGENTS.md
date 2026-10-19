# Agent instructions

- The challenge is described in [README.md](README.md), the verifier boundary in
  [verifier/README.md](verifier/README.md) and the submission format in
  [submission/README.md](submission/README.md). The fixed statement is
  `initChallenge.Certificate submittedBytes submittedScore` (`challenge/initChallengeScript.sml`).
  Those upstream documents are the authority for the challenge; this file covers the Yukon harness.
- `benchmark.json` is schema v2 with one track, `hol`. Pass `--track hol` to `yukon setup`,
  `yukon run` and `yukon submit`. `yukon switch` changes only Yukon's track selection; it keeps
  your Git branch, `HEAD`, index and worktree.
- Yukon submissions on the `hol` track replace only `candidate/`. It must contain exactly:
  - `rom.bin`: the submitted bytes, at most 128 MiB.
  - `claim.json`: exactly `{"K":123}` or `{"K":"infinity"}`.
  - One of `certificate.art` (an OpenTheory article), `certificate.art.xz` (the same article as
    one xz stream) or `certificate.art.zip` (a zip holding exactly one stored or deflated file
    named `certificate.art`, for example `zip -9 certificate.art.zip certificate.art`). The
    harness expands a compressed form, refusing more than 3 GiB, and passes a fresh `rom.bin`,
    `claim.json` and `certificate.art` to `verifier/verify.py`.
- The certificate is a large file: Git and the Yukon archive carry only a pointer,
  `candidate/<certificate file>.yukon-ref.json` (its size and SHA-256), and the file itself is
  stored by Yukon. Put the real file at its path; `yukon submit --track hol` uploads it (resuming
  an interrupted upload) and submits the pointer. A pointer you leave unchanged, such as the
  baseline's `candidate/certificate.art.zip.yukon-ref.json`, is submitted as-is. Keep exactly one
  of the three certificate files; delete a stale pointer if you switch formats.
- `yukon setup --track hol` downloads the file each pointer names, so `yukon run --track hol`
  works in a fresh clone. The official run fetches it the same way (`scripts/large_files.py`)
  and refuses a file whose size or SHA-256 differs from its pointer.
- Changes outside `candidate/` are dropped from Yukon submissions.

## Size limits

- The certificate file may be at most 300 MiB (314,572,800 bytes) as uploaded and 3 GiB
  (3,221,225,472 bytes) expanded. zstd is not accepted.
- The rest of `candidate/` goes in the Yukon archive: 25 MiB compressed, 512 MiB expanded and
  10,000 entries.
- The baseline article is 2,803,497,058 bytes; upstream's zip of it is 98,247,790 bytes, about
  29x (`artifacts/baseline/certificate-compression.json`). xz has not been measured.
- The article must be self-contained. Replay trusts only HOL's four foundational axioms, the
  literal definitions built from your `rom.bin` and `claim.json`, and the definitions and
  theorems of `initProofLibrary` and its ancestors. It cannot cite baseline theories such as
  `initBaselineCertificate` or `initArtifacts`, or facts from another submission.

## Score

- `scripts/run.py` scores the certified step bound `K` from `claim.json`; lower is better. Ties
  do not improve the incumbent.
- Official runs then add verification time (`scripts/time_score.py`, run by the workflow on the
  host): `score = K * 10^4 + verification minutes`, so a smaller `K` always wins and time only
  breaks ties at equal `K`. At equal `K` a submission must verify at least 5% faster than the
  `verifySeconds` of the record read when it finishes; otherwise it takes the record's score and
  ties. If the record cannot be read, the minutes are 9999 and the step logs a warning.
  `YUKON_API_URL` (repository variable, default `https://api.yukon.org`) names the API. Local
  runs score `K` alone.
- `{"K":"infinity"}` is scored as `9007199254740991` (2^53 − 1). The initial submission claims
  infinity, so any accepted finite `K` improves it.
- Yukon stores scores as doubles and returns them with 15 significant digits, so the infinity
  score reads back as `9007199254740990`, as does every value from `9007199254740985` up. A
  finite `K` of `9007199254740985` or more is rejected. A `K` of 10^11 or more carries no
  minutes, since they would round into `K`, so equal bounds that large stay tied; from about
  9 * 10^11 every timed score is capped at `9007199254740984`, still below infinity, and those
  bounds tie.
- A score is written only when the verifier reports `verified`; otherwise `scripts/run.py` exits
  nonzero and writes no score. `metrics` records the claim, the verifier's ROM and proof
  SHA-256 and the harness commit.
- `metrics.verifySeconds` and `metrics.verifyCpuSeconds` are the verifier's wall and CPU time,
  and `metrics.verifyRunner` describes the runner.

## Verification

`scripts/run.py` runs `verifier/verify.py --local` unchanged, with `--timeout 21600
--memory-gib 112`. The verifier checks the trusted file hashes and the CakeML pin, freezes the
submitted files, builds HOL literals from the ROM and claim, and replays the article in a fresh
HOL process with the operator-built heap. It never executes candidate ML. It accepts only a
closed proof of exactly the fixed Certificate. Upstream's baseline replay took 8,973 seconds and
peaked at 90.4 GiB RSS with an 84 GiB Poly/ML heap (`--memory-gib 112`).

Run `bash scripts/setup.sh`, then `python3 scripts/run.py` (what `yukon setup --track hol` and
`yukon run --track hol` do). Setup needs git, curl, a C/C++ toolchain, GMP and Python 3.11 or
newer. It builds the pinned Poly/ML and HOL4 under `work/`, checks out the pinned CakeML
submodule and builds the verifier heap; the cold build has not been timed. Replaying a
baseline-sized article needs about 91 GiB of RAM. Do not claim verification without a
successful run.

Producing an article uses upstream's author export pipeline
([verifier/README.md](verifier/README.md#author-proof-export)), which needs a separate
tracing-kernel HOL checkout.

## Notes

- Put reproducible context in the Yukon submission note. Remove secrets and private data first.
- Yukon handles submission pull requests and promotions; do not merge them by hand.
