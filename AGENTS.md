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
  - `certificate.art` (an OpenTheory article) or `certificate.art.xz` (the same article as one
    xz stream), not both. The harness expands the xz stream, refusing more than 3 GiB, and passes
    a fresh `rom.bin`, `claim.json` and `certificate.art` to `verifier/verify.py`.

  Only the unchanged baseline (`candidate/rom.bin` identical to `artifacts/baseline/rom.bin`,
  claiming infinity) may omit the certificate. It is then checked with the operator-published
  baseline article, whose hash is in `artifacts/baseline/verification.json` and whose size and
  hash are pinned in `scripts/baseline-article.json`.
- Changes outside `candidate/` are dropped from Yukon submissions.

## Size limits

- Yukon archives are limited to 25 MiB compressed, 512 MiB expanded and 10,000 entries. Yukon
  commits the submission to Git, and GitHub rejects files over 100 MB.
- The baseline article is 2,803,497,058 bytes. An article of that size fits only if it
  compresses below 25 MiB, a ratio above 106x. Upstream measured zstd at 97,104,273 bytes and
  zip at 98,247,790 bytes, about 29x (`artifacts/baseline/certificate-compression.json`); xz
  has not been measured.
- The article must be self-contained. Replay trusts only HOL's four foundational axioms, the
  literal definitions built from your `rom.bin` and `claim.json`, and the definitions and
  theorems of `initProofLibrary` and its ancestors. It cannot cite baseline theories such as
  `initBaselineCertificate` or `initArtifacts`, or facts from another submission.

## Score

- `score` in `scripts/score.json` is the certified step bound `K` from `claim.json`; lower is
  better. Ties do not improve the incumbent.
- `{"K":"infinity"}` is scored as `9007199254740991` (2^53 − 1). The initial submission claims
  infinity, so any accepted finite `K` improves it.
- Yukon stores scores as doubles and returns them with 15 significant digits, so the infinity
  score reads back as `9007199254740990`, as does every value from `9007199254740985` up. A
  finite `K` of `9007199254740985` or more is rejected, and a finite `K` of 10^15 or more may be
  shown and compared rounded to 15 significant digits.
- A score is written only when the verifier reports `verified`; otherwise `scripts/run.py` exits
  nonzero and writes no score. `metrics` records the claim, the verifier's ROM and proof
  SHA-256 and the harness commit.

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
