# Trusted verifier boundary

Run from an operator-controlled checkout of the fixed challenge:

```sh
python3 verifier/verify.py --local /path/to/untrusted-submission --hol /path/to/tested/HOL --progress
python3 verifier/test_verify.py
python3 verifier/test_replay.py
```

The operator pins this checkout and dependencies. Participants control only
`rom.bin`, `claim.json`, and `certificate.art` in a separate submission directory.
A trust manifest supplied by a participant would not establish trust.

`--local` uses the original init-e invocation style and verifies by default.
The same command prepares a missing or stale operator heap before replay,
using `--hol`, `HOLDIR`, or the existing build's HOL path. Submitted files are
frozen before preparation and are not read again afterward.

`--structural-only` explicitly returns `structural_pass` (exit 0) for a valid
envelope without claiming a Certificate proof. The legacy positional interface
still performs preflight unless `--replay` is specified. The original
`--trusted`, `--work`, and `--hide` options are described below.

## Frozen literals and the exact statement

The verifier checks trusted-file hashes and the CakeML pin, exact file names,
regular files without symlinks, bounded sizes (128 MiB ROM, 2 GiB article), and a literal finite/infinite
score. It reads each candidate file once into an immutable snapshot. Later
steps use those frozen bytes rather than reopening candidate paths.

`claim.json` is exactly `{"K":123}` or `{"K":"infinity"}`. The operator's fixed
checker constructs HOL word8 literals from the frozen ROM and a natural-number
or Infinity literal from the sanitized score. It requires exactly:

```text
|- initChallenge.Certificate submissionLiterals.submittedBytes
                             submissionLiterals.submittedScore
```

The certificate existentially quantifies admitted dispatch/layout metadata;
its code field must equal the submitted bytes. The source program, oracle,
restricted target, initial state, evaluator, and admission rules are fixed.
Infinity still requires finite termination for each covered source execution.

No candidate ML, build scripts, or load paths are executed. ROM data is allowed;
instruction restrictions apply when the machine fetches instructions.

## Independent replay

`strictReplayLib.sml` supplies OpenTheory reader callbacks. Axiom requests must
match checked library or previously replayed facts (including kernel-checked
specialization, generalization, and conjunction projection), or be independently
proved by logical simplification or computation. Article-defined CV functions
are evaluated from already proved executable equations using `cv_compute`.
Representation lemmas are not treated as executable equations. It never calls `axiom_in_db`, whose fallback
admits a theorem. Definitions may introduce only fresh constants/types in the
operator-created candidate theory. The expected theorem must have no hypotheses
or untrusted theorem tags and must have the exact fixed conclusion.

The replay process uses a private working directory, the hash-checked operator
heap, fixed checker code, time and memory limits, and a completion marker written
only after the exact theorem check. Defaults are 600 seconds and 32 GiB;
`--timeout` and `--memory-gib` configure these limits. The operator must use the
tested HOL revision in `provenance.json`.

Exit codes: **0** verified; **1** rejected; **2** incomplete/preflight only or
missing/stale prepared verifier. The positional interface without `--replay` never accepts a proof.
`--local` selects full replay automatically; explicit `--structural-only` is a
separate successful envelope check and never returns `verified`.

The complete baseline article package passes the production Python verifier
with the exact fixed Certificate conclusion and frozen ROM/score literals.
The [verification record](../artifacts/baseline/verification.json) records exit 0,
`status: verified`, the 950,344-byte ROM, Infinity score, and artifact hashes.
Tests include
strict-reader positive examples and a real-process negative test using a valid
article proving an unrelated statement, including a full 904,616-byte literal
ROM. `test_replay.py` checks that this reaches the exact-conclusion rejection
rather than failing during literal loading. An isolated author tracing build now
exports CV computation requests and their proved equations; the unmodified
standard verifier kernel recomputes those requests. For the prior guest, the exact first nine compiler articles selected for its package independently
replay 13,399 exported theorems in one fresh standard-kernel process, using only
the fixed library and preceding proof data. This includes full native bytecode
compilation. The measured run took 679.5 seconds and peaked at 52.7 GiB RSS,
so the baseline requires explicit limits above the defaults. The successful
full-package run (PR25 v4) took 8,727 seconds and peaked at 90.54 GiB child RSS,
using `--timeout 10800 --memory-gib 112`. Reduced Lean decoder/step agreement
remains an independent, unproved semantic obligation.

The fixed `initProofLibrary` supplies generic compiler, target, semantics, and
CV lemmas. Its local source dependencies are pinned in the trusted-file manifest.
It contains no baseline-specific compilation or Certificate theorem.

## Auditable literal preparation

```sh
python3 verifier/verify.py /path/to/candidate --prepare /path/to/new-directory
```

This creates a new mode-0700 directory containing frozen ROM and article bytes,
a regenerated claim, and an audit `submissionLiteralsScript.sml` with decimal
byte and score literals. No candidate text is interpolated into HOL syntax.
Preparation alone returns exit 2. Replay constructs the same literals with HOL
term constructors rather than executing the audit script.

`trusted-files.json` is updated only by challenge authors for a release. The
verifier never regenerates it for a participant. Re-run operator heap preparation
after changing fixed challenge or verifier files.

## Original command-line options

The original option names are supported: `--local`, `--trusted`, `--work`,
repeatable `--hide`, `--structural-only`, and `--progress`.

`--trusted` selects the operator-owned HOL port checkout whose manifest,
challenge, dependency pins, checker, and prepared heap are used. It is never
read from a submission. `--work` must name a new directory; it retains frozen
inputs, `replay.log`, and `replay-process.json` after success or rejection.
The process report records the HOL return code or signal, elapsed time, and
timeout status; it is diagnostic data, not an acceptance marker. Without `--work`,
replay uses a private temporary directory. Structural checks with `--work` retain the
sanitized inputs, but never claim a proof was verified.

`--hide` masks each named file or directory in the replay process using
Bubblewrap. The host filesystem is mounted read-only, the replay workspace is
writable, and the process has private network and PID namespaces. Hidden
directories are empty mounts; hidden file contents are inaccessible (the
replacement may read as empty or be denied by the host mount policy). Overlap with
required verifier, HOL, heap, or workspace paths is rejected. Missing isolation
support or failed sandbox execution rejects verification; masking is never
silently skipped. Structural-only mode executes no participant proof process.

Example:

```sh
python3 verifier/verify.py --local /path/to/submission \
  --trusted /path/to/hol-init-e --work /path/to/new-run \
  --hide /path/to/submission --hide /path/to/private-data --progress
```

The full baseline Certificate is proved in HOL, and its complete article package
has passed end-to-end Python verification. Use `--timeout 10800 --memory-gib 112`
for the resource limits of the successful baseline run.

## Author proof export

The author uses a separate tracing-kernel checkout at the tested HOL revision:

```sh
python3 tools/prepare_exporter.py --hol-source ../HOL-init-e
python3 tools/test_exporter.py --hol ../HOL-init-e --author-hol ../HOL-init-e-export
python3 tools/build.py --hol ../HOL-init-e initBaselineCertificateTheory initProofLibraryTheory
python3 tools/export_baseline.py --hol ../HOL-init-e --author-hol ../HOL-init-e-export --resume
python3 tools/bind_baseline.py --hol ../HOL-init-e --author-hol ../HOL-init-e-export
python3 tools/package_baseline.py --output /path/to/new-submission
```

`--only THEORY` exports one dependency; `--start-at THEORY` resumes a suffix of
the dependency order. `--stop-before THEORY` bounds a suffix for separate
export batches. Workers default to a 24 GiB Poly/ML heap limit and one GC thread;
`--maxheap-mib` and `--gc-threads` adjust these author resource settings.
The author patch records proofs, supports CV computation
requests, and emits dictionary cleanup. Exported baseline constants are renamed
into the fresh candidate namespace. Article compaction preserves inference
commands while releasing dictionary objects at their last use. Neither the
patch nor author caches are used to accept a submission. Large CV and byte-list
spines are serialized without ordering every suffix in the writer dictionary.
The exporter reuses the allocation hint from the prior build as data; its full
compiler evaluation still checks the hint before returning bytes. Large literal
conversions use independently recomputed evaluation requests. The suffix exporter
records shared helper proofs and solved instruction goals separately, then clears
its temporary dictionary before continuing the final conjunction proof.

The smoke regression independently replays fresh definitions, ordinary proof
commands, CV evaluation, and compacted articles. A literal-decoding request is
re-proved with kernel inference rules and matched against the verifier's own
sanitized byte constant. Fixed-vocabulary `EVAL` requests are also recomputed by
the standard kernel; this path rejects candidate-defined constants. Propositional
congruence requests are discharged with HOL’s tautology prover. The lookup set
includes exactly HOL’s four foundational axioms (`BOOL_CASES_AX`, `ETA_AX`,
`SELECT_AX`, `INFINITY_AX`) alongside the fixed library theorems. Regression
checks reject changed bytes, forged literal
definitions, false results, missing or forged equations, unrelated conclusions, and attempts
to replace fixed constants. The full baseline package has passed production
verification; its result, resource use, and hashes are recorded in
[verification.json](../artifacts/baseline/verification.json).


### Parallel article diagnostics

To locate replay gaps without repeatedly processing the full compiler prefix:

```sh
python3 tools/audit_articles.py --list
python3 tools/audit_articles.py --workers 3 --heap-gib 24 --resume \
  initBootstrapSuffixSteps initBootstrapChallengeSuffixSteps initBaselineCertificate
```

With no module names, the tool checks all modules in the export plan. Each worker
loads built predecessor theories, introduces the selected article's definitions
in a fresh candidate theory, and checks that article's commands. The runner
uses compiled theory parent metadata and records separate logs and results under
`.export-baseline-checkpoint/audit/`. Successful results are reused only when
the recorded input fingerprints match. Failures in one article do not stop
the other workers.

These are author diagnostics, **not submission verification**: predecessor
theorems are imported instead of reconstructed from the submitted article, and
the loaded datatype metadata can differ from a fresh full replay. The diagnostic
evaluation guard also excludes mapped predecessor constants, preserving the
production restriction on evaluating candidate definitions. Only the complete
`verifier/verify.py` run checks the package from the fixed trust root and binds
its conclusion to the frozen bytecode and score.
