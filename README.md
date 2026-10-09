# hol-init-e

## Verified guest input-bound update

The guest guard from init-e PR #25 (commit `afa0071e8`) is imported.
Native code has been rebuilt (904,616 bytes, 4,614 bitmap words); HOL boundary
regressions pass. The full HOL Certificate and fresh submission passed independent
article replay on 2026-10-09. The verification record below describes this guest;
tag `r20261008-v` retains the prior guest and its historical evidence.
The new compilation requires the two bitmap-end startup header words to advance
from `0xa0029040` to `0xa0029048`; this layout adjustment is recorded in
`provenance.json`. The Certificate has no added input-length premise.


An experimental port of the [init-e challenge](https://github.com/flamingoponderado/init-e).
Participants submit arbitrary RISC-V bytes; the fixed guest, supported target
instructions, observations, and execution budget define the challenge.
CakeML's Pancake compiler supplies one route to a baseline submission.

The experiment replaces generated Lean computation certificates with HOL4
`cv_compute` evaluations. The generated Lean proof tree is not imported.
HOL has proved that the full top-level Pancake compilation returns the
904,616-byte native RISC-V artifact. The fixed challenge evaluator also has a
checked finite bootstrap execution to native entry, and the resulting ordinary
memory agrees with the fixed source state.
HOL now proves the full fixed challenge Certificate for the 950,344-byte
bootstrapped baseline ROM with score Infinity. The complete article package is
assembled and **accepted by the full Python verifier**, binding the proof to
the frozen ROM and Infinity score. The [verification record](artifacts/baseline/verification.json)
contains the result and artifact hashes. Agreement with the pinned reduced Lean
decoder and machine step remains unproved.

## Fixed challenge and untrusted submissions

`challenge/`, `source/`, dependency pins, and `verifier/` belong to the challenge
operator. Participants supply a separate submission directory; they cannot
replace the challenge or certificate proposition. `experiments/` is baseline
compiler development and grants no additional participant authority.

```sh
python3 verifier/verify.py --local /path/to/submission --hol /path/to/HOL --progress
python3 verifier/test_verify.py
```

The verifier checks trusted-file hashes and the CakeML pin before inspecting
candidate files. It never executes candidate ML. `--local` runs full verification,
preparing a missing or stale operator heap as needed. Acceptance requires a
closed proof of the exact fixed
`initChallenge.Certificate submittedBytes submittedScore`. The legacy positional
interface performs preflight only (exit 2) unless `--replay` is supplied. See
[the verifier boundary](verifier/README.md) and [submission format](submission/README.md).

## Included

- CakeML as a pinned `cakeml/` submodule. The separate sibling checkout is
  independent and is not a build dependency.
- The complete literal guest AST, translated to `64 panLang$decl list` from
  init-e's authoritative `Guest/Ast.lean`, plus the readable preprocessed source.
- The finite/infinite score model and memory-layout constants and proofs.
  Infinity still requires a finite terminating execution for every covered input.
- A restricted instruction decoder and machine step. Unsupported fetched
  encodings become `UnknownInstruction`; compressed decoding always does so.
  There is no blanket requirement that every byte in a submitted ROM be code.
- The declared gas-limit reader and covered-outcome/output comparison rules.
- Fixed source state, machine startup, framing, shared memory, accelerator
  oracle, submission admission, and challenge certificate definitions.
- Frozen submission snapshots, regenerated ROM/score literals, and a strict
  proof-replay component with tampering tests.
- All Pancake frontend passes and the RISC-V backend translated to cv equations.
  Native register allocation supplies an untrusted hint checked by HOL.
- Resource-limited certificate replay from frozen bytes and sanitized score
  literals, with exact conclusion, assumption, and theorem-tag checks.

## Build

Use Poly/ML and a built HOL4 checkout with `cv_transLib`. Revisions and source
hashes are in `provenance.json`. No Lean installation is needed for the build.

The successful full verification used:

- **HOL4:** `7f769972f0acf26df39facd83339c05a66d9ff26`, standard kernel
  (`Trindemossen 2`); this is `tested_hol` in `provenance.json`.
- **Poly/ML:** `5.9.2 Release`, configured executable `/usr/bin/poly`, reporting
  Git version `v5.9.2-311-gd615dad7`.

The separate `HOL` field in `provenance.json` records the imported source's
upstream provenance, not the HOL checkout used for verification. Earlier native
artifact manifests retain their original build revisions. The full verification
record is [artifacts/baseline/verification.json](artifacts/baseline/verification.json).


```sh
git submodule update --init
python3 tools/build.py --hol /path/to/HOL
python3 tools/test_import_ast.py
```

With HOL at `../HOL`, the `--hol` argument may be omitted. `HOLDIR` also works.
The build driver creates an ignored `.build/` source view linking the needed
CakeML and project files. This avoids unrelated upstream heap/bootstrap targets
and gives dependency discovery a common search path. It does not edit CakeML.
Use the same HOL checkout for successive builds of that directory.

To reproduce the AST from the pinned init-e checkout:

```sh
python3 tools/import_ast.py /path/to/init-e/Guest/Ast.lean --check
```

The importer checks the entire input hash and rejects unknown syntax and
constructors. Its output is checked as HOL definitions, but the importer is
**not a proof of agreement between Lean and HOL**. Review the constructor
mapping and pin when changing the guest. The Pancake parser is not used to
redefine the challenge's authoritative input.

## Target restriction

`source/instruction-subset.json` records the pinned Flapjack L3 instruction
carrier. This subset is narrower than ordinary RV64IM: for example, it includes
`ADDIW` but excludes `ADDW`, `MULW`, and word shifts. FP, atomics, privileged
operations other than the retained system calls, and compressed instructions
are excluded. `challenge/initTargetScript.sml` applies the whitelist to the
upstream decoder and derives a new `Next` body using the restricted decoders.

The target restriction applies to every participant, regardless of compiler.
An instruction check on baseline compiler output is not a replacement for it.
The current restricted step reuses upstream L3 semantics. Agreement with the
pinned reduced Lean decoder and step remains to be proved; the challenge's
initial state and oracle hooks are fixed in `initMachine` and `initSubmission`.
The remaining bridge must cover physical-address translation and failed steps
as well as decoding, including arbitrary invalid participant bytecode. See
[the semantic agreement investigation](experiments/RESULTS.md#semantic-agreement-investigation)
for the existing state invariant and unresolved obligations.
The compiler correctness theorem is connected to this fixed evaluator.

## Reproduce the compiler and verifier

```sh
python3 tools/build.py --hol /path/to/HOL initBaselineCertificateTheory
python3 tools/prepare_verifier.py --hol /path/to/HOL
python3 verifier/verify.py --local /path/to/submission --hol /path/to/HOL \
  --timeout 10800 --memory-gib 112 --progress
```

The successful full-baseline verification run (PR25 v4) used the 10,800-second
and 112 GiB limits above. It took 8,727 seconds (about 2 hours 25 minutes)
and peaked at 90.54 GiB child RSS. The 600-second/32 GiB defaults are below
the measured requirements of this baseline proof.

[Checked native artifacts](artifacts/README.md) are included in `artifacts/`.
The compiler target writes `compiled.bin`, `bitmaps.txt`, and `backend.conf`
under ignored `.build/`. These are native compiler artifacts, not an admitted
challenge ROM. Large evaluated theories require substantial memory and time
to export. Use the tested HOL pin in `provenance.json` for verifier preparation.

The fixed challenge and accelerator regression theories build successfully.
Six AST importer tests and thirty-one verifier boundary tests pass. Strict replay component
tests cover valid proofs and forged axioms; the real verifier rejects a valid
article whose conclusion is merely `T`. The full baseline package also passes
the production Python verifier.

See [experiment results](experiments/RESULTS.md) for the compiler results and
[the verifier boundary](verifier/README.md) for statement binding.

## Remaining semantic agreement obligation

Prove agreement with the pinned reduced Lean decoder and machine step.
The full baseline `Certificate` package has passed the Python verifier with
frozen bytecode and score literals; that proves the fixed HOL challenge
statement and does not establish cross-language semantic agreement.

The full compiler installation predicate (`pan_installed`) is proved for states
related to the checked bootstrap final state, including native bytes, bitmap
allocation, startup headers, and MMIO layout. The general Pancake compiler
refinement is also proved for the fixed challenge evaluator, retaining its
explicit installation, configuration, and resource premises. The exact full
compilation now also has a checked stack bound of 7,480 words (59,840 bytes),
using a compact ranking certificate checked by `cv_compute`.

`cv_compute` replaces concrete evaluation proofs; these semantic obligations
still require proofs. No admitted theorem fills the gaps. The 56,017-file Lean
submission proof tree is neither copied nor built.
