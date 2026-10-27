# hol-init-e

## Verified software guest

The software-precompile guest shared by pinned init-e and Rocq passed the full
public source-only verifier on **2026-10-26**, with score Infinity. Its only
external calls are `halt` and `trap`; EVM precompiles execute in guest software.
The fresh HOL compiler output and full ROM match both pinned references byte
for byte: 979,140 native bytes, 4,603 bitmap words, and a 1,028,080-byte ROM,
SHA256 `44b6a6b828293a54cf2e8698a6a0af6a0d08b4ea825f6504547996c31969d04b`.
See [the accepted verification record](artifacts/software-guest/verification.json)
and [current artifacts](artifacts/software-guest/README.md).

The participant envelope contains 145 files totaling 3,045,749 bytes, or
693,478 bytes as a level-9 DEFLATE ZIP. The operator generates the 4,446,682,307-byte
OpenTheory article locally. A fresh uninterrupted public CLI run built,
exported, bound, and independently replayed it. Strict replay returned 0 without
a signal or timeout and wrote the exact `VERIFIED\n` completion marker. The
whole-ROM CV translation is retained; the generated-article limit is 8 GiB.
Tag `r20261026-verifier-passed` identifies the verified release commit.

The fixed memory and host semantics follow init-e `184e96cdc`: a 1 GiB input
arena, 4 KiB output window, software guest scratch placement, and host mapping
limited to the framed input. Rocq `92a7233` has the same guest and ROM literals
but retains older host/layout constants; the differences and exact pins are
recorded in [the reference comparison](source/software-update-reference.json).
Formal correspondence with the reduced Lean decoder and step remains open.

## Historical verified source-only submission

The source bundle's generated Certificate passed fresh independent kernel
replay on 2026-10-25 (Europe/Berlin), with the same original 950,344-byte ROM
and Infinity score. The participant bundle is 2,832,136 bytes across 146 files,
or 655,407 bytes when zipped with DEFLATE level 9. The 2.80 GB OpenTheory
article is generated locally by the operator.
See the [source verification record](artifacts/baseline/source-submission-verification.json)
for exact input hashes, limits, and staged build/export continuations. This
experiment resumed the export and replay stages; it was not an uninterrupted
public CLI run. Formal reduced Lean decoder/step agreement remains outstanding.

## Historical verified original ROM match

The HOL baseline ROM now matches original init-e `b3831bc` and Rocq byte for
byte: 950,344 bytes, SHA256
`22a1dd0963f12a3492e647b2626101fad2312dfcff813978b8ff1aca9897d7cc`.
The 904,196-byte native image and all 4,614 bitmap words also match the pinned
original. HOL uses native entry `0x80001190`, end `0x800ddd94`, and a 620-byte
code buffer. The fresh full independent verifier passed on 2026-10-13.
Tag `r20261012v` describes the prior, different ROM and remains historical.
Formal agreement with the reduced Lean decoder and step remains outstanding.
See [accepted verifier evidence](artifacts/baseline/verification.json) and
[byte comparison](artifacts/baseline/original-byte-comparison.json).

## Historical verified guest input-bound update

The guest guard from init-e PR #25 (commit `afa0071e8`) is imported.
Native code has been rebuilt (904,196 bytes, 4,614 bitmap words); HOL boundary
regressions pass. The full HOL Certificate passed independent article replay on 2026-10-13. Tag
`r20261009-v` preserves the previous different bytecode and layout as historical
evidence.
The new compilation requires the two bitmap-end startup header words to advance
from `0xa0029040` to `0xa0029048`; this layout adjustment is recorded in
`provenance.json`. The Certificate has no added input-length premise.


An experimental port of the [init-e challenge](https://github.com/flamingoponderado/init-e).
Participants submit arbitrary RISC-V bytes; the fixed guest, supported target
instructions, observations, and execution budget define the challenge.
CakeML's Pancake compiler supplies one route to a baseline submission.

The experiment replaces generated Lean computation certificates with HOL4
`cv_compute` evaluations. The generated Lean proof tree is not imported.
For the previous guest, HOL proved that the full top-level Pancake compilation
returns the 904,196-byte native RISC-V artifact. The fixed challenge evaluator also has a
checked finite bootstrap execution to native entry, and the resulting ordinary
memory agrees with the fixed source state.
That revision proved the full fixed challenge Certificate for the 950,344-byte
bootstrapped baseline ROM with score Infinity. The legacy complete article
package was **accepted by the full Python verifier**, binding the proof to the
frozen ROM and Infinity score. This is historical evidence, not a second
submission route. The [verification record](artifacts/baseline/verification.json)
contains the result and artifact hashes. Agreement with the pinned reduced Lean
decoder and machine step remains unproved.

## Fixed challenge and untrusted submissions

`challenge/`, `source/`, dependency pins, and `verifier/` belong to the challenge
operator. Participants supply a separate source-submission directory; they
cannot replace the challenge or certificate proposition. Its proof scripts
run only in a sandboxed author environment and acceptance still requires strict
kernel replay. The repository's `experiments/` directory is operator
development material; participants provide their own `experiments/` directory
in the source envelope.

```sh
python3 verifier/verify.py /path/to/source-submission \
  --hol /path/to/HOL --author-hol /path/to/tracing-HOL \
  --source-timeout 28800 --source-memory-gib 64 \
  --timeout 21600 --memory-gib 112
python3 verifier/test_verify.py
```

The participant-facing verifier checks trusted-file hashes and the CakeML pin,
freezes source inputs, runs source only in a sandboxed author HOL, and requires
fresh strict kernel replay of the exact fixed
`initChallenge.Certificate submittedBytes submittedScore`. There is one
participant submission format: the source envelope described in
[submission/README.md](submission/README.md). See
[the verifier boundary](verifier/README.md).

The OpenTheory article is an internal generated artifact and is not accepted as
a participant submission. The legacy article package's successful replay is
historical evidence for the same ROM and claim, not a second submission path.

## Included

- CakeML as a pinned `cakeml/` submodule. The separate sibling checkout is
  independent and is not a build dependency.
- The complete literal guest AST, translated to `64 panLang$decl list` from
  init-e's authoritative `Guest/SoftwareAst.lean`, plus the readable preprocessed source.
- The finite/infinite score model and memory-layout constants and proofs.
  Infinity still requires a finite terminating execution for every covered input.
- A restricted instruction decoder and machine step. Unsupported fetched
  encodings become `UnknownInstruction`; compressed decoding always does so.
  There is no blanket requirement that every byte in a submitted ROM be code.
- The declared gas-limit reader and covered-outcome/output comparison rules.
- Fixed source state, machine startup, framing, shared memory, terminal external-call
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

The public source exporter defaults to a 48 GiB per-process address-space limit;
the accepted software-guest run used an explicit 64 GiB limit. It uses a
40 GiB Poly/ML heap for its sequential article export. Build and binding
workers retain 24 GiB heaps. The smaller export heap exhausted its store while
recording `initBootstrapChallengeSuffixSteps`; the raised bound accommodates
that fixed proof under the public CLI.

The separate `HOL` field in `provenance.json` records the imported source's
upstream provenance, not the HOL checkout used for verification. Earlier native
artifact manifests retain their original build revisions. The full verification
record is [artifacts/software-guest/verification.json](artifacts/software-guest/verification.json).


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
python3 tools/import_ast.py /path/to/init-e/Guest/SoftwareAst.lean --check
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
python3 verifier/verify.py /path/to/source-submission --hol /path/to/HOL \
  --author-hol /path/to/tracing-HOL \
  --source-timeout 28800 --source-memory-gib 64 \
  --timeout 21600 --memory-gib 112
```

The successful original-ROM-match verification used a 21,600-second timeout,
112 GiB address-space limit, and 84 GiB Poly/ML heap. It took 8,973 seconds
(about 2 hours 30 minutes) and peaked at about 90.4 GiB child RSS. The current
8 GiB article cap accommodates the source-only software guest certificate,
including its checked whole-ROM CV translation. The 600-second/32 GiB defaults are below
the measured requirements of this baseline proof.

[Checked native artifacts](artifacts/README.md) are included in `artifacts/`.
The compiler target writes `compiled.bin`, `bitmaps.txt`, and `backend.conf`
under ignored `.build/`. These are native compiler artifacts, not an admitted
challenge ROM. Large evaluated theories require substantial memory and time
to export. Use the tested HOL pin in `provenance.json` for verifier preparation.

For the historical accepted revision, the fixed challenge and regression theories
built successfully. Its six AST importer tests and thirty-one verifier boundary tests passed. Strict replay component
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
