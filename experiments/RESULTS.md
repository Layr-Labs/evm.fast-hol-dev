# cv_compute results, 2026-10-07

Dependency pins are in `../provenance.json`; builds use `tested_hol`.
The source submission has 56,017 Lean files. None of its generated proof tree
was copied or built. The pinned literal AST contains 928 declarations.

## Full compiler computation

The complete guest passed simplification, struct lowering, global lowering,
Crep, loop, word, register allocation checking, and RISC-V backend encoding.
The native allocator is an untrusted hint generator; the logical backend checks
the hint before returning bytes. All saved computation results are checked for
hypotheses and untrusted theorem tags.

Native output:

- Length: **904,476 bytes**.
- SHA-256: `4403ff7d9c7b663ba20a4e9c961547b2548530a56b15f238248886763009489e`.
- This is compiler code, **not a bootstrapped challenge ROM**.

`initCompilationInput.top_compile_to_backend` proves the composition from the
ordinary top-level Pancake compiler to its backend input. `initBytecode` evaluates
the backend, proves successful completion and the byte count, and exports the
byte array. `pancakeBackendBridge` proves correspondence between the cv backend
wrapper and the ordinary backend. `initCompileProof` composes these results;
`initArtifacts` exports 4,613 bitmap words and encoded configuration data.
It also proves the exact result triple using the proved configuration
encode/decode round trip. The checked
source-to-bytecode theorem is:

```text
|- ?bm c. pan_to_target$compile_prog riscv_config
            (set_oracle pancakeRiscvConfig allocation) guestAst =
          SOME (compiledBytes,bm,c)
```

`initBytecode` and `initCompileProof` passed in 182 s and 73 s of Holmake wall
time respectively on the final run, including ancestor loading.

```sh
python3 tools/build.py --hol /path/to/HOL initArtifactsTheory.uo
```

Generated files are `.build/compiled.bin`, `.build/bitmaps.txt` (decimal word64
values, one per line), and `.build/backend.conf` (CakeML's configuration encoding).
The kernel-checked byte result is separate from the file writer and external
SHA-256 reporting; no cryptographic digest equality is claimed as a HOL theorem.

### Translation details

All passes share CakeML's `backend_64_cv` codecs, including wordLang and mlstring.
Record literals are converted to constructors using proved reconstruction
identities and fully evaluated before deep embedding. Specializations of
higher-order helpers, mutual recursion, sorting, and finite-map representations
are proved from their original definitions.

The RISC-V specialization retains raw defining equivalences as well as evaluation
equations, allowing the evaluated wrapper result to be related to the original
backend. Native allocation is never accepted as a proof. No upstream CakeML
source was edited; derived translation/correspondence files carry its BSD notice.

Large literal theories disable HTML theorem pretty-printing: that optional
output grew to 24 GB for the bytecode result alone. Serialized HOL theory data
is far smaller. Compilation and loading still need substantial RAM.

Selected observed Holmake wall times (cached prerequisites; not benchmarks):

| Theory | Time |
| --- | ---: |
| initSimplify | 140 s |
| initGlobals | 84 s |
| initCrep | 95 s |
| initPrepared | 235 s |
| initLoops | 199 s |
| initWord | 154 s |
| initCompilationInput | 62 s |
| backendRiscvCv | 57 s |
| pancakeBackendBridge | 15 s |

The reproducible native artifacts are checked in under `artifacts/`.

## Fixed challenge and verifier

The challenge now fixes the source initial state, accelerator oracle, reduced
instruction decoder, machine initial state, dispatch hooks, cache-hook evaluator,
admission rules, observations, and certificate proposition. Metadata is an
admitted existential witness bound to the submitted code. The score is finite
or Infinity; both require termination on every covered source execution.

Keccak and SHA-256 known-answer checks pass, along with modular arithmetic,
curve/Fp2, malformed input, and accelerator rejection regressions. Initial PC,
zero registers/RAM, initial target validity, byte limits, cache return, and
infinite-score termination lemmas build successfully. These tests do not prove
Lean/HOL semantic agreement.

Six AST importer tests and sixteen Python verifier boundary tests pass. The
pinned AST reimports exactly. The strict OpenTheory replay component tests valid
proofs, forged axioms, altered conclusions, assumptions, invalid theorem tags,
and fixed-constant replacement. The prepared verifier rejects a valid article
proving `T` instead of the fixed Certificate, after loading all 904,476 bytes as
literals. This runtime regression is reproducible with `verifier/test_replay.py`.

Replay uses frozen bytes and sanitized score literals, a fixed operator heap,
a private working directory and resource limits. It checks the exact closed
certificate statement. There is no participant ML execution or admitting-axiom
fallback. No positive full Certificate replay has been produced yet.

## Remaining proof work

The baseline challenge certificate is **not proved**. Outstanding work includes
reduced-target semantic agreement, connecting compiler correctness to the fixed
cache-hook evaluator, wellformedness and configuration/resource premises,
bootstrap and installation from zero RAM, and a complete replayable article.
The upstream compiler correctness theorem has explicit installation and resource
premises; the concrete compiler equality does not discharge them.

## Certificate continuation

The baseline zero-RAM bootstrap in `initBootstrapScript.sml` passes an isolated
HOL build, including its 208-byte size, instruction and layout checks. The
native entry is 0x80000400, leaving space for the bootstrap/dispatch slots while
keeping the larger native output below the fixed source code-buffer headers.
Encoding and layout facts do not by themselves prove bootstrap execution.
`initBaselineRom` also passed an isolated build: its 950,336-byte image contains
the exact native bytes and initialization data at the specified offsets. The
candidate image is in `artifacts/baseline/`. Its admission proof is now checked
(see below); its full Certificate remains unproved.

The build driver now includes upstream Pancake/backend/RISC-V semantic proof
sources. `pan_to_targetProofTheory` and `riscv_targetProofTheory` are required
prerequisites for the semantic certificate. The old-toolchain build exposed
failures in `bvl_to_bviProof`, `clos_callProof`, and `word_instProof`; other dependencies continue
building. A compatibility test with the newer provenance HOL pin failed earlier
in `flatLang` (`exp6_size` missing), so that pin has not replaced `tested_hol`.
The missing register-allocation proof directory has also been added to the
build search path for the next semantic build.

The single Python entry point now supports `--local`, `--structural-only`,
`--progress`, and `--hol`, with automatic preparation of the fixed verifier.
Twenty Python boundary/command tests pass. The complete certificate and the
remaining original CLI options are still outstanding.

The newer HOL failure coincides with its October 3 datatype-package switch;
the August checkout predates the September tactic updates. An isolated checkout
at `7f769972f0acf26df39facd83339c05a66d9ff26` (October 1) is being built to test
the combination of newer tactics and the previous datatype package. It is an
unverified compatibility candidate, not a replacement for `tested_hol` yet.

## Bootstrap execution lemmas and toolchain compatibility

`initBootstrapMemoryTheory` passes the normal HOL build. It proves byte reads
and writes, exact eight-byte copying, preservation of other memory and
registers, non-failure under alignment/domain premises, and commutation with
PC updates. The word-result width is explicitly 64 bits, independently of the
address width in HOL's polymorphic `read_mem_word`.

`initBootstrapLoopTheory` also passes (40 s observed). It takes its five
instructions directly from `bootstrapBlocks`, computes their encoder lengths
with cv, and proves the complete assembler-state effect: copied memory, both
pointers advanced by eight, preserved end pointer/domain/endian/failure flag,
and the exact back-edge or fall-through PC. This still requires instruction
installation and RISC-V simulation to obtain the full machine trace.

The October 1 HOL compatibility candidate built successfully. All four
previously failing theories (`bvl_to_bviProof`, `clos_callProof`, `word_instProof`,
and `panProps`) now pass unchanged. A full compiler/challenge/semantic-proof
build is running in `.build-hol-compatible`; `tested_hol` remains unchanged
until that wider validation succeeds. Missing GC and register-allocation proof
source directories are now included by the build driver.

The real `verify.py --local` path automatically rebuilt its stale fixed heap
and rejected the unrelated truth article after preparation. Twenty Python
verifier tests also pass. No positive baseline Certificate is claimed.

## Finite bootstrap initialization copy

`initBootstrapIterationTheory` passes the normal build (31 s observed). It
proves pointer advancement, preservation of memory outside the destination,
byte-for-byte copying under explicit separation premises, non-failure under
alignment/domain premises, and the exact loop branch/exit PC for any finite
iteration count. Its loop body is the five actual bootstrap instructions.

`initBootstrapCopyTheory` specialises these facts to the fixed layout. The
4,616 iterations copy all 36,928 initialization bytes from ROM to RAM, preserve
all other memory, and exit after the final word. The concrete source/destination
separation and alignment arithmetic is proved, with memory-domain membership
remaining an explicit premise. The full theory rebuild passed (33 s observed).

`initBootstrapStartupTheory` passes the normal rebuild (35 s observed). It
proves the three actual prefix instructions set
the expected pointers and enter the copy loop at `0x80000018`. Its composed
`bootstrap_copy_effect` theorem reaches `0x8000002c`, copies the full data
range, preserves other memory, and has no failed-state flag, assuming the
initial PC, little-endian/non-failed state, and access to both memory ranges.

These are proofs of the assembler state updates. Instruction installation,
RISC-V step simulation, the remaining bootstrap stores, and composition with
compiler correctness remain necessary for the complete Certificate. No
participant statement or fixed verifier condition was relaxed.

The compatibility build also passed upstream `riscv_targetProofTheory`
(349 s observed). `pan_to_targetProofTheory` and the final evaluated artifact
theories are still running; the recorded tested toolchain has not changed.

## Complete bootstrap assembler-state effect

The full compatibility build at HOL
`7f769972f0acf26df39facd83339c05a66d9ff26` passed all 230 requested theories,
including `pan_to_targetProofTheory` (490 s), `riscv_targetProofTheory`
(349 s), the fixed challenge and replay theories, full compiler computation,
and `initBaselineRomTheory`. The resulting native bytes, bootstrap bytes,
and baseline ROM match the checked-in artifact hashes exactly. The copy,
iteration, and startup theories also passed on this HOL version.

`initBootstrapStoresTheory` proves a factored little-endian byte-memory view
of `write_mem_word` and `mem_store`, including selected-byte and outside-memory
lemmas. `initBootstrapSuffixTheory` proves the actual suffix's entry registers,
entry PC, eight exact header/pointer stores, and non-failure under the two
explicit writable-range premises. Reducing individual instruction projections
avoids the large expression expansion caused by unfolding the entire state.

`initBootstrapState.bootstrap_final_effect` composes the entire bootstrap's
assembler state updates through native entry. It passed the normal build
(27 s; its suffix ancestor took 66 s). The theorem states the native PC,
registers 10--13, non-failure, and the exact installed byte-memory function.
The input PC, little-endian/non-failed input state, and ROM/RAM domain premises
remain explicit. Instruction installation and RISC-V execution simulation are
not supplied by this state-update theorem. The complete challenge Certificate
and positive certificate replay remain unfinished.

The recorded `tested_hol` pin is now the October 1 revision above. The original
August build cache was preserved locally, and `.build` selects the existing
compatible cache without relocating its generated loaders. Twenty verifier
unit tests and six importer tests pass with the updated trusted pin/manifest.

The final suffix and composed-state theories also passed on the new tested
HOL pin (69 s and 32 s). The fixed verifier heap was rebuilt successfully.

The real-HOL replay regression on this heap loaded all 904,476 submitted
literal bytes and rejected an unrelated truth theorem at the exact Certificate
conclusion check. This is a negative boundary test, not a positive certificate.

## Original verifier CLI options

The single Python entry point now supports all original option names:
`--local`, `--trusted`, `--work`, repeatable `--hide`, `--structural-only`, and
`--progress`. The trusted root is explicit operator input. Work directories
are fresh/private and retain the sanitized submission and replay log. Path
hiding uses Bubblewrap with read-only host mounts and a writable private
workspace; inability to apply isolation rejects the replay.

All 25 verifier unit tests pass, including trusted-root selection, retained
literal snapshots, immutable input across preparation retries, and rejection
of missing sandbox support or hidden required paths. A real isolation test
checks both file and directory masking, unchanged host files, and workspace
writes. A real subprocess test invokes the original CLI flags with all
904,476 bytecode bytes, hides the original submission and a separate private
directory, automatically rebuilds the stale heap, and reaches the exact
Certificate-conclusion rejection for an unrelated proof. The full baseline
Certificate and positive replay are still outstanding.

## Native-byte installation and compiler layout bridge

`initBootstrapFrameTheory` passed (31 s). It proves preservation of memory
below initialization RAM, the memory domain/endian flag, and CakeML's
`bytes_in_memory` predicate for code in that range.

`initInitialCodeTheory` proves byte installation from the fixed
`initialMemory` definition. Code-range bytes are independent of shared
input/output memory. Addresses at or above the submission anchor cannot
coincide with reserved FFI entries under the challenge's anchor-spacing
condition. Its general code-slice installation theorem passed (14 s).

`initNativeInstalledTheory` passed (76 s). It connects the checked ROM-slice
equality to the exact compiled native bytes in initial memory, then preserves
their installation through the bootstrap state updates. Its premises bind
the submission to `baselineRom` and `baselineNativePc`, retain the FFI spacing
condition, and bind the assembler memory/domain to the fixed initial memory
and program domain. This does not prove a RISC-V execution trace.

`pancakeCorrectnessBridgeTheory` passed (18 s). With performance calls disabled,
the compiler entry point used by Pancake's semantic correctness theorem and
the concrete `from_word_0` pipeline produce equal bytes, bitmaps, and target
layout. Symbol names and intermediate configuration bookkeeping are projected
out by a proved equality. The stack/resource and source-semantic premises of
the correctness theorem remain necessary.

`initCorrectnessInput.guest_correctness_compilation` instantiates that bridge
for the fixed prepared guest and checked allocation. The theorem gives a
successful `compile_prog_max` result containing the exact `compiledBytes`,
`compiledBitmaps`, and target layout from `compiledConfig`. The stack maximum
is an existential output, not an established resource bound. This discharges
the concrete compilation premise, not all premises of semantic correctness.
The complete `initCorrectnessInputTheory` rebuild passed on the tested HOL pin
in 81 s. All new results are checked for hypotheses and untrusted theorem tags.

## Source correctness premises

`initSourceChecksTheory` passed a fresh build (65 s). Kernel-checked evaluation
of the fixed `prepared_guest` proves `pancake_good_code`, distinct parameters,
distinct function names, and the exception-count bound required by
`pan_to_target_compile_semantics`. The operand traversal uses first-order
recursive equations proved equivalent to the upstream `every_exp` predicate;
its translation preconditions are discharged by datatype induction.

`initGlobalLayoutTheory` passed (61 s). The guest has no named-structure
declarations, its structure context is empty, and its global declarations
occupy exactly **93 words**, equal to the fixed challenge's `globalsWords`.
Declaration checks and shape extraction use `cv_compute`; the small resulting
shape list is evaluated in the kernel.

`initSourceAllocationTheory` passed its final rebuild (56 s). It proves the
global allocation premise for every input
of the fixed `sourceInitialState`. Ordinary memory lies below the globals,
the globals lie above ordinary memory, the region endpoint is outside ordinary
memory, and its byte size fits in 64 bits. `prepared_source_premises` combines
this result with the syntax checks and empty initial code/local/global/exception
maps. These are closed results checked for hypotheses and untrusted theorem tags.

Reproduce this theory chain with:

```sh
python3 tools/build.py --hol /path/to/tested-HOL initSourceAllocationTheory.uo
```

The results discharge specific source-side premises of the compiler theorem.
Target installation/execution, sufficient runtime stack/heap bounds,
and the final challenge Certificate remain separate obligations. A positive full certificate replay remains
outstanding.


## Compiler source order preserves challenge behavior

`panMainOrderTheory` passed (7 s). A function declaration commutes with a
neighboring declaration when the neighbor does not define the same function
name. This covers globals and exceptions as well as functions; global
initializer evaluation is independent of the function map. Induction lifts the
swap to a declaration prefix. Named-structure processing is also preserved.

`initSourceOrderTheory` passed (59 s). Checked evaluation shows the fixed AST
ends with `main` and the prefix contains no other function of that name.
Instantiating the generic theorem proves, for any initial state and start name,
that `prepared_guest` and `guestAst` have equal declaration semantics. In
particular:

```text
|- semantics_decls (sourceInitialState input) «main» prepared_guest =
   sourceBehaviour input
```

This closes the source-order gap between the compiler correctness theorem and
the fixed challenge. All exported semantic results are checked for hypotheses
and untrusted theorem tags. The challenge definitions are unchanged.

```sh
python3 tools/build.py --hol /path/to/tested-HOL initSourceOrderTheory.uo
```

## Exact serialized compiler configuration

`initConfigNumbersTheory` checks a proposed list of 69,393 numbers against
the saved configuration characters and derives exact character decoding using
the upstream inverse theorem. `initDecodedConfigTheory` then obtains a candidate
record from a conditional decoder translation and checks its entire encoding:

```text
|- encode_backend_config candidateConfig = compiledBackendConfig
|- compiledConfig = candidateConfig
```

The final configuration theorems are closed and checked for untrusted theorem
tags. Decoder preconditions are retained, and their conditional results supply
only candidate data. The unconditional encoding equality and upstream
encode/decode inverse establish the result. The local decoder translator derives
a variant of the pinned HOL translator without modifying HOL or CakeML sources;
it fails if the expected source patterns change.

The split configuration theory passed (253 s wall time, including ancestor
loading). This result supplies exact compiler metadata; it does not establish
baseline admission or the challenge Certificate.

```sh
python3 tools/build.py --hol /path/to/tested-HOL initDecodedConfigTheory.uo
```

## Baseline submission admission

`initCompiledMetadataTheory` passed (79 s wall time). Its checked configuration
contains **20 external FFI names** and **13 MMIO records**, for 33 total names.
Every MMIO address offset is nonnegative.

`initBaselineAdmissionTheory` passed its complete build. It proves:

```text
|- baselineMetadataRoundtrip
|- admitted baselineSubmission
|- initialPc + LENGTH bootstrapBytes <
   baselineNativePc - ffiOffset * (compiledFirst + 2)
```

The submission uses the exact 950,336-byte baseline ROM and the exact compiled
metadata. The roundtrip check rules out information loss when converting signed
compiler offsets to the natural offsets of the fixed challenge. Admission is
proved by kernel evaluation of the concrete metadata and proved ROM length,
using finite-quantifier equivalences. Compiler computation and metadata literal
extraction use `cv_compute`. All exported results are closed and tag-checked.

```sh
python3 tools/build.py --hol /path/to/tested-HOL initBaselineAdmissionTheory.uo
```

This establishes layout admissibility. Actual bootstrap execution, compiler
resource/installation premises, restricted-machine simulation, and the complete
challenge Certificate still require proofs. No positive full certificate replay
is claimed.

## Bootstrap instruction fetch

`initBootstrapInstalledTheory` passed. It proves that the bootstrap's 208 bytes
are installed in the admitted baseline's initial program domain, for every
input. A domain lemma excludes all reserved dispatch slots below native entry.
Checked evaluation verifies the offset, bounds, and exact encoded slice for
every bootstrap instruction. A generic memory-slice theorem then yields:

```text
|- MEM (pc,instruction) bootstrapBlocks ==>
   bytes_in_memory (n2w pc) (riscv_enc instruction)
     (initialMemory baselineSubmission input)
     (programDomain baselineSubmission)
```

All exported results are closed and checked for untrusted tags. This establishes
initial fetchability. The bootstrap execution trace must still establish these
fetch premises and successful assembler steps at each intermediate state,
including every copy-loop iteration, before lifting to restricted RISC-V.

```sh
python3 tools/build.py --hol /path/to/tested-HOL initBootstrapInstalledTheory.uo
```

## Bootstrap assembler steps and startup execution

`initBootstrapStepTheory` passed. Its ROM invariant fixes the program domain
and preserves initial memory below `bootDataRam`. The fetch-preservation theorem
transfers the checked instruction encodings to any state satisfying that
invariant. `bootstrap_asm_step` then establishes the upstream `asm_step` relation
for a bootstrap instruction, given its declared PC, RISC-V configuration fields,
and a non-failing `bootAfter` result.

`initBootstrapPrefixStepsTheory` also passed. It defines `bootSteps` as a finite
sequence of those actual assembler steps and proves it for the three startup
instructions from the initial PC. The premise requires the ROM invariant,
link register index 1, little endian state, alignment 2, and no initial failure.
The instruction memberships and encoded lengths are checked in HOL. All
exported results are closed and tag-checked.

```sh
python3 tools/build.py --hol /path/to/tested-HOL initBootstrapPrefixStepsTheory.uo
```

The copy-loop iterations and suffix still need their step-sequence proofs.
The restricted RISC-V simulation and full challenge Certificate remain
outstanding; these startup results do not imply a complete certificate.

## Trace composition and copy-loop ROM preservation

`initBootstrapExecutionTheory` passed. `bootSteps_append` composes checked
instruction sequences, and `bootSteps_RTC` turns such a sequence into the
upstream reflexive-transitive assembler-step relation ending at `bootRun`.
Configuration fields (link register index, alignment, endianness, and memory
domain) are preserved by `bootRun`; the link register index and alignment are
also preserved by `copyIterations`.

The ROM invariant is preserved by one copy-loop state update and by any finite
number of iterations when their destination bytes lie at or above
`bootDataRam`. These results use the existing proved write-footprint lemmas;
all exported results are closed and tag-checked.

```sh
python3 tools/build.py --hol /path/to/tested-HOL initBootstrapExecutionTheory.uo
```

The step premises for the five instructions in a copy-loop iteration must
still be established and composed through all 4,616 iterations. ROM
preservation alone does not prove those steps or the final Certificate.

## Copy-loop instruction execution

`initBootstrapCopyStepsTheory` passed. `copy_loop_steps` proves `bootSteps
copyLoopBody s`: the load, store, two pointer increments, and conditional branch
all take valid upstream assembler steps. Its premises require the fixed loop
entry PC, the RISC-V configuration fields, no initial failure, aligned source
and destination words, membership of all eight accessed bytes in the memory
domain, and destination bytes above the executable ROM.

The theory checks load safety, load/store configuration-field preservation,
and preservation of the ROM invariant. It handles both branch outcomes. The
encoded instruction lengths and membership at their fixed bootstrap PCs are
checked in HOL. All exported results are closed and tag-checked.

```sh
python3 tools/build.py --hol /path/to/tested-HOL initBootstrapCopyStepsTheory.uo
```

The finite 4,616-iteration execution theorem remains to be assembled from this
per-iteration result and the existing pointer, memory, and branch-bound proofs.
Suffix execution, restricted RISC-V simulation, and full Certificate replay
also remain outstanding.

## All 4,616 copy iterations execute

`initBootstrapCopyExecutionTheory` passed. It composes the checked five-instruction
loop body into `copyInstructions 4616` and proves that its state update agrees
with `copyIterations 4616`. The fixed address bounds establish alignment,
memory-domain membership, and ROM separation at every intermediate iteration.
The proof also establishes each iteration's loop-entry PC and non-failure.

`baseline_copy_execution` proves the upstream reflexive-transitive assembler-step
relation from loop entry to `copyIterations 4616 s`, given the initial ROM
invariant, configuration fields, fixed source/destination/end pointers, no
initial failure, and membership of the 36,928 source and destination bytes in
the memory domain. All exported results are closed and tag-checked.

```sh
python3 tools/build.py --hol /path/to/tested-HOL initBootstrapCopyExecutionTheory.uo
```

This closes finite copy-loop execution at the assembler level under those
premises. Connecting the complete startup/copy/suffix trace from the fixed
initial machine state, lifting it to restricted RISC-V, and completing the
challenge Certificate remain outstanding.

## Runtime-initialization suffix execution

`initBootstrapSuffixStepsTheory` passed its complete build (8m24s for the theory,
plus ancestor loading). It proves `bootSteps bootstrapSuffix s`, covering the
runtime-bound stores, source-header stores, native-entry register setup, and
final jump. The premises are the ROM invariant, suffix-entry PC, RISC-V
configuration fields, no initial failure, and membership of the 24-byte and
40-byte initialization regions in the memory domain.

Each instruction uses the checked fetch/step theorem. Generic store-field
preservation and the low-memory write-footprint rule discharge configuration
and ROM-preservation conditions. All exported results and generated rewrite
rules are closed and tag-checked. Evaluation never unfolds the entire baseline
ROM to prove a store's local memory-domain premise.

```sh
python3 tools/build.py --hol /path/to/tested-HOL initBootstrapSuffixStepsTheory.uo
```

Composition with startup and copy execution, connection to the fixed initial
machine, restricted RISC-V simulation, and the final Certificate remain separate
obligations.

## Complete assembler bootstrap trace

`initBootstrapFullExecutionTheory` passed. `bootstrap_full_execution` composes
the startup prefix, all 4,616 copy iterations, and the initialization suffix into
the upstream reflexive-transitive assembler-step relation from `s` to
`bootFinalState s`. ROM preservation is carried across both phase boundaries.

The theorem assumes the initial PC and RISC-V configuration fields, the initial
ROM invariant, no initial failure, and membership of the copy-data and header
regions in the memory domain. The existing `bootstrap_final_effect` supplies
the native-entry PC, registers, and final memory effects. All exported results
are closed and tag-checked.

```sh
python3 tools/build.py --hol /path/to/tested-HOL initBootstrapFullExecutionTheory.uo
```

This closes composition of the assembler bootstrap trace. The fixed initial
challenge machine must still be related to an assembler state satisfying these
premises. Restricted RISC-V simulation, compiler resource/installation premises,
and the complete challenge Certificate and positive replay remain outstanding.


## Fixed initial assembler state and native entry

`initBaselineInitialTheory` passed a clean build (91 s reported theory time,
plus ancestor loading). `baselineInitialAsm input` explicitly fixes every
assembler-state field: zero registers, the challenge's `initialMemory` and
`programDomain`, initial PC, and RISC-V configuration fields.

- `baseline_bootstrap_domains` discharges all 36,928 source and destination
  copy-byte memberships and all 40 source-header byte memberships.
- `baseline_initial_target_relation` relates this assembler state to the fixed
  challenge `initialState baselineSubmission input` using upstream
  `target_state_rel`.
- `baseline_bootstrap_execution` proves the complete assembler-step RTC from
  that concrete initial state to `bootFinalState`, with no remaining premises.
- `baseline_native_installed` proves that the exact compiled native bytes are
  installed in the resulting memory and domain.
- `baseline_native_entry` proves the native entry PC, registers 10–13, and the
  absence of assembler failure.

All results are kernel checked, closed, and tag checked. The input remains
universally quantified. This discharges the concrete initial-state premises
of the preceding bootstrap trace; lifting the trace to restricted RISC-V and
`challengeEvaluate`, compiler semantic installation/resource premises, and a
complete Certificate with positive replay remain outstanding.


## Restricted instruction step agreement and bootstrap words

`initRestrictedStepTheory` passed (13 s reported theory time). It proves that
`restrictedNextRISCV` and upstream `NextRISCV` agree whenever the fetched
instruction is a full word whose decoded constructor is supported. The
corresponding target-next equality and equality of target-state relations are
also checked. Fetch and support are explicit premises; this is not yet an
execution trace transfer.

`initBootstrapRestrictedTheory` passed (33 s reported theory time). Checked
computation constructs the 52 little-endian words from the exact 208 bootstrap
bytes and proves that every word decodes to a supported instruction. The
indexed corollary `bootstrap_word_supported` applies at each offset `4*i` for
`i < 52`. Both theories check that their exported results are closed and have
acceptable proof tags. Native-code support and the whole restricted execution
trace remain outstanding.


## Encoder correctness for the restricted RISC-V target

`initRestrictedRulesTheory`, `initRestrictedEvaluatorTheory`,
`initRestrictedTargetTheory`, and `initRestrictedEncoderTheory` passed.
The encoder proof took 5m07s of theory time, plus loading. Its final result is:

```text
|- encoder_correct restrictedTarget
```

The adapted proof retains the pinned CakeML assembler/configuration arguments.
A local evaluator is derived from the pinned HOL RISC-V step library. Before
applying each restricted step rule, it proves that the decoded instruction's
constructor satisfies `supported_instruction`. It never asserts this premise
or widens the challenge's decoder. The adapter refuses unsupported `ADDW`;
checked arithmetic, load, store, conditional-branch, and jump examples pass.
The HOL and CakeML checkouts are not modified by this adapter.

The full encoder proof covers all valid assembler instructions under the
RISC-V configuration, including the absence of usable floating-point registers.
The final theorem is closed and passes `check_thm`. This supplies the restricted
encoder premise required by compiler correctness, rather than an unchecked
whole-ROM instruction scan.

`initEncoderExecutionTheory` also passed. `encoder_rtc_reaches` lifts a finite
assembler-step RTC and an initial target-state relation to finite target-next
execution with the final target-state relation. This generic result does not
by itself establish the additional checks of `challengeEvaluate`.


## Restricted CPU bootstrap execution from the fixed initial state

`initBaselineRestrictedExecutionTheory` passed a clean build (96 s reported
including theory loading). For every input, `baseline_restricted_execution`
proves a finite RTC of `restrictedTarget.next` from
`initialState baselineSubmission input` to a state related to the complete
assembler bootstrap result.

`baseline_restricted_native_entry` exposes the resulting machine facts:

- `riscv_ok final`;
- native entry PC `0x80000400`;
- registers 10–13 equal the native entry, source base, stack start, and RAM end;
- all exact compiled native bytes installed in `final.MEM8` under the fixed
  `programDomain baselineSubmission`.

Both execution results are closed and tag checked. This is execution of the
restricted CPU from the challenge's actual initial state, including zero RAM.
It does not yet prove execution by `challengeEvaluate`, whose program-domain,
FFI, and memory-interference checks must also be connected. The full baseline
Certificate and positive article replay are still not proved.


## Restricted machine-configuration premise

`initMachineConfigTheory` passed a clean build (15 s reported). It derives
`enc_ok riscv_config` from restricted encoder correctness and proves:

```text
|- mc_conf_ok (challengeMachineConfig pc program shared names nexternal extra)
```

This holds for arbitrary layout arguments; admission separately validates the
concrete layout. It discharges the compiler theorem's `mc_conf_ok` premise for
the challenge machine. Backend configuration, initial installation, resource
bounds, and semantic/evaluator composition remain distinct obligations.


## Normal-instruction simulation inside the fixed challenge evaluator

`initChallengeStepTheory` passed a clean build (16 s reported). It adapts the
pinned CakeML `targetProps` normal-instruction prefix proof to
`challengeEvaluate`. The theorem `asm_step_IMP_challenge_step` proves that an
assembler step executes in a nonzero number of challenge-evaluator steps,
with the final target-state relation and equality for every remaining fuel.
Its premises retain encoder correctness, matching program/memory domains,
instruction-range disjointness from FFI entries, permitted interference, and
the initial target-state relation.

Only the normal-instruction evaluator branch is used. The fixed cache-hook
and FFI branches retain their challenge definitions. Explicit 64-bit RISC-V
configuration types are required in inherited tactic instantiations to avoid
introducing unrelated polymorphic configurations with the same printed name.
Both exported simulation theorems are closed and tag checked. Trace composition
and concrete bootstrap FFI-disjointness remain to be instantiated.


## Composition of challenge-evaluator instruction prefixes

`initChallengeExecutionTheory` passed a clean build (15 s reported).
`challenge_rtc_execution` composes a finite `challengeAsmEdge` trace into an
equality of `challengeEvaluate` prefixes for every remaining fuel, preserving
the final target-state relation. Each edge explicitly requires an assembler
step, the fixed program/memory domain, and an instruction range disjoint from
FFI entries. `challenge_identity_interference` discharges the identity
interference premise for `challengeMachineConfig`; `identity_shift_interfer`
shows that consuming such interference leaves the configuration unchanged.

The composition and instruction results are closed and tag checked. Applying
the theorem to the concrete bootstrap requires the stronger assembler trace
with the FFI-range condition on every edge; the previously proved raw CPU RTC
alone does not supply that condition.


## Correct native placement for the fixed source header

The installation predicate `pan_installed` requires the source header's code
buffer start to equal native entry plus the exact compiled byte count. The
fixed challenge source memory contains `0x800ddd08` in that header. The former
entry `0x80000400` ended the 904,476-byte image at `0x800dd11c`; the earlier
non-overlap inequality was insufficient for installation.

The candidate native entry is now **`0x80000fec`**, making its end exactly
`0x800ddd08`. The fixed challenge/source definitions and compiled native bytes
are unchanged. `initBootstrap`, `initBaselineRom`, and `initBaselineAdmission`
passed clean rebuilds (31 s, 85 s, and 108 s reported). The new closed,
tag-checked theorem `native_ends_at_fixed_buffer` proves the required equality.
The candidate ROM and bootstrap binaries and their manifest hashes were
regenerated from these checked builds. Dependent execution proofs are being
rebuilt for this placement; earlier sections reporting `0x80000400` describe
the previous development layout. The full Certificate remains unproved.


## Bootstrap FFI separation and strengthened instruction steps

For the corrected native placement, `initBootstrapFfiTheory` and
`initBootstrapChallengeStepTheory` passed clean builds (92 s each reported).
Checked computation derives all baseline FFI addresses and proves that they
are at or above the end of the 208-byte bootstrap. The range theorem and
`bootstrap_instruction_ffi_disjoint` then show that every bootstrap instruction
is disjoint from those entries.

`bootstrap_challenge_step` combines that result with the actual assembler-step
proof and the fixed ROM/domain invariant. `challengeBootSteps` records the
stronger edges required by the challenge-evaluator simulation;
`challengeBootSteps_append` and `challengeBootSteps_RTC` compose them.
All exported results are closed and tag checked. The strengthened whole-trace
build is continuing through startup, the copy loop, and initialization.


## Complete bootstrap execution in the fixed challenge evaluator

The dependent proofs were rebuilt for native entry `0x80000fec`. Both suffix
proofs passed (615 s for the assembler trace and 623 s for the stronger
challenge trace, including ancestor loading). The prefix, 4,616-iteration copy
loop, final stores, native entry, and ROM preservation compose into
`bootstrap_challenge_trace`.

`initBaselineChallengeExecutionTheory` then passed a clean build (93 s).
`baseline_challenge_execution` proves the existence of a finite prefix length
and native-entry machine state such that, for every remaining fuel, evaluating
the fixed baseline from its fixed initial state is exactly evaluating from that
native-entry state. The final state is related to the proved assembler
`bootFinalState`. `baseline_bootstrap_timeout` exposes the corresponding
finite prefix result and unchanged FFI state. This uses `challengeEvaluate`
itself, including its instruction checks and fixed memory/FFI boundaries.

The final instantiation must specialize the FFI type before assuming the
polymorphic simulation theorem: specializing an already-assumed proposition
would change a hypothesis. The checked script performs this specialization on
the closed theorem instead.

## Source memory, configuration, and native proof components

`initBootstrapSourceMemoryTheory` passed a clean build (32 s), proving the five
fixed source header words and preservation above those headers.
`initBaselineSourceMemoryTheory` passed (85 s): for every address in
`ordinaryDomain`, packing the eight final machine bytes produces exactly the
word in fixed `sourceMemory`. This includes the zeroed ordinary heap beyond
the headers. The challenge source definitions were not changed.

`initBackendConfigTheory` passed (73 s), proving backend configuration validity
and the initial machine-configuration premise for the exact compiler input.
`initChallengeNopTheory` passed (16 s), extending normal instruction simulation
to compiler padding while retaining the companion interference-search equality.

`initNoInstallTheory` passed (79 s). `guestLabProgram` follows the same
word-to-word, word-to-stack, and stack-to-lab pipeline as the resource-aware
compiler, and `guest_lab_no_install` proves the absence of lab-level dynamic
installation. The upstream theorem is explicitly specialized to 64-bit source
words; its lab-language conclusion alone does not determine that type.

`initMachineReturnTheory` passed (15 s). It proves the assembler/target
relations for the fixed external-call return and MMIO read/write returns,
including alignment and the MMIO destination register bound. The disabled
floating-point register clauses are discharged using the fixed RISC-V config.

These are closed, tag-checked proof components. The full native execution
connection, FFI/compiler installation obligations, sufficient stack/resource
bounds, full `Certificate`, and positive article replay remain to be proved.
In particular, the generic CakeML installation callback obligation does not
hold for the fixed cache-hook callback. The no-install result is a premise for
bridging that semantic difference, not a completed bridge.


## FFI installation and an auxiliary compiler configuration

`initFfiInstallationTheory` passed a clean build (18 s).
`admitted_ffi_interference` proves CakeML's `ffi_interfer_ok` for every admitted
submission using the fixed challenge callbacks. Admission supplies the exact
external/MMIO boundary, MMIO register bounds, and aligned return addresses;
`mmio_info_before_boundary` rules out MMIO metadata for external calls.

`initChallengeConfigTheory` passed (16 s).
`challenge_install_callback_irrelevant` proves, for every fuel and machine/FFI
state, that changing only `install_interfer` leaves `challengeEvaluate`
unchanged. The fuel induction unfolds both sides explicitly, uses unchanged
FFI-array reads, and commutes installation-callback updates past next/FFI
interference updates.

`initCompilerMachineTheory` passed (18 s). Its auxiliary
`compilerMachineConfig` supplies the callback required by the upstream
compiler theorem: copy the already-read bytes, return to the link register,
and return the destination address in register 10. The theory proves
`install_interfer_ok`, preserves the proved FFI condition, and establishes
exact equality of its `challengeEvaluate` results with `submissionConfig`.
The fixed challenge files and verifier statement are unchanged.

This does not establish equality of upstream `targetSem.evaluate` and the
cache-hook evaluator. A native simulation using the no-install property is
still required, along with the remaining memory/bitmap installation and
resource obligations, before a full Certificate or positive replay is claimed.


## Packed source memory and copied bitmap bytes

`initPackedMemoryTheory` passed a clean build (31 s). It constructs a total
64-bit word view of the actual machine byte memory and proves the compiler's
byte/word correspondence, including addresses that are not word aligned.
`initBaselinePackedMemoryTheory` passed (84 s): on every ordinary source
address, that view of native-entry memory agrees with the fixed source memory,
using the source-to-word value conversion.

`initBootWordBytesTheory` passed (75 s), proving little-endian word recovery
and indexing/slicing of flattened word encodings. `initBitmapFrameTheory`
passed (31 s), proving that the bootstrap's header stores preserve the copied
bitmap bytes. `initBaselineBitmapBytesTheory` passed (88 s): every byte in the
bitmap portion of the concrete native-entry memory equals the corresponding
byte of the fixed ROM data image.

`initWordListMemoryTheory` passed (9 s). Its generic lemma constructs a
separated `word_list` from indexed memory equalities over the exact generated
address domain. These theorems are closed and tag checked. Reconstruction of
the concrete bitmap word allocation and the remaining installation,
native-simulation, resource-bound, Certificate, and positive-replay obligations
are still pending.


## Exact native-entry bitmap allocation and target configuration

`initBaselineBitmapWordsTheory` passed a clean build (98 s), reconstructing
each of the 4,613 compiled bitmap words from the copied machine bytes.
`initBitmapDomainTheory` passed (29 s): its aligned byte domain is exactly the
word-address image, and the byte domain is closed under alignment.
`initWordListMemoryTheory` then connects indexed memory equalities to the
compiler's separated word-list predicate. `initBaselineBitmapInstalledTheory`
passed (95 s), establishing the exact bitmap allocation and empty data stack
in that predicate.

`initDataDomainTheory` passed (31 s), proving heap/stack alignment closure,
separation from the bitmap region, and disjointness of both ordinary regions
from shared I/O memory. `initBaselineConfiguredTheory` passed (91 s): the
proved bootstrap execution preserves the memory domain, link-register index,
instruction alignment, and endianness, and the resulting native-entry state
satisfies `target_configured` for the auxiliary compiler machine.

All results are closed and tag checked. The complete `pan_installed` contract,
native no-install simulation, stack/resource bounds, full Certificate, and
positive article replay remain outstanding.


`initBaselineDataDomainTheory` passed a clean build (86 s). The entire
heap/stack and bitmap byte-domain union is contained in the baseline program
domain and, using the proved bootstrap constants, in the actual native-entry
assembler memory domain. This discharges the data-domain containment component
of `good_init_state`; the full installation contract is still incomplete.


## Native code placement and shared-memory setup

`initCodeMemoryTheory` passed a clean build (14 s). It derives separated code
installation from indexed byte facts and proves exact `read_bytearray` recovery
and `code_loaded` from a related target state. `initBaselineCodeMemoryTheory`
passed (93 s): the native image is disjoint from ordinary data, the 760-byte
code buffer is installed outside that data domain, the size does not wrap,
and every target state related to the native-entry assembler state has the
exact compiled code loaded.

`initFfiBoundaryTheory` passed (15 s), proving that admission's name-boundary
predicate selects exactly the compiler's external-call/MMIO boundary.
`initSharedDomainTheory` passed (33 s), proving alignment closure of shared I/O
memory, program/shared disjointness, and identity interference for the auxiliary
compiler configuration. The saved-PC layout and assembled `good_init_state`
proofs are still being checked; no full Certificate is claimed.

For the remaining resource obligation, the original Lean entry point is
`submission/InitECandidate/Proofs/SourceStackCertificate.lean`. It uses the
checker and proof in `Proofs/StackAnalysis/RankedBound.lean`: all direct calls
must target present functions of strictly smaller rank, all frames are at most
92 words, and an entry rank of 39 gives the bound `(39+1)*187 = 7480`. This is
evidence for implementing a compact HOL checker over the actual optimized
word program, not a checked HOL resource bound yet. The generated Lean stack
proof files need not be imported.


## Complete native-entry good_init_state

`initBaselineStartPcTheory` passed a clean build (91 s), checking the saved halt
and installation PCs, external dispatch slots, MMIO entries, alignment, and
exact name/entry lengths. Finite reserved-slot witnesses are discharged with
bounded existential evaluation after reducing set membership.

`initInstallationMetadataTheory` passed (77 s). `cv_compute` proves that the
checked decoded compiler configuration has exactly `SOME compiledFfiNames`
and `compiledMmio` in its lab configuration.

`initBaselineGoodInitTheory` passed (97 s). For any restricted machine state
related to the proved bootstrap final assembler state, it establishes the full
upstream `good_init_state` contract for the auxiliary compiler configuration,
the exact native bytes, 760-byte code buffer, packed word memory, ordinary
data allocation, and fixed shared I/O domain. This combines the checked target
setup, saved-PC layout, callbacks, code/data separation, byte/word relation,
and memory-domain closure/containment.

The enclosing `pan_installed` witness is still being checked. Native no-install
simulation, the resource bound, the full challenge Certificate, and positive
article replay remain outstanding.


## Complete native-entry pan_installed

`initBaselineMemoryHeadersTheory` passed a clean build (99 s), connecting the
five fixed startup headers to the packed native-entry memory without evaluating
the bootstrap again. `initBaselineMmioLayoutTheory` passed (95 s): `cv_compute`
checks the exact MMIO entry/exit layout, dispatch indices, and nonwrapping bound.

`initBaselineInstalledTheory` passed a clean build (109 s). For every restricted
target state related to the fixed bootstrap final assembler state,
`baseline_pan_installed` proves the complete upstream Pancake installation
predicate for the auxiliary compiler machine: exact native bytes, 760-byte
code buffer, 4613 bitmap words, zero extra data words, source memory, ordinary
and shared domains, startup headers, and MMIO metadata. All exported results
are closed and tag checked. The bootstrap challenge execution already produces
a state with the required target relation.

This completes installation. Native no-install simulation between the compiler
and fixed challenge evaluator, resource bounds, the full challenge Certificate,
and positive article replay remain outstanding.


## Challenge evaluator clock and observation properties

`initChallengeClockTheory` passed a clean build (30 s). It proves preservation
of non-timeout results when increasing the execution clock, monotonicity of
I/O event prefixes both from the initial state and between execution clocks,
and uniqueness of non-timeout results across clocks. All four theorems are
closed and tag checked for the fixed challenge evaluator, including its cache
hook. These are prerequisites for lifting native simulation to observable
challenge behavior; they do not yet establish the full Certificate.

`initLabSimulationHelpersTheory` passed a clean build (17 s), including explicit
closure and tag checks. It exposes 27 lemmas that were local to the pinned
CakeML compiler proof, covering encoded instruction bytes, byte arrays,
labels, and external-call indices. They support the no-install simulation
without changing the CakeML submodule. The full simulation is still under
proof development.


## Initial native simulation relation

`initLabInitialStateTheory` passed a clean build (17 s). It exposes the pinned
compiler proof that a correctly installed image establishes `state_rel` for
`make_init`, including external calls and shared-memory metadata. The theorem
is closed and tag checked. The same theory proves that `filter_skip` preserves
and reflects `no_install`, supporting the challenge-specific semantics bridge.

## Complete native no-install simulation

`initChallengeCompileTheory` passed a clean HOL build (360 s observed).
`challenge_compile_correct` proves that every non-error laboratory-machine
execution of code satisfying `no_install` is simulated by the fixed
`challengeEvaluate`, from related initial states and a tied oracle. It covers
ordinary instructions, all supported shared-memory widths, jumps, conditional
jumps, calls, label addresses, external callbacks, and halt. The dynamic-install
case is excluded by the stated `no_install` premise.

The proof uses the previously checked restricted-target instruction simulation;
it does not replace the challenge cache hook with the upstream install hook.
The exported theorem is closed and tag checked. Concrete 64-bit address
identities are proved with word arithmetic. Temporary debugging hooks were
removed before the clean build.

Lifting this result to observable semantics and the full Pancake compiler,
proving the resource bound, assembling `Certificate`, and positive article
replay remain outstanding.

## Observable semantics and lab compiler refinement

`initChallengeSemanticsTheory` passed a clean build (18 s observed). Its
`challengeMachineSem` records termination, divergence, and failure using the
fixed `challengeEvaluate`. For related initial states, a correct encoder,
`no_install` code, and non-failing lab semantics,
`challenge_machine_sem_EQ_sem` proves equality with the singleton lab behavior,
including the complete I/O trace. The divergence proof uses the checked clock
and prefix-monotonicity results.

`initChallengeLabCompilerTheory` passed a clean build (19 s observed).
`challenge_semantics_make_init` connects the installed-code initial relation to
observable semantics. `challenge_semantics_compile` composes that result with
label compilation, skip filtering, and aligned ordinary/shared memory domains.
It retains the upstream compiler and installation hypotheses and adds the
explicit `no_install` input-code requirement. Both exported results are closed
and tag checked.

The full Pancake composition and concrete resource bound still need checking;
these results do not yet establish the baseline `Certificate`.

## Checked input for stack analysis

`initStackInputTheory` passed a clean build (127 s observed). It uses
`cv_compute` to check the register-allocation hint and produce the optimized
word program. `optimized_word_compilation` proves that this literal is exactly
the result of the ordinary `word_to_word` compiler on the fixed guest input.
Total projections are used for CV translation; a separate checked theorem
requires compilation success. The exported compilation theorem is closed and
tag checked.

This provides the actual compiler output for a compact stack-bound checker;
it does not yet prove a stack bound or the full `Certificate`.

## Complete Pancake-to-challenge refinement

`initChallengePancakeTheory` passed a clean HOL build (395 s observed).
`challenge_pan_to_target_compile_semantics` composes the checked fixed-evaluator
lab compiler refinement with CakeML's word-to-stack, word-to-word, and
Pancake-to-word correctness results. It proves that the fixed
`challengeMachineSem` refines the source behavior, with the upstream explicit
resource-limit condition and installation/configuration premises. The absence
of dynamic installation is derived from the Pancake compilation pipeline.

The proof covers initialization, source memory agreement, the globals/heap
split, alignment, and the connection between stack limits in words and machine
address intervals. Concrete 64-bit arithmetic is discharged by small arithmetic
lemmas and directed bounds. The final theorem is closed and tag checked; no
interactive debugging hooks or admitted facts occur in the source.

This completes the general compiler/evaluator bridge. The concrete stack bound,
remaining baseline instantiations, full `Certificate`, and positive verifier
article replay still need to be completed.

## Compact stack ranking checker

`initStackRankTheory` passed a clean HOL build (31 s observed).
`call_graph_rank_bound` proves the word compiler's call-tree depth is bounded
by `(rank(n) + 1) * 187` when all code frames are at most 92 words and every
direct call has a present, strictly lower-ranked target. The proof covers
callee deletion, tail calls, continuations, exception handlers, and allocation.
`checkedRanks_bound` connects a finite executable checker to the full call
graph. The exported soundness theorems are closed and tag checked.

`initStackFramesTheory` also passed a clean build (322 s observed). It computes
the frame map and its maximum directly from the checked optimized 64-bit word
program using `cv_compute`, and proves the per-function frame formula agrees
with `word_to_stack.compile_prog`.

The program-specific ranking witness and its connection to `compile_prog_max`
remain to be checked. These results alone do not prove the full Certificate.

## Checked concrete stack certificate

`initStackEdgesTheory` passed a clean build (228 s observed), computing the
call edges of the exact optimized word program. `tools/build_stack_ranks.py`
constructs an untrusted ranking from that data: 826 functions, maximum rank 39,
entry function 64 at rank 39. No correctness theorem depends on the generator.

`initStackCertificateTheory` passed a clean build (101 s observed, plus 8 s
for the rank-data theory). Its `cv_compute` check validates every rank, callee
presence, continuation, handler, and frame-size condition directly against the
compiled program. `optimized_stack_bound` proves that the full entry call
graph has a defined depth of at most 7,480 words (59,840 bytes). This theorem
is closed and tag checked.

The computed maximum frame size is exactly 92 words.
`initStackFrameProofTheory` passed a clean build (96 s observed), proving that
the computed frame map is exactly the stack compiler's `stack_frame_size` map.
The connection to the full compilation theorem is checked separately in
`initStackLimitTheory`; the challenge Certificate still requires baseline
instantiation and positive verifier replay.

To regenerate and check the compact witness:

```sh
python3 tools/build.py --hol ../HOL-init-e initStackEdgesTheory
python3 tools/build_stack_ranks.py .build/stack-edges.txt experiments/initStackRanksDataScript.sml
python3 tools/build.py --hol ../HOL-init-e initStackCertificateTheory initStackFrameProofTheory
```

## Stack bound connected to full compilation

`initStackLimitTheory` passed a clean build (100 s observed).
`guest_bounded_compilation` strengthens the exact full Pancake compilation
result with `stack_max = SOME depth` and `depth <= 7480`, retaining the exact
compiled bytecode, bitmaps, and lab configuration. The connection unfolds the
ordinary compiler, uses the checked optimized word program, and applies the
proved frame-map correspondence. All exported theorems are closed and tag
checked. The baseline resource-limit and source/machine-state instantiation,
full challenge Certificate, and positive verifier replay remain.

## Baseline resource condition and finite execution

`initBaselineLimitsTheory` passed a clean build (137 s observed). It proves
that the compiler's `read_limits` stack capacity at the checked baseline native
entry is greater than 7,480 words, including the runtime's reserved storage.
`baseline_bounded_compilation` combines this with the exact compilation result
and proves its precise `option_lt` resource condition.

`initChallengeTotalTheory` passed a clean build (28 s observed). It proves the
fixed challenge machine semantics always has a behavior, using clock/trace
monotonicity for the divergence case. `challenge_singleton_termination` turns
refinement to a terminating behavior into an actual finite evaluator run with
the same outcome and I/O events. Both theories check closure and theorem tags.

The next step is to instantiate the Pancake refinement with the proved baseline
installation, source/configuration premises, and resource condition, then
compose bootstrap execution and export/replay the full challenge Certificate.

## Full baseline challenge Certificate

`initBaselineRefinementTheory` passed a clean build (143 s observed),
instantiating the Pancake-to-fixed-challenge theorem with the exact compilation,
source state, installed memory, configuration, layout, and stack-resource facts.
`baseline_native_refinement` refines the fixed source behavior whenever it is
not Fail; its resource condition is fully discharged.

`initBaselineCertificateTheory` passed a clean build (144 s observed). It
extracts finite native execution, composes the checked bootstrap, preserves the
source outcome and I/O events, and applies the fixed observation rules. Its
closed, tag-checked final theorem is:

```
|- initChallenge.Certificate initBaselineRom.baselineRom initParams.Infinity
```

The 950,336-byte exported `.build/baseline-rom.bin` matches the committed
`artifacts/baseline/rom.bin` byte for byte. The proof uses no participant-defined
challenge statement and no admitted facts. The tested HOL revision remains
`7f769972f0acf26df39facd83339c05a66d9ff26`.

A replayable article and positive run through the single Python verifier are
still required. The standard HOL kernel used for these checked builds does not
retain OpenTheory proof traces, so the saved theorem alone is not an exported
article. Export/replay remains explicit unfinished work.


## Independent article export and first full-pass replay

The author-only tracing HOL build now succeeds using `tools/prepare_exporter.py`.
The verifier continues to use the unmodified standard kernel. The author patch
records CV requests with proved equations and supports bounded dictionary
lifetimes; `articleReaderLib` adds the writer's missing version-6 commands using
kernel inference rules and the strict definition/axiom callbacks.

`initProofLibraryTheory` built successfully (43 s observed). Its closure consists
of generic compiler, semantics, and CV proofs; baseline-specific conclusions are
excluded. Its local inputs are included in the fixed integrity manifest.

A full `initSimplify` article exported successfully: 143,598,759 bytes before
compaction and 115,526,261 bytes after. Independent standard-kernel replay
checked 7,565 exported theorems, including the full guest simplification CV
computation. After compaction the observed replay process used about 4.5 GB RSS,
compared with over 70 GB while retaining the original article dictionary.
This is component evidence, not a full Certificate replay.

`initStructs` also exported (4,723,541 bytes before subsequent compaction).
The plan contains 81 baseline-specific theories. The updated author exporter
and its compactor pass the standalone positive replay regression; the strict
reader also passes the CV equation-selection and rejection checks. The 25 Python
sanitization/interface tests pass. Complete dependency export, final literal
binding, package assembly, and positive Python verification remain in progress.

### Literal binding export

The author exported the full 950,336-byte ROM's exact Certificate binding to
sanitized bytes and the `Infinity` score. The compact article is 47,987,416 bytes
(SHA-256 `8f5ad0aef7e19990ed67daa0b5e040eeb0ae9636fd3c66f2ea74bcb31e2c03e6`).
This is the final binding component, not a self-contained certificate: the
preceding baseline articles and full independent replay remain required.
The standard kernel separately passed the literal-request smoke replay and
rejected changed bytes and forged literal definitions. The real verifier also
loaded all 904,476 native byte literals and rejected an unrelated proof at the
exact-conclusion check.

### Full compiler proof export

The author recorded the full checked register allocation and RISC-V backend
computation in a 57,621,218-byte article. Its exported native binary is exactly
904,476 bytes with SHA-256
`4403ff7d9c7b663ba20a4e9c961547b2548530a56b15f238248886763009489e`,
matching the committed compilation artifact. Standard HOL separately evaluated
the complete allocation-literal conversion. The compact refinement article also
exports successfully after recording configuration unfolding before fixed
`EVAL` requests. Independent replay of the complete dependency chain is still
outstanding.


## Independent compiler replay through source preparation

A fresh standard-kernel process replayed the first five compiler articles in
sequence: `initSimplify` (7,565 theorems), `initStructs` (92), `initGlobals`
(128), `initCrep` (357), and `initPrepared` (2,575). This uses the previously
checked 115,526,261-byte simplification article and the newer following
articles. The process receives the fixed library and preceding replayed facts;
it does not import the built baseline theories.

This exposed symbolic normalization requests for pair reconstruction and
`TAILREC`. The reader now resolves these from proved logical/library facts and
rejects symbolic requests in its ordinary evaluation fallback. Small logical
requests are handled before the full library search. The real single-script
CLI regression still loads all 904,476 frozen native bytes and rejects an
unrelated proof at the exact Certificate-conclusion check.

The following loop compiler pass exposed an overly broad filter that excluded
all functions in theory `cv`, including the nonprimitive `cv_exp`. The filter
now excludes exactly the kernel CV primitives and accepts checked executable
equations for other functions. Positive and false-result exponentiation
regressions pass. A focused loop-pass diagnostic then replayed 147 theorems;
that diagnostic imports built predecessor theories and is not evidence of
independent full-chain acceptance.

The challenge bootstrap suffix export also completed: its compact article is
158,412,578 bytes. Export of the remaining dependency chain and independent
verification of the complete Certificate package are still unfinished.

The word compiler additionally requires mutually recursive CV equations stored
as a conjunction. The reader now extracts the checked conjuncts before selecting
code equations. Direct word compilation from those equations succeeds, and the
independent exporter regression covers conjunctive code facts. Failed executable CV requests no longer fall through to ordinary evaluation;
a missing equation now fails directly instead of causing an expensive fallback.
Closed representation conversions use the fixed ordinary evaluator instead.


### Native article replay and remaining package assembly

Focused standard-kernel checks now pass the word compiler article (94 exported
theorems), compiler configuration article (486), and full native-bytecode
article (1,955). The native check recomputes the complete register-allocation
literal conversion, checked backend compilation, and byte count. These focused
checks import built predecessor theories and do not establish independent
full-chain acceptance.

The configuration check required reconstruction of small symbolic natural-number
arithmetic and datatype-constructor equations. The reader uses HOL's arithmetic
prover and checked datatype equations, with negative regression cases. Primitive
CV arithmetic now avoids scanning the full accumulated equation library.
Representation conversions are distinguished from executable CV expressions;
this permits checked conversion of the allocation literal without allowing
missing executable equations to fall through to ordinary evaluation.

A separate concatenated replay, using only the fixed library, processed the
first eight compiler articles and reached the native article. That run used
the older 115,526,261-byte simplification article and stopped at the allocation
conversion before the representation fix. A new independent run uses the exact
first nine articles selected by the current package plan (532,903,402 bytes),
including its newer 421,769,322-byte simplification article. Its success and
full Certificate acceptance remain unverified.

The ordinary bootstrap suffix export is complete at 158,386,675 bytes. Both
bootstrap suffix articles and the final challenge Certificate article are now
available; the installation and memory dependency exports are still in progress.


### Independent replay of the selected compiler articles

All nine compiler articles selected by the current package plan now replay in
one fresh standard-kernel process: 532,903,402 article bytes and 13,399 exported
theorems. The reader loads only `initProofLibrary` and its fixed ancestors; it
introduces fresh candidate constants and checks subsequent requests from the
preceding proof data. No built baseline compiler theories are imported.

This includes the newer 421,769,322-byte simplification article, full checked
allocation and native RISC-V compilation. The process exited successfully after
679.5 seconds, with peak RSS 55,264,192 KiB (52.7 GiB). The earlier focused
native result is therefore now supported by independent compiler-chain replay.
This still does not prove acceptance of the complete Certificate package; the
installation dependency export and final Python verifier run remain required.


### Complete package assembled; full verifier run pending

All 81 dependency articles and the literal-binding article are exported. The
standard packaging tool assembled 82 articles into a 1,255,970,139-byte
`certificate.art`, alongside the 950,336-byte ROM and `{"K":"infinity"}` claim.
Each dependency article hash and the binding ROM/article hashes were checked
during assembly. The ROM SHA-256 remains
`ea0df268b27634b513e326c04308171ee8062e802e8e09e9260a2d5cca2417f6`.

The actual single Python verifier is running on this complete package with a
7,200-second timeout and a 96 GiB memory limit. It has frozen the submission,
created the operator-owned literals, and started replay. No positive
full-Certificate acceptance is claimed until that process succeeds. The latest
prepared heap passed the real CLI regression: all 904,476 native bytes were
frozen and an unrelated proof was rejected at the exact conclusion check.


### First complete Python verification rejected

The first full Python verifier run completed after 825.1 seconds and rejected
the package. Its peak child RSS was 81,663,732 KiB (77.9 GiB). The HOL log reports
`certificate replay: symbolic request requires a proved library fact`; this is
a missing replay proof, not successful Certificate acceptance. The fixed
bytecode/score snapshot and assembled proof package are retained for diagnosis.

An author-only diagnostic replay now logs candidate definitions and the exact
unresolved request. It uses the same frozen input and standard kernel, without
adding facts or changing the acceptance criterion. The production reader also
attaches the article line number to `Fail` exceptions, as it already did for
`HOL_ERR`, so subsequent rejections can be located in the concatenated package.


### Symbolic quantifier request repaired; second full run pending

The diagnostic replay reached `initStackInput`, immediately after the definition
`cv_optimized_colours`, then rejected the request
`P \/ (!x. Q x) <=> !x. P \/ Q x`. It exited after 905.4 seconds with
57,249,036 KiB peak RSS. The compiler prefix was therefore traversed again, but
full Certificate acceptance was not established.

The strict simplifier now reconstructs this request using HOL's proved
`RIGHT_FORALL_OR_THM`. An independent focused check verified its exact sequent,
empty hypotheses, and acceptable proof tags. The verifier heap was rebuilt
with matching source and heap hashes; the negative replay regression and all
25 Python verifier tests passed. A production run using the same complete
package and fresh private work directory is in progress. A passing full run
is still required before publishing the requested verification tag.


### Bootstrap parity request repaired

The second full Python run rejected after 1,579.4 seconds, with peak child RSS
82,048,496 KiB. The reader's line-number diagnostic located the unresolved
request at concatenated article line 116,435,794: `initBootstrap` local line
421,132. Replay had passed the earlier `initStackInput` quantifier request.

A focused replay using only the fixed proof library identified the request as
`!n. ODD (BIT1 n) <=> T`. Adding the proved `numeral_evenodd` theorem to the
logical simplifier lets the complete bootstrap article replay independently:
403 checked exported theorems. Existing replay regression checks, including
true and false symbolic parity cases and the preceding quantifier cases, pass.
The full package still requires a successful production run before tagging.


### Third full run: decoded configuration and parallel diagnostics

The third production verification rejected after 2,357.1 seconds with peak
child RSS 82,066,220 KiB. Its unresolved request was at concatenated article
line 131,092,019 (`initDecodedConfig`, local line 2,163,390):
`0 < n ==> ((m MOD n < n) <=> T)`.

The resolver now tries a kernel-checked Boolean normalization for small requests
before looking up the normalized statement in the checked theorem library. A
matched theorem is transported back through the conversion, then checked against
the exact original sequent. Regression tests prove the guarded remainder bound
and reject both removal of its positive-divisor premise and a false conclusion.
All strict replay component checks pass.

Focused configuration replay passed this request and exposed a further record
representation conversion at local article line 3,851,987. Work is shifting to
bounded parallel per-article diagnostics to collect remaining failures before
another complete replay. These diagnostics use built predecessor theories and
do not establish full package acceptance. The final fixed-library-only Python
verification and the reduced Lean decoder/step agreement remain outstanding.


### Parallel diagnostics and bounded theorem indexes

The first parallel batch passed `initBaselineInstalled`, `initCompiledMetadata`,
and `initBaselineAdmission` against imported checked predecessor theories. These
are diagnostic passes, not independent full-package acceptance. The final
Certificate worker was terminated by SIGTERM during indexing; the refinement
worker explicitly reported HOL heap exhaustion before article replay. Neither
is a theorem rejection. High memory use and SIGTERM are consistent with earlyoom,
but an earlyoom log confirming the termination was not available.

Fast theorem indexes now omit conclusions larger than 4,096 term nodes. All
trusted facts remain available through the existing exact/instance fallback.
The regression suite verifies lookup of a large checked fact through that
fallback and continues to reject false and premise-free requests.

The configuration conversion repair uses checked word-zero/word-one identities
and the proved lower bounds on `dimword`. This covers both residual word
conversions and conditional expressions produced by different evaluator setups.
All strict replay component regressions pass with these changes. A new article
audit snapshots the repaired sources. HOL concurrency is capped at three at the
user's request; the old suffix worker continues while two new workers audit
configuration, Certificate, refinement, and the remaining articles.

The source manifest and production heap must be refreshed after the diagnostic
repairs settle, before the next full Python verification. No successful full
verification or verification release tag is claimed.


The guarded per-article audit now passes both `initDecodedConfig` and
`initBaselineCertificate` with the bounded-index and word-conversion repairs.
The configuration pass covers the complete article that previously failed on
Boolean theorem normalization and polymorphic word conversion. The Certificate
pass checks eight exported theorems using built predecessors. Neither imports
its target theory, and the diagnostic evaluator guard rejects mapped candidate
predecessor constants. These remain local diagnostics rather than an independent
replay of the full package. The redundant queued configuration retry was
cancelled after checking that the successful audit's source hash matches the
current strict replay library.


### Semantic agreement investigation

Reduced Lean decoder/step agreement remains **unproved**. Read-only inspection
of the pinned Flapjack sources identified the following concrete proof path;
none of these observations changes the fixed challenge or establishes a new
equivalence theorem.

The reduced `Defs/Decode.lean` contains 163 Boolean conditional nodes. The
pinned reduction manifest records replacement of unsupported instruction leaves
by `UnknownInstruction`, retaining the original predicates. Its remaining
operations are bit-tuple destructuring,
Boolean negation/conjunction, typed lists and tuples, instruction constructors,
`holV2w`, and the three immediate assembly helpers. A next deliverable is a typed
decoder contract with universal equations checked separately in HOL and Lean:
`restricted_decode w = decodeContract w` and
`Decode w = decodeContractLean w`. The pinned elaborated HOL term export and
renderer can supply the tree; a Lean kernel proof against the actual pinned
definition must validate the generated expression. Structural conditional
rewriting should be tried before Boolean decision procedures. Such equations
still require the explicit word/bitvector interpretation bridge; matching
renderings or source hashes alone do not prove cross-language agreement.

The step reduction also changes memory translation: Lean
`Defs/MMU/Translate.lean` returns `(some address, state)` unconditionally and
`vmType` always returns `Mbare`. The current HOL step retains upstream memory
semantics. The relevant physical-address invariant is already part of
`riscv_targetTheory.riscv_ok_def`: the active core has `VM = 0`,
`ArchBase = 2`, no pending transfer or exception, and an aligned PC.
`initial_state_valid` proves it initially; `challengeEvaluate` checks it before
continuing an instruction step. Upstream `riscv_stepScript.sml` derives physical
`translateAddr` from the `VM = 0` premise alone. Exposing that general lemma,
proving agreement of option-valued steps under a projection to the reduced
state, and handling the fixed FFI/cache transitions are concrete next steps.
Unconditional agreement over arbitrary upstream virtual-memory states is not
the required reachable-state theorem.

A separate failure case must remain in scope: invalid instructions, `ECALL`,
and `EBREAK` can produce `NextRISCV = NONE` from a valid input state. Both target
wrappers apply an unspecified value operation to this result: HOL `THE NONE`
and Lean's opaque `holTheNone`, on different state carriers. A projection proof
must address their correspondence explicitly; equality of option-valued steps
alone does not discharge this obligation. Restricting the bridge to successful
compiler-produced steps would leave arbitrary participant bytecode uncovered.


### Further parallel replay findings

The ordinary `initBootstrapSuffixSteps` diagnostic completed naturally with
exit 0 after 2,321.0 seconds, replaying 3,074 exported theorems. The independently
scheduled challenge suffix diagnostic also passed (477.7 seconds). Neither
imports its target theory; both remain native-predecessor diagnostics rather
than full-package acceptance.

The parallel audit exposed two additional logical replay forms:
`initBootstrapCopy` request 237 (line 148825), also seen in `initPackedMemory`,
uses `LEFT_FORALL_OR_THM`; `initBaselineInitial` request 336 (line 331211)
uses the reverse direction of `FORALL_AND_THM`. The early logical simplifier
now includes these checked library rules. Exact-sequent positive cases and
false variants were added to `replayChecksTheory`; the regression completed
successfully in 8 seconds (`/tmp/hol-init-focused-regression.log`). Focused
article retries are still running. The refinement computation failure remains
under investigation; no untested evaluator setup change has been made.


The focused retries passed `initBootstrapCopy` (14.7 seconds),
`initBaselineInitial` (78.2 seconds), and `initPackedMemory` (16.7 seconds).
The refinement retry still rejected request 255, but the new residual diagnostic
showed concrete word arithmetic and `dimindex (:64)` left unevaluated.
An isolated standard-kernel test from the saved verifier heap failed before
loading `wordsLib` and succeeded afterward, with a false arithmetic equality
rejected (`/tmp/hol-init-word-setup.log`, `WORD_SETUP_CHECK_OK`). Operator heap
preparation now explicitly loads `wordsLib`; author diagnostics mirror that
setup when using an older heap. A new concrete-word regression and full
refinement-article retry are running. The shared saved heap still awaits refresh after the active audit workers
finish. The operator trust manifest has been refreshed for the reviewed
`strictReplayLib.sml` and `prepareHeap.sml` changes and passes `check_trusted`.


With the explicit `wordsLib` setup, the complete `initBaselineRefinement`
article passed its guarded native-predecessor diagnostic in 142.0 seconds,
exporting 570 theorems (`audit-word-v4/initBaselineRefinement/replay.log`).
The concrete-word regression also passed in 9 seconds. All four failures
observed so far in the ongoing parallel batch have successful focused retries;
the batch and full independent Python verification remain unfinished.


The 54-module parallel diagnostic batch has finished. Its final failure,
`initBaselineChallengeExecution` request 32 (line 38847), was another use of
`FORALL_AND_THM` against the older immutable reader snapshot. The repaired
focused retry passed in 85.8 seconds (`audit-final-v5`). Combining the original
batch with the five repaired module results leaves all 54 modules passed.
This remains diagnostic coverage with checked native predecessor imports;
it does not establish independent full Certificate acceptance. The operator
heap rebuild and boundary/CLI gates are now running before full verifier v4.


Verifier v4 preparation completed with the current trusted manifest and explicit
word evaluator setup. All 25 Python boundary tests passed, as did the real CLI
negative test with 904,476 frozen ROM bytes and exact-conclusion rejection.
The full assembled submission is now running through `verifier/verify.py
--local .submission-baseline-full --work .verify-baseline-full-v4 --timeout
10800 --memory-gib 96 --progress`. Its result is still pending; a one-shot Herdr
waker tracks the pipeline and will report completion to the verified session.


### Full verifier v4 rejection without a HOL diagnostic

The full Python verifier returned rejection after 5,659.224 seconds, with
82,149,108 KiB maximum child RSS. The 493-byte replay log ends after creation
of `candidateCertificate`; it contains no proof-rejection exception. The old
Python wrapper discarded the child return code, so this evidence does not
distinguish a signal termination from another nonzero exit. System earlyoom
and kernel logs are inaccessible to this account. The operator subsequently
checked the earlyoom log and confirmed SIGTERM against HOL PID 1409261.
This run was therefore externally terminated; it does not establish a proof
replay error. No verification release was committed or tagged.

The wrapper now preserves `replay-process.json` and distinguishes signals,
nonzero exits, timeouts, and missing/incorrect completion markers. Six new
mocked-process regressions include rejection of a killed or unsuccessful child
even when an exact marker exists. All 31 boundary tests pass. Full verifier v5
will retain external memory/input-position samples and use an 80 GiB address
space limit (60 GiB Poly/ML heap) to leave more host memory headroom.


The operator requested a higher memory limit after freeing host RAM. V5 had
passed heap preparation, all 31 boundary tests, and the real CLI negative test;
its live HOL replay was deliberately stopped with SIGTERM for this requested
restart. This is recorded separately from the earlyoom termination of v4.
V6 is now running with `--memory-gib 112` (84 GiB Poly/ML heap), the same tested
heap and unchanged trusted sources, a fresh `.verify-baseline-full-v6` workspace,
process telemetry, and a rearmed Herdr waker. The operator requested keeping
that limit for retries and publishing a commit/tag only after full acceptance.


### Full independent verification passed (v6)

On 2026-10-08, the complete assembled baseline passed the production Python
verifier with exit 0 and JSON status `verified`, score `infinity`, and the exact
950,336-byte frozen ROM. HOL returned 0, did not time out, and wrote the exact
`VERIFIED\n` marker. The original and frozen ROM/proof hashes and all recorded
trusted source hashes were independently checked after completion.

The full run took 8,700.966 seconds (about 2 hours 25 minutes), with maximum
child RSS 94,926,156 KiB (90.53 GiB). It used a 10,800-second timeout, 112 GiB
address-space limit, and 84 GiB Poly/ML heap. The saved operator heap, all 31
boundary tests, and real CLI negative test had passed before this unchanged-
source run. No native baseline predecessor theories were imported for acceptance.

See [the retained verification report](../artifacts/baseline/verification.json)
for exact hashes, command, process status, limits, and resource measurements.
The proof SHA-256 is
`aad8e2e6ec4b59cf36e922c8fdcbaaa0bf89c4c3eff91bc97aef5b3f6e0cd98b`.
This closes full certificate replay, not the separate reduced Lean decoder/step
agreement obligation, which remains explicitly outstanding.


### PR25 guest input bound: fresh full verifier passed (2026-10-09)

Imported init-e PR25 at `afa0071e8611d5b1b18d4033cc350e5072d4a0dd`. The guest
rejects unsigned input lengths above 134,217,712 bytes with trap 8 before
allocation or payload access. Kernel regression checks execute the actual imported
guest on synthetic oversized headers and valid boundary lengths. No input-length
premise was added to Certificate.

Fresh native compilation is 904,616 bytes with 4,614 bitmap words. Native entry
is `0x80000f60`, preserving the fixed code-buffer end `0x800ddd08`; two bitmap-end
startup headers advance to `0xa0029048`. This difference from the pinned upstream
startup headers is documented in `provenance.json`. Stack ranks remain unchanged.

The normal HOL build passed, including `baseline_certificate`. All 81 fresh
author exports passed; three tracing exports required sequential 24 GiB retries.
The fresh literal binding, package, operator heap, 31 boundary tests, and real
CLI negative test passed. The production full verifier then accepted the new
950,344-byte ROM with Infinity score: Python and HOL exit 0, no signal or timeout,
and the exact `VERIFIED\n` marker. Run PR25 v4 took 8,727 seconds and peaked at
94,934,632 KiB (90.54 GiB) child RSS, with 112 GiB address-space, 84 GiB heap,
and 10,800-second timeout limits. Artifact and proof hashes are recorded in
`artifacts/baseline/verification.json`. Earlier entries above describe historical
artifacts and runs. Reduced Lean decoder/step agreement remains explicitly unproved.
