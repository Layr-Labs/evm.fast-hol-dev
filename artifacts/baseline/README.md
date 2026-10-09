# Baseline ROM — Certificate proved in HOL

The 950,344-byte ROM combines the 208-byte bootstrap, padding to native entry
`0x80000f60`, the checked 904,616-byte native compiler output, and initialization
data at `0x800df000`. The native image ends exactly at `0x800ddd08`, as required
by the fixed source-memory code-buffer header. The bootstrap copies the data
into zero-initialized RAM, sets the heap/stack pointers and source headers, and
jumps to native code.

`initBootstrap` checks encoding, assembler instruction admissibility, and
numeric layout. `initBaselineRom` proves the ROM length, exact native/data
placement, and `native_ends_at_fixed_buffer`. `initBaselineAdmission` proves
admission of the resulting submission. These theories passed clean builds for
this placement. Execution-proof details and remaining obligations are tracked
in `experiments/RESULTS.md`.

`initBaselineCertificate.baseline_certificate` proves the fixed challenge
statement `Certificate baselineRom Infinity`. Its clean build checks the full
compiler, bootstrap, installation, source refinement, and concrete stack bound.
The exported ROM matches the checked construction byte for byte.

The full Python verifier accepted the replayable article package with exit 0
and `status: verified`. The [verification record](verification.json) includes the
frozen ROM/proof hashes and Infinity score. Run PR25 v4 took 8,727 seconds and peaked
at 90.54 GiB child RSS, using `--timeout 10800 --memory-gib 112`.

This directory remains an artifact archive, not the three-file submission
package. See [author proof export](../../verifier/README.md#author-proof-export)
for the export, literal-binding, and packaging commands. Agreement with the
pinned reduced Lean decoder and machine step remains unproved.

Build the Certificate with:

```sh
python3 tools/build.py --hol /path/to/tested/HOL initBaselineCertificateTheory
```

The construction target is `initBaselineRomTheory`. Exported files are named
`bootstrap.bin` and `baseline-rom.bin` in the build directory. Integrity hashes
are in `manifest.json`; these hashes are external checks, not HOL theorems.
