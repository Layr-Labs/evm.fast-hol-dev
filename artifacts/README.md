# Checked native compiler artifacts

`native-riscv.bin` contains the 904,616 native bytes computed by HOL4 from the
fixed guest AST. `bitmaps.txt` contains 4,614 decimal word64 bitmap values;
`backend.conf` is CakeML's encoded output configuration. File hashes and pins
are in `manifest.json`.

The checked theorem `initArtifacts.exact_guest_riscv_compilation` states that
the top-level Pancake compiler returns the named bytes, bitmaps and decoded
configuration. Reproduce with:

```sh
python3 tools/build.py --hol /path/to/tested/HOL initArtifactsTheory.uo
cmp .build/compiled.bin artifacts/native-riscv.bin
cmp .build/bitmaps.txt artifacts/bitmaps.txt
cmp .build/backend.conf artifacts/backend.conf
```

The files are exported from the checked CV results. Their SHA-256 hashes are
external integrity checks, not HOL cryptographic proofs.

**This is not a challenge submission.** The raw native code omits startup and initialization data. The
[bootstrapped baseline](baseline/README.md) includes the PR25 input-bound guest update and has a proved HOL Certificate with
score Infinity and a replayable article package accepted by the full Python
verifier. See the [verification record](baseline/verification.json). No Certificate
is claimed for the raw native image alone.
