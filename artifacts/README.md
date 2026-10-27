# Checked software-guest artifacts

`native-riscv.bin` contains the 979,140 native bytes computed by HOL4 from the
fixed software guest AST. `bitmaps.txt` contains 4,603 decimal word64 bitmap
values; `backend.conf` is CakeML's encoded output configuration. File hashes
and dependency pins are in [manifest.json](manifest.json).

The theorem `initArtifacts.exact_guest_riscv_compilation` checks the full
Pancake compilation result. Reproduce the native artifacts with:

```sh
python3 tools/build.py --hol /path/to/tested/HOL initArtifactsTheory.uo
cmp .build/compiled.bin artifacts/native-riscv.bin
cmp .build/bitmaps.txt artifacts/bitmaps.txt
cmp .build/backend.conf artifacts/backend.conf
```

[software-guest/rom.bin](software-guest/rom.bin) is the complete 1,028,080-byte
ROM, including bootstrap, padding, native image and initialization data. The
full public source-only verifier accepted its fixed Certificate with score
Infinity on 2026-10-26. See [current evidence](software-guest/README.md) and
[verification.json](software-guest/verification.json). The ROM and native bytes
match both pinned init-e/Rocq references. External SHA-256 hashes are integrity
checks; they are not HOL cryptographic proofs.

Raw native artifacts alone omit bootstrap and initialization. Participant
submissions use the [source envelope](../submission/README.md). The
[baseline/](baseline/README.md) directory preserves previous-guest evidence.
Formal reduced Lean decoder/step agreement remains outstanding.
