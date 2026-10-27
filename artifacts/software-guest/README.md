# Independently verified software guest

The public source-only verifier accepted the exact fixed HOL Certificate for
[rom.bin](rom.bin), with score Infinity, on **2026-10-26**. The ROM has 1,028,080
bytes and SHA-256 `44b6a6b828293a54cf2e8698a6a0af6a0d08b4ea825f6504547996c31969d04b`.
It matches both pinned reference ROMs. The compiled guest uses software EVM
precompiles and has only terminal `halt`/`trap` external calls.

[verification.json](verification.json) records the fresh public CLI acceptance,
exact hashes, resource limits, gates, operator heap and strict process result.
The [source manifest](source-submission-manifest.json) identifies every frozen
participant file. The 145-file envelope is 3,045,749 bytes, or 693,478 bytes zipped.
The generated 4,446,682,307-byte article stays on the operator side; its whole-ROM
CV translation is retained and the article cap is 8 GiB.

Strict replay took 13,127.7 seconds, returned 0 without signal or timeout, and
wrote exactly `VERIFIED\n`. The public CLI took 10 hours 52 minutes 57 seconds
and reached 94,629,628 KiB maximum RSS. Its limits were 64 GiB author address
space, 24 GiB build/bind heaps, 40 GiB export heap, and 112 GiB strict replay
address space with an 84 GiB heap. Logs are retained in [verification-logs/](verification-logs/).

The native image has 979,140 bytes; the 4,603 bitmap words and output configuration
are published one directory above. Native entry is `0x80001070`, native end
`0x800f0134`, and the fixed code buffer has 3,788 bytes. The checked stack bound
is 7,480 words. Startup memory and host semantics follow original init-e; the
pinned Rocq host/layout differences are documented in
[the reference comparison](../../source/software-update-reference.json).

The other JSON files in this directory preserve individual earlier build checks;
their pending scopes describe those checkpoints. The final verification record
above is the acceptance evidence for this revision. Tag
`r20261026-verifier-passed` identifies the release commit. Formal reduced Lean
decoder/step correspondence remains outstanding.
