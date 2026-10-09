# Participant submissions (untrusted)

Put a candidate in its own directory outside the trusted challenge tree:

- `rom.bin`: arbitrary submitted bytes, at most 128 MiB.
- `claim.json`: exactly `{"K":123}` or `{"K":"infinity"}`.
- `certificate.art`: an OpenTheory article proving the exact fixed certificate.

The operator runs `python3 verifier/verify.py --local /path/to/candidate`
from the trusted checkout. This prepares a missing or stale operator heap and
verifies by default. The bytes and score are frozen and sanitized
into literal HOL definitions. Acceptance requires a closed proof of precisely
`initChallenge.Certificate submittedBytes submittedScore`.

The fixed challenge is not participant-editable. Candidate code is never added
to the trusted HOL load path. Dispatch/layout metadata is an admitted existential
witness in the proof, not a replacement challenge configuration.

HOL proves the full baseline Certificate, including compilation, bootstrap,
installation, and source refinement. Its three-file article package has passed
the full Python verifier; see the [verification record](../artifacts/baseline/verification.json).
The successful run used `--timeout 10800 --memory-gib 112`. Agreement with the
pinned reduced Lean decoder and machine step remains a separate unproved
obligation. See [verifier documentation](../verifier/README.md).
