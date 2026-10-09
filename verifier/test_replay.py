#!/usr/bin/env python3
"""Optional real-HOL regression; prepare the fixed verifier heap first."""
from pathlib import Path
from unittest.mock import patch
import verify

# A valid article requesting the fixed HOL truth theorem, not Certificate.
TRUTH_ARTICLE = b'''nil
"HOL4.bool.T"
const
"HOL4.min.bool"
typeOp
nil
opType
constTerm
0
def
axiom
nil
0
ref
thm
'''

def main():
    verify.check_trusted()
    rom = (verify.ROOT/'artifacts/native-riscv.bin').read_bytes()
    frozen = verify.FrozenSubmission('infinity', rom, TRUTH_ARTICLE)
    diagnostic = []
    original = verify.subprocess.run
    def record(*args, **kwargs):
        result = original(*args, **kwargs)
        kwargs['stdout'].flush()
        diagnostic.append(Path(kwargs['stdout'].name).read_text())
        return result
    with patch.object(verify.subprocess, 'run', record):
        try:
            verify.replay_frozen(frozen)
        except verify.Rejected:
            # A resource failure or broken literal loader must not count as
            # successful testing of the exact-statement acceptance boundary.
            assert diagnostic and 'exact fixed certificate conclusion was not proved' in diagnostic[0], diagnostic
        else:
            raise AssertionError('Unrelated theorem was accepted as Certificate')
    print(f'PASS: {len(rom)} literal bytes loaded; unrelated proof rejected at the exact conclusion check')

if __name__ == '__main__':
    main()
