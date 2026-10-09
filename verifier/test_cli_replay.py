#!/usr/bin/env python3
"""Real single-script regression with the original flags and full-size literals."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import verify
from test_replay import TRUTH_ARTICLE


def main():
    with tempfile.TemporaryDirectory(prefix='hol-init-cli-test-') as temporary:
        base = Path(temporary)
        candidate = base/'candidate'
        candidate.mkdir()
        rom = (verify.ROOT/'artifacts/native-riscv.bin').read_bytes()
        (candidate/'rom.bin').write_bytes(rom)
        (candidate/'claim.json').write_text('{"K":"infinity"}')
        (candidate/'certificate.art').write_bytes(TRUTH_ARTICLE)
        private = base/'private'
        private.mkdir()
        (private/'secret').write_text('not an input')
        work = base/'retained run'
        result = subprocess.run([sys.executable, str(verify.ROOT/'verifier/verify.py'),
            '--local', str(candidate), '--trusted', str(verify.ROOT),
            '--work', str(work), '--hide', str(candidate), '--hide', str(private),
            '--progress'], capture_output=True, text=True, timeout=900)
        assert result.returncode == 1, (result.stdout, result.stderr)
        assert json.loads(result.stdout)['status'] == 'rejected', result.stdout
        assert (work/'input/rom.bin').read_bytes() == rom
        assert 'exact fixed certificate conclusion was not proved' in (work/'replay.log').read_text()
        assert work.stat().st_mode & 0o777 == 0o700
    print(f'PASS: original CLI flags; {len(rom)} frozen bytes; exact-conclusion rejection')


if __name__ == '__main__':
    main()
