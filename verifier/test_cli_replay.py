#!/usr/bin/env python3
"""The public CLI accepts the source envelope only, never OpenTheory input."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import verify


def main():
    with tempfile.TemporaryDirectory(prefix='hol-init-cli-test-') as temporary:
        base = Path(temporary)
        candidate = base/'candidate'
        candidate.mkdir()
        rom = (verify.ROOT/'artifacts/native-riscv.bin').read_bytes()
        (candidate/'rom.bin').write_bytes(rom)
        (candidate/'claim.json').write_text('{"K":"infinity"}')
        (candidate/'certificate.art').write_bytes(b'OpenTheory is an internal generated artifact')
        work = base/'retained run'
        result = subprocess.run([sys.executable, str(verify.ROOT/'verifier/verify.py'),
            str(candidate), '--hol', str(verify.ROOT.parent/'HOL'),
            '--author-hol', str(verify.ROOT.parent/'HOL-export'),
            '--work', str(work)], capture_output=True, text=True, timeout=30)
        assert result.returncode == 1, (result.stdout, result.stderr)
        assert json.loads(result.stdout)['status'] == 'rejected', result.stdout
        assert 'experiments/' in json.loads(result.stdout)['reason']
        assert work.stat().st_mode & 0o777 == 0o700
    print(f'PASS: article-only envelope rejected; {len(rom)} ROM bytes were not replayed')


if __name__ == '__main__':
    main()
