#!/usr/bin/env python3
"""Real Linux isolation regression for --hide (requires working bwrap)."""
from pathlib import Path
import subprocess
import sys
import tempfile
import verify


def main():
    with tempfile.TemporaryDirectory(prefix='hol-init-hide-test-') as temporary:
        base = Path(temporary)
        hidden = base/'hidden directory'
        hidden.mkdir()
        (hidden/'secret').write_text('must be invisible')
        hidden_file = base/'hidden file'
        hidden_file.write_text('must be invisible')
        visible = base/'visible'
        visible.write_text('read only')
        work = base/'work'
        work.mkdir(mode=0o700)
        probe = """
from pathlib import Path
import sys
hidden, hidden_file, work, visible = map(Path, sys.argv[1:])
assert list(hidden.iterdir()) == []
try:
    assert hidden_file.read_bytes() == b''
except PermissionError:
    pass
assert visible.read_text() == 'read only'
try:
    visible.write_text('forbidden')
except OSError:
    pass
else:
    raise AssertionError('host filesystem was writable')
(work/'result').write_text('isolated')
"""
        command = verify.hidden_replay_command(
            [sys.executable, '-c', probe, str(hidden), str(hidden_file), str(work), str(visible)],
            [hidden, hidden_file], work, [sys.executable])
        subprocess.run(command, check=True, cwd=work)
        assert (work/'result').read_text() == 'isolated'
        assert (hidden/'secret').read_text() == 'must be invisible'
        assert hidden_file.read_text() == 'must be invisible'
        assert visible.read_text() == 'read only'
    print('PASS: file/directory masks, read-only host, and writable private workspace')


if __name__ == '__main__':
    main()
