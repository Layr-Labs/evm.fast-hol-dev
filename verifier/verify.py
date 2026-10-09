#!/usr/bin/env python3
"""Trusted, fail-closed entry point for untrusted hol-init-e submissions.
Preflight freezes literal inputs. --replay uses an operator-built HOL heap
to require the exact fixed Certificate, without executing participant ML.
"""
from __future__ import annotations
import argparse
from contextlib import contextmanager
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import signal
import time
import resource
import shutil
import tempfile
import sys

ROOT = Path(__file__).resolve().parents[1]
ROM_LIMIT = 128 * 1024 * 1024
PROOF_LIMIT = 2 * 1024 * 1024 * 1024
FILES = {'rom.bin', 'claim.json', 'certificate.art'}

class Rejected(ValueError): pass
class ReplayUnavailable(RuntimeError): pass

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result: raise Rejected('duplicate JSON key: '+key)
        result[key] = value
    return result

def inspect_file(directory_fd, name, limit, collect=False):
    """Open once, never follow symlinks, bound reads even if a file grows."""
    fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=directory_fd)
    with os.fdopen(fd, 'rb') as stream:
        info = os.fstat(stream.fileno())
        if not stat.S_ISREG(info.st_mode): raise Rejected(name+' must be a regular file')
        if info.st_size > limit: raise Rejected(name+' exceeds size limit')
        digest, size, chunks = hashlib.sha256(), 0, []
        while chunk := stream.read(min(1024*1024, limit-size+1)):
            size += len(chunk)
            if size > limit: raise Rejected(name+' exceeds size limit')
            digest.update(chunk)
            if collect: chunks.append(chunk)
        return size, digest.hexdigest(), b''.join(chunks)

@dataclass(frozen=True)
class FrozenSubmission:
    """One bounded read of candidate data; later phases never reopen its paths."""
    score: int | str
    rom: bytes
    proof: bytes

    def __post_init__(self):
        if self.score != 'infinity' and not (type(self.score) is int and self.score >= 0):
            raise Rejected('invalid frozen score')
        if type(self.rom) is not bytes or type(self.proof) is not bytes:
            raise Rejected('frozen submission must contain immutable bytes')

    def report(self):
        return {'K': self.score, 'rom_bytes': len(self.rom),
                'rom_sha256': hashlib.sha256(self.rom).hexdigest(),
                'proof_sha256': hashlib.sha256(self.proof).hexdigest()}

    def write_literals(self, stream):
        """Emit only trusted syntax and decimal integers, never candidate text.

        This module supplies the inputs to the fixed challenge. The eventual
        replay checker must require its exact closed Certificate conclusion;
        generating literals alone does not verify a certificate.
        """
        stream.write('Theory submissionLiterals\nAncestors initParams\n\n')
        stream.write('Definition submittedBytes_def:\n  submittedBytes : word8 list = [')
        for offset in range(0, len(self.rom), 1024):
            if offset: stream.write(';')
            stream.write(';'.join(str(byte)+'w' for byte in self.rom[offset:offset+1024]))
            stream.write('\n')
        stream.write(']\nEnd\n\nDefinition submittedScore_def:\n')
        literal = 'initParams$Infinity' if self.score == 'infinity' else (
            'initParams$Finite '+str(self.score))
        stream.write('  submittedScore = '+literal+'\nEnd\n')


def freeze(candidate):
    fd = os.open(candidate, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        names = set()
        with os.scandir(fd) as entries:
            for entry in entries:
                if entry.name not in FILES or len(names) >= len(FILES):
                    raise Rejected('unexpected submission entry')
                names.add(entry.name)
        if names != FILES:
            raise Rejected('submission must contain exactly rom.bin, claim.json, certificate.art')
        _, _, claim_bytes = inspect_file(fd, 'claim.json', 65536, True)
        claim = json.loads(claim_bytes, object_pairs_hook=unique_object)
        if not isinstance(claim, dict) or set(claim) != {'K'}:
            raise Rejected('claim.json must have exactly the K field')
        score = claim['K']
        if score != 'infinity' and not (type(score) is int and score >= 0):
            raise Rejected('K must be a nonnegative integer or "infinity"')
        size, digest, rom = inspect_file(fd, 'rom.bin', ROM_LIMIT, True)
        proof_size, proof_hash, proof = inspect_file(fd, 'certificate.art', PROOF_LIMIT, True)
        if not proof_size: raise Rejected('certificate.art is empty')
        return FrozenSubmission(score, rom, proof)
    finally:
        os.close(fd)

def preflight(candidate):
    return freeze(candidate).report()


def prepare_snapshot(frozen, destination):
    """Create a fresh operator-owned replay input directory from frozen data."""
    destination.mkdir(mode=0o700, parents=False, exist_ok=False)
    for name, contents in [('rom.bin', frozen.rom), ('certificate.art', frozen.proof)]:
        with (destination/name).open('xb') as stream:
            stream.write(contents)
    with (destination/'claim.json').open('x') as stream:
        json.dump({'K': frozen.score}, stream, separators=(',', ':'))
        stream.write('\n')
    with (destination/'submissionLiteralsScript.sml').open('x') as stream:
        frozen.write_literals(stream)


def check_trusted(root=None):
    root = ROOT if root is None else Path(root)
    manifest = json.loads((root/'verifier/trusted-files.json').read_text())
    for relative, expected in manifest.items():
        path = root/relative
        if path.is_symlink() or not path.is_file():
            raise Rejected('missing or redirected trusted file: '+relative)
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise Rejected('modified trusted file: '+relative)
    for directory in ['challenge', 'source']:
        expected_files = {name for name in manifest if name.startswith(directory+'/')}
        observed = set()
        for path in (root/directory).rglob('*'):
            if path.is_symlink(): raise Rejected('redirected trusted path: '+str(path))
            if path.is_file(): observed.add(path.relative_to(root).as_posix())
        if observed != expected_files:
            raise Rejected('unexpected trusted file set in '+directory)
    pin = json.loads((root/'provenance.json').read_text())['cakeml']
    actual = subprocess.check_output(['git', '-C', str(root/'cakeml'), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != pin: raise Rejected('CakeML submodule pin differs')
    dirty = subprocess.check_output(['git', '-C', str(root/'cakeml'), 'status',
                                    '--porcelain', '--untracked-files=all'], text=True)
    if dirty: raise Rejected('CakeML submodule has local changes')

def file_digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()



@contextmanager
def replay_workspace(build, requested=None):
    if requested is None:
        with tempfile.TemporaryDirectory(prefix='replay-', dir=build) as temporary:
            yield Path(temporary)
    else:
        work = Path(requested).absolute()
        work.mkdir(mode=0o700, parents=True, exist_ok=False)
        yield work.resolve()


def hidden_replay_command(command, hidden, work, protected):
    """Mask operator-selected paths in the replay process; never ignore --hide."""
    if not hidden:
        return command
    bwrap = shutil.which('bwrap')
    if bwrap is None:
        raise Rejected('--hide requires bubblewrap (bwrap)')
    masks = sorted({Path(path).resolve(strict=True) for path in hidden},
                   key=lambda path: len(path.parts))
    required = [Path(path).resolve() for path in [work, *protected]]
    selected = []
    for path in masks:
        if any(path == needed or path in needed.parents for needed in required):
            raise Rejected('--hide overlaps a required verifier path: '+str(path))
        if not path.is_dir() and not path.is_file():
            raise Rejected('--hide requires a regular file or directory: '+str(path))
        if any(parent == path or parent in path.parents for parent in selected):
            continue
        selected.append(path)
    isolated = [bwrap, '--die-with-parent', '--new-session', '--unshare-net',
                '--unshare-pid', '--ro-bind', '/', '/', '--proc', '/proc',
                '--dev', '/dev', '--bind', str(work), str(work)]
    for path in selected:
        isolated += ['--tmpfs', str(path)] if path.is_dir() else [
            '--ro-bind', '/dev/null', str(path)]
    return isolated + ['--', *command]


def replay_frozen(frozen, timeout=600, memory_gib=32, *, trusted=None, work=None, hide=()):
    """Replay only frozen data in a fresh process with the fixed checker."""
    root = ROOT if trusted is None else Path(trusted).resolve()
    build = root/'.build'
    heap, metadata = build/'verifier.heap', build/'verifier.json'
    if not heap.is_file() or not metadata.is_file():
        raise ReplayUnavailable('Run tools/prepare_verifier.py with the pinned HOL checkout first.')
    info = json.loads(metadata.read_text())
    if set(info) != {'hol','hol_revision','heap_sha256','manifest_sha256'}:
        raise Rejected('invalid verifier heap metadata')
    pin = json.loads((root/'provenance.json').read_text())['tested_hol']
    if info['hol_revision'] != pin or info['manifest_sha256'] != file_digest(root/'verifier/trusted-files.json'):
        raise ReplayUnavailable('The verifier heap is stale; rebuild it against the fixed manifest.')
    if info['heap_sha256'] != file_digest(heap):
        raise Rejected('modified verifier heap')
    executable = Path(info['hol'])/'bin/hol'
    def limits():
        resource.setrlimit(resource.RLIMIT_CPU, (timeout, timeout+1))
        memory = memory_gib*1024**3
        resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
        resource.setrlimit(resource.RLIMIT_FSIZE, (256*1024**2, 256*1024**2))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    with replay_workspace(build, work) as work:
        snapshot = work/'input'
        prepare_snapshot(frozen, snapshot)
        (snapshot/'score.txt').write_text(str(frozen.score), encoding='ascii')
        environment = os.environ.copy()
        environment['HOL_INIT_E_SNAPSHOT'] = str(snapshot)
        started = time.monotonic()
        def record_process(returncode=None, *, timed_out=False):
            number = -returncode if returncode is not None and returncode < 0 else None
            try:
                name = signal.Signals(number).name if number is not None else None
            except ValueError:
                name = 'signal '+str(number)
            report = {'returncode': returncode, 'signal': name,
                      'signal_number': number, 'timed_out': timed_out,
                      'wall_seconds': time.monotonic()-started}
            (work/'replay-process.json').write_text(json.dumps(report, indent=2)+'\n')
            return report
        with (work/'replay.log').open('wb') as log:
            try:
                command = hidden_replay_command(
                    [str(executable), '--maxheap', str(memory_gib*768), '--gcthreads=1',
                     '--holstate='+str(heap), str(root/'verifier/check.sml')],
                    hide, work, [heap, root/'verifier', executable.parent.parent])
                process = subprocess.run(command, cwd=work, env=environment,
                    stdout=log, stderr=subprocess.STDOUT, timeout=timeout,
                    preexec_fn=limits)
            except subprocess.TimeoutExpired as exc:
                # subprocess.run kills and waits for the child on timeout, but
                # TimeoutExpired does not expose that child's final returncode.
                record_process(timed_out=True)
                raise Rejected('proof replay exceeded the time limit') from exc
        report = record_process(process.returncode)
        if process.returncode < 0:
            raise Rejected('HOL replay process terminated by '+report['signal']+
                           ' ('+str(report['signal_number'])+')')
        if process.returncode != 0:
            raise Rejected('HOL replay process exited with status '+str(process.returncode))
        marker = snapshot/'verified'
        if not marker.is_file():
            raise Rejected('HOL replay did not prove the exact fixed Certificate: completion marker missing')
        if marker.read_bytes() != b'VERIFIED\n':
            raise Rejected('HOL replay did not prove the exact fixed Certificate: incorrect completion marker')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('candidate', type=Path, nargs='?', help='legacy positional submission directory')
    parser.add_argument('--local', type=Path, help='submission directory; verify by default, as in init-e')
    parser.add_argument('--trusted', type=Path, help='operator-owned trusted checkout (defaults to this checkout)')
    parser.add_argument('--work', type=Path, help='fresh directory to retain the frozen inputs and replay log')
    parser.add_argument('--hide', type=Path, action='append', default=[], help='mask a host file or directory during replay (repeatable; requires bwrap)')
    parser.add_argument('--structural-only', action='store_true', help='check the envelope without proving Certificate')
    parser.add_argument('--progress', action='store_true', help='report verification stages to stderr')
    parser.add_argument('--hol', type=Path, help='operator HOL checkout for automatic verifier preparation')
    parser.add_argument('--prepare', type=Path, metavar='NEW_DIRECTORY',
        help='write a sanitized snapshot for inspection; this does not verify a proof')
    parser.add_argument('--replay', action='store_true',
        help='check the exact HOL Certificate using the prepared fixed verifier heap')
    parser.add_argument('--timeout', type=int, default=600, help='replay wall/CPU limit in seconds')
    parser.add_argument('--memory-gib', type=int, default=32, help='replay address-space limit')
    args = parser.parse_args(argv)
    if (args.candidate is None) == (args.local is None):
        parser.error('supply exactly one submission directory, using --local or a positional argument')
    if args.structural_only and args.replay:
        parser.error('--structural-only cannot be combined with --replay')
    candidate = args.local if args.local is not None else args.candidate
    replay = (args.local is not None or args.replay) and not args.structural_only
    def progress(message):
        if args.progress: print(message, file=sys.stderr, flush=True)
    if args.timeout < 1 or args.memory_gib < 1:
        parser.error('replay resource limits must be positive')
    try:
        progress("Checking the fixed challenge and freezing submission literals")
        root = args.trusted.resolve() if args.trusted is not None else ROOT
        check_trusted(root)
        if args.work is not None and (args.work.exists() or args.work.is_symlink()):
            raise Rejected('work directory must not exist')
        frozen = freeze(candidate)
        report = frozen.report()
        if args.prepare is not None:
            prepare_snapshot(frozen, args.prepare)
        if args.structural_only:
            if args.work is not None:
                with replay_workspace(root/'.build', args.work) as work:
                    prepare_snapshot(frozen, work/'input')
            print(json.dumps({'status':'structural_pass', **report}))
            return 0
        if replay:
            progress('Replaying the exact fixed Certificate')
            try:
                replay_frozen(frozen, args.timeout, args.memory_gib,
                              trusted=root, work=args.work, hide=args.hide)
            except ReplayUnavailable:
                # Only operator-owned tools run here. The candidate was already
                # frozen and never participates in preparing this trusted heap.
                stamp = root/'.build/hol-path.txt'
                hol = args.hol or os.environ.get('HOLDIR') or (
                    stamp.read_text().strip() if stamp.is_file() else root.parent/'HOL')
                progress('Preparing the fixed HOL verifier')
                subprocess.run([sys.executable, str(root/'tools/prepare_verifier.py'),
                    '--hol', str(hol)], check=True,
                    stdout=sys.stderr if args.progress else subprocess.DEVNULL,
                    stderr=sys.stderr if args.progress else subprocess.DEVNULL)
                progress('Replaying the frozen submission with the prepared verifier')
                replay_frozen(frozen, args.timeout, args.memory_gib,
                              trusted=root, work=args.work, hide=args.hide)
            print(json.dumps({'status':'verified', **report}))
            return 0
    except ReplayUnavailable as exc:
        print(json.dumps({'status':'incomplete', 'reason':str(exc)}))
        return 2
    except (Rejected, OSError, ValueError, RecursionError, subprocess.CalledProcessError) as exc:
        print(json.dumps({'status':'rejected', 'reason':str(exc)}))
        return 1
    print(json.dumps({'status':'incomplete', 'preflight':'passed', **report,
        'reason':'Preflight only: use --replay with an operator-built verifier heap to check the fixed Certificate.'}))
    return 2

if __name__ == '__main__': raise SystemExit(main())
