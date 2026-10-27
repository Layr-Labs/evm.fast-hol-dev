#!/usr/bin/env python3
"""Build and strictly verify a source-based HOL4 init-e submission.

Participant SML is run only in an isolated author-side HOL process. Its
generated OpenTheory article is then frozen and checked by verify_article.py's
fresh, operator-owned kernel replay. This is the only participant submission
path; article files are internal build output, not an accepted envelope.
"""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import resource
import shutil
import stat
import subprocess
import sys
import tempfile

from verify import check_trusted, main as strict_article_replay, unique_object

ROOT = Path(__file__).resolve().parents[1]
MAX_SOURCE_FILE = 16 * 1024 * 1024
MAX_SOURCE_TOTAL = 64 * 1024 * 1024


def read_regular(directory_fd, name, limit):
    fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                 dir_fd=directory_fd)
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode) or info.st_size > limit:
            raise ValueError(name+' must be a bounded regular file')
        chunks, total = [], 0
        while True:
            chunk = os.read(fd, min(1024 * 1024, limit - total + 1))
            if not chunk:
                break
            total += len(chunk)
            if total > limit:
                raise ValueError(name+' exceeds size limit')
            chunks.append(chunk)
        return b''.join(chunks)
    finally:
        os.close(fd)


def frozen_source_submission(candidate: Path, destination: Path):
    fd = os.open(candidate, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        entries = {entry.name: entry for entry in os.scandir(fd)}
        if set(entries) != {'rom.bin', 'claim.json', 'experiments'}:
            raise ValueError('source submission must contain exactly rom.bin, claim.json, experiments/')
        if not entries['experiments'].is_dir(follow_symlinks=False):
            raise ValueError('experiments must be a regular directory')
        rom = read_regular(fd, 'rom.bin', 128 * 1024 * 1024)
        claim_bytes = read_regular(fd, 'claim.json', 65536)
        claim = json.loads(claim_bytes, object_pairs_hook=unique_object)
        if not isinstance(claim, dict) or set(claim) != {'K'}:
            raise ValueError('claim.json must have exactly the K field')
        score = claim['K']
        if score != 'infinity' and not (type(score) is int and score >= 0):
            raise ValueError('K must be a nonnegative integer or "infinity"')
        (destination/'experiments').mkdir()
        (destination/'rom.bin').write_bytes(rom)
        (destination/'claim.json').write_text(json.dumps({'K': score}, separators=(',', ':'))+'\n')
        exp_fd = os.open(candidate/'experiments', os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try:
            total = 0
            source_entries = list(os.scandir(exp_fd))
            if len(source_entries) > 256:
                raise ValueError('too many proof source files')
            for entry in source_entries:
                name = entry.name
                if name == 'original-allocation.term':
                    valid_name = True
                else:
                    suffix = next((s for s in ('Script.sml', 'Lib.sml', 'Lib.sig')
                                   if name.endswith(s)), None)
                    valid_name = (name.isascii() and suffix is not None and
                                  name[:-len(suffix)].isidentifier())
                if not valid_name:
                    raise ValueError('unsupported proof source name: '+name)
                if not entry.is_file(follow_symlinks=False):
                    raise ValueError('proof sources must be regular files: '+name)
                contents = read_regular(exp_fd, name, MAX_SOURCE_FILE)
                total += len(contents)
                if total > MAX_SOURCE_TOTAL:
                    raise ValueError('proof sources exceed total size limit')
                (destination/'experiments'/name).write_bytes(contents)
            if not any((destination/'experiments').iterdir()):
                raise ValueError('experiments/ must contain proof sources')
            if not (destination/'experiments'/'original-allocation.term').is_file():
                raise ValueError('experiments/original-allocation.term is required')
        finally:
            os.close(exp_fd)
    finally:
        os.close(fd)
    return score


def author_sandbox_command(bwrap: str, work: Path, standard: Path, author: Path,
                           command):
    """Expose only the toolchain and the job workspace to submitted ML."""
    isolated = [bwrap, '--die-with-parent', '--new-session', '--unshare-net',
                '--unshare-pid', '--ro-bind', '/', '/',
                '--tmpfs', '/home', '--dir', '/home/zksecurity',
                '--dir', '/home/zksecurity/cv_compute',
                '--dir', str(standard), '--dir', str(author),
                '--ro-bind', str(standard), str(standard),
                '--ro-bind', str(author), str(author),
                '--tmpfs', '/root', '--tmpfs', '/run', '--tmpfs', '/var',
                '--dir', '/var/tmp', '--dir', str(ROOT), '--dir', str(work),
                '--ro-bind', str(ROOT), str(ROOT),
                '--bind', str(work), str(work),
                '--ro-bind', str(work/'input'), str(work/'input'),
                '--ro-bind', str(work/'experiments'), str(work/'experiments'),
                '--ro-bind', str(work/'tools/allocationHintLib.sml'),
                str(work/'tools/allocationHintLib.sml'),
                '--tmpfs', '/mnt', '--tmpfs', '/media', '--tmpfs', '/srv',
                '--tmpfs', '/opt', '--proc', '/proc', '--dev', '/dev',
                '--tmpfs', '/tmp', '--clearenv',
                '--setenv', 'PATH', '/usr/local/bin:/usr/bin:/bin',
                '--setenv', 'HOME', str(work/'home'),
                '--setenv', 'TMPDIR', '/tmp',
                '--setenv', 'PYTHONDONTWRITEBYTECODE', '1',
                '--setenv', 'PYTHONNOUSERSITE', '1',
                '--chdir', str(work), '--', *map(str, command)]
    return isolated


def author_sandbox(work: Path, standard: Path, author: Path, command, *,
                   timeout: int, memory_gib: int, stdout=None):
    bwrap = shutil.which('bwrap')
    if bwrap is None:
        raise RuntimeError('source verification requires bubblewrap (bwrap)')
    def limits():
        resource.setrlimit(resource.RLIMIT_CPU, (timeout, timeout + 1))
        memory = memory_gib * 1024**3
        resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
        resource.setrlimit(resource.RLIMIT_FSIZE, (8 * 1024**3, 8 * 1024**3))
        resource.setrlimit(resource.RLIMIT_NOFILE, (256, 256))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    isolated = author_sandbox_command(bwrap, work, standard, author, command)
    return subprocess.run(isolated, cwd=work, stdin=subprocess.DEVNULL,
                          stdout=stdout, stderr=subprocess.STDOUT,
                          preexec_fn=limits, timeout=timeout, check=False)


def install_author_helpers(work: Path):
    """Install fixed, verifier-owned SML helpers beside the isolated build."""
    helper_dir = work/'tools'
    helper_dir.mkdir(mode=0o700)
    helper = helper_dir/'allocationHintLib.sml'
    shutil.copyfile(ROOT/'tools/allocationHintLib.sml', helper)
    helper.chmod(0o444)
    return helper


def install_author_data(work: Path):
    """Expose the participant's allocation hints at the source's QUse path."""
    data_dir = work/'experiments'
    data_dir.mkdir(mode=0o700)
    source = work/'input/experiments/original-allocation.term'
    data = data_dir/'original-allocation.term'
    shutil.copyfile(source, data)
    data.chmod(0o444)
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('candidate', type=Path)
    parser.add_argument('--hol', type=Path, required=True,
                        help='operator-controlled standard HOL4 checkout')
    parser.add_argument('--author-hol', type=Path, required=True,
                        help='separate tracing/export HOL4 checkout')
    parser.add_argument('--work', type=Path,
                        help='new directory for author outputs and strict replay evidence')
    parser.add_argument('--source-timeout', type=int, default=14400)
    parser.add_argument('--source-memory-gib', type=int, default=48,
                        help='per-process author-side address-space limit')
    parser.add_argument('--timeout', type=int, default=10800,
                        help='strict kernel replay time limit')
    parser.add_argument('--memory-gib', type=int, default=112,
                        help='strict kernel replay address-space limit')
    parser.add_argument('--generate-only', action='store_true',
                        help='generate the large article but do not claim verification')
    args = parser.parse_args()
    standard, author = args.hol.resolve(), args.author_hol.resolve()
    if standard == author:
        parser.error('--hol and --author-hol must name distinct HOL checkouts')
    if min(args.source_timeout, args.source_memory_gib, args.timeout, args.memory_gib) < 1:
        parser.error('time and memory limits must be positive')
    work = args.work.absolute() if args.work else ROOT/'.build'/('source-job-'+next(tempfile._get_candidate_names()))
    if work.exists() or work.is_symlink():
        parser.error('--work must name a new directory')
    work.mkdir(mode=0o700, parents=True)
    work = work.resolve()
    (work/'home').mkdir(mode=0o700)
    try:
        check_trusted(ROOT)
        source = work/'input'
        source.mkdir()
        score = frozen_source_submission(args.candidate.absolute(), source)
        # The baseline's allocation source uses a relative QUse path from the
        # isolated build directory. Supply this fixed helper beside that build;
        # it is operator-owned and cannot be submitted or replaced by a user.
        install_author_helpers(work)
        # QUse resolves this untrusted hint relative to build/, so expose the
        # frozen candidate data at ../experiments and mount it read-only.
        install_author_data(work)
        build, exports = work/'build', work/'exports'
        package = work/'generated-package'
        stages = [
            ('build', [sys.executable, ROOT/'tools/build.py', '--hol', standard,
                       '--build-dir', build, '--experiments-dir', source/'experiments',
                       '--jobs', '2', '--maxheap-mib', '24576',
                       'initBaselineCertificateTheory', 'initProofLibraryTheory']),
            ('export', [sys.executable, ROOT/'tools/export_baseline.py', '--hol', standard,
                        '--author-hol', author, '--build-dir', build,
                        '--experiments-dir', source/'experiments', '--output', exports,
                        '--maxheap-mib', '40960']),
            ('bind', [sys.executable, ROOT/'tools/bind_baseline.py', '--hol', standard,
                      '--author-hol', author, '--build-dir', build,
                      '--experiments-dir', source/'experiments', '--rom', source/'rom.bin',
                      '--claim', source/'claim.json', '--output', exports/'binding',
                      '--maxheap-mib', '24576']),
            ('package', [sys.executable, ROOT/'tools/package_baseline.py', '--exports', exports,
                         '--binding', exports/'binding', '--claim', source/'claim.json',
                         '--output', package]),
        ]
        for name, command in stages:
            with (work/(name+'.log')).open('wb') as log:
                result = author_sandbox(work, standard, author, command,
                                        timeout=args.source_timeout,
                                        memory_gib=args.source_memory_gib, stdout=log)
                log.write(f'author stage exit={result.returncode}\n'.encode())
            if result.returncode:
                print(json.dumps({'status': 'source_rejected', 'stage': name,
                                  'exit': result.returncode, 'work': str(work)}))
                return 1
        generated = {'rom_bytes': (package/'rom.bin').stat().st_size,
                     'certificate_bytes': (package/'certificate.art').stat().st_size,
                     'source_bytes': sum(p.stat().st_size for p in (source/'experiments').iterdir()),
                     'score': score}
        (work/'generated-package.json').write_text(json.dumps(generated, indent=2)+'\n')
        if args.generate_only:
            print(json.dumps({'status': 'generated_unverified', **generated,
                              'work': str(work)}))
            return 2
        verifier_work = work/'strict-replay'
        # Invoke the article checker directly as an internal function. There
        # is intentionally no article-only command-line submission route.
        verifier_exit = strict_article_replay([
            '--local', str(package), '--hol', str(standard), '--work', str(verifier_work),
            '--timeout', str(args.timeout), '--memory-gib', str(args.memory_gib), '--progress'])
        print(json.dumps({'status': 'verified' if verifier_exit == 0 else 'rejected',
                          'verifier_exit': verifier_exit, **generated,
                          'work': str(work)}))
        return verifier_exit
    except (OSError, ValueError, json.JSONDecodeError, subprocess.SubprocessError) as exc:
        print(json.dumps({'status': 'rejected', 'reason': str(exc), 'work': str(work)}))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
