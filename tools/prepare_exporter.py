#!/usr/bin/env python3
"""Build an isolated proof-recording HOL for authors; never used to accept proofs.

The verifier continues to use the unmodified tested HOL and strict replay.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def run(arguments, *, cwd=None, env=None):
    subprocess.run(arguments, cwd=cwd, env=env, check=True)


def output(arguments, *, cwd=None):
    return subprocess.check_output(arguments, cwd=cwd, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hol-source', type=Path, required=True,
                        help='local checkout containing the tested HOL commit')
    parser.add_argument('--output', type=Path, default=ROOT.parent/'HOL-init-e-export')
    parser.add_argument('-j', '--jobs', type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    source, destination = args.hol_source.resolve(), args.output.resolve()
    if source == destination:
        parser.error('the author build must be separate from the verifier HOL')
    pin = json.loads((ROOT/'provenance.json').read_text())['tested_hol']
    patch = ROOT/'tools/exporter-hol.patch'
    if not destination.exists():
        run(['git', '-C', str(source), 'worktree', 'add', '--detach',
             str(destination), pin])
    if output(['git', 'rev-parse', '--show-toplevel'], cwd=destination) != str(destination):
        parser.error('--output is not a distinct Git checkout')
    if output(['git', 'rev-parse', 'HEAD'], cwd=destination) != pin:
        parser.error('--output is not at the tested HOL pin')
    applied = subprocess.run(['git', 'apply', '--reverse', '--check', str(patch)],
                             cwd=destination, stdout=subprocess.DEVNULL,
                             stderr=subprocess.DEVNULL).returncode == 0
    if not applied:
        run(['git', 'apply', '--check', str(patch)], cwd=destination)
        run(['git', 'apply', str(patch)], cwd=destination)
    if not (destination/'bin/build').is_file():
        run(['poly', '--script', 'tools/smart-configure.sml'], cwd=destination)
    env = dict(os.environ, HOL_TRACE_MODE='none')
    run(['bin/build', '--trknl', '--no-helpdocs', '-j', str(args.jobs)],
        cwd=destination, env=env)
    print(f'Author proof-export HOL ready: {destination}')


if __name__ == '__main__':
    main()
