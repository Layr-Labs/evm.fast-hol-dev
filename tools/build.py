#!/usr/bin/env python3
"""Build the focused HOL4 port (no Lean toolchain required)."""
import argparse
import fcntl
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--hol', type=Path, default=Path(os.environ.get('HOLDIR', ROOT.parent/'HOL')))
p.add_argument('-j', '--jobs', type=int, default=3)
p.add_argument('--maxheap-mib', type=int, default=24576, help='Poly/ML heap limit per HOL worker')
p.add_argument('--build-dir', type=Path, help='isolated output directory for a different HOL toolchain')
p.add_argument('targets', nargs='*', default=['initParamsTheory.uo', 'initGuestTheory.uo',
                                         'initSimplifyTheory.uo', 'initTargetTheory.uo',
                                         'initGasTheory.uo', 'initObservationsTheory.uo',
                                         'initHostTheory.uo', 'initSourceTheory.uo',
                                         'initStructsTheory.uo', 'initGlobalsTheory.uo',
                                         'initChallengeTheory.uo', 'initAccelChecksTheory.uo',
                                         'replayChecksTheory.uo', 'certificateReplayLib.uo'])
a = p.parse_args()
if a.jobs < 1 or a.jobs > 3 or a.maxheap_mib < 1:
    p.error('use 1 to 3 workers and a positive heap limit')
hol = a.hol.resolve()
if not (hol/'bin/Holmake').is_file():
    p.error('build HOL4 first, then set --hol or HOLDIR')
if not (ROOT/'cakeml/pancake/panLangScript.sml').is_file():
    p.error('run git submodule update --init')
# A flat source view gives Holmake one dependency search path. No upstream
# files are edited and unrelated CakeML heaps/examples are not build targets.
build = a.build_dir.resolve() if a.build_dir is not None else ROOT/'.build'
build.mkdir(exist_ok=True)
lock = (build/"build.lock").open("w")
fcntl.flock(lock, fcntl.LOCK_EX)
stamp = build/'hol-path.txt'
if stamp.exists() and stamp.read_text() != str(hol):
    p.error('this .build belongs to another HOL checkout; remove .build before switching')
stamp.write_text(str(hol))
directories = [ROOT/'challenge', ROOT/'experiments', ROOT/'verifier'] + [ROOT/'cakeml'/x for x in [
    'misc', 'basis/pure', 'compiler/encoders/asm', 'compiler/backend', 'semantics', 'semantics/ffi', 'pancake', 'cv_translator',
    'compiler/backend/cv_compute', 'compiler/backend/reg_alloc', 'compiler/backend/pattern_matching', 'compiler/inference', 'compiler/inference/proofs',
    'compiler/parsing', 'compiler/printing', 'semantics/proofs',
    'compiler/encoders/riscv', 'compiler/backend/riscv', 'compiler/backend/semantics',
    'translator/monadic/monad_base', 'translator',
    'compiler/backend/serialiser', 'compiler/backend/gc', 'unverified/reg_alloc', 'pancake/semantics',
    'pancake/proofs', 'compiler/backend/proofs', 'compiler/backend/reg_alloc/proofs',
    'compiler/encoders/riscv/proofs']]
for directory in directories:
    for source in directory.iterdir():
        if source.suffix not in {'.sml', '.sig'} or 'Theory.' in source.name: continue
        target = build/source.name
        if target.is_symlink():
            if target.resolve() != source.resolve(): p.error('duplicate module '+source.name)
        elif target.exists(): p.error('unexpected file '+str(target))
        else: target.symlink_to(os.path.relpath(source, build))
cmd = [str(hol/'bin/Holmake'), '--no-project', '--no_hmakefile', '--no_preexecs',
       '--rebuild_deps', '--keep-going', '--heap-size', str(a.maxheap_mib), '-j', str(a.jobs)]
for directory in ['examples/pl-semantics/lprefix_lub',
    'examples/machine-code/hoare-triple', 'examples/l3-machine-code/riscv/model',
    'examples/l3-machine-code/riscv/step',
    'examples/formal-languages/regular', 'examples/machine-code/multiword',
    'examples/formal-languages/context-free', 'examples/formal-languages',
    'examples/data-structures/balanced_bst', 'examples/algorithms',
    'examples/algorithms/unification/triangular/first-order',
    'examples/algorithms/unification/triangular/first-order/compilation',
    'src/transfer/examples', 'src/search']:
    cmd += ['-I', str(hol/directory)]
raise SystemExit(subprocess.call(cmd+a.targets, cwd=build))
