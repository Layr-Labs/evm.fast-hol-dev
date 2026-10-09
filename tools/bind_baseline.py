#!/usr/bin/env python3
"""Export exact baseline Certificate binding to operator-sanitized literals."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

from compact_article import compact
from export_baseline import ROOT, author_setup, dependencies, local_closure, theory_sources


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hol', type=Path, required=True)
    parser.add_argument('--author-hol', type=Path, required=True)
    parser.add_argument('--build-dir', type=Path, default=ROOT/'.build')
    parser.add_argument('--output', type=Path, default=ROOT/'.export-baseline/binding')
    parser.add_argument('--maxheap-mib', type=int, default=24576)
    parser.add_argument('--rom', type=Path, default=ROOT/'artifacts/baseline/rom.bin')
    args = parser.parse_args()
    if args.maxheap_mib < 1:
        parser.error('--maxheap-mib must be positive')
    standard, author = args.hol.resolve(), args.author_hol.resolve()
    build, output = args.build_dir.resolve(), args.output.resolve()
    if standard == author or (build/'hol-path.txt').read_text() != str(standard):
        parser.error('use distinct author and standard HOL, and its matching build directory')
    sources = theory_sources()
    fixed = set(local_closure(build, sources, 'initProofLibrary'))
    candidates = [name for name in local_closure(build, sources, 'initBaselineCertificate')
                  if name not in fixed]
    output.mkdir(parents=True, exist_ok=True)
    rom = args.rom.read_bytes()
    (output/'rom.bin').write_bytes(rom)
    deps = [str(Path(dep).with_suffix('')) for dep in dependencies(build, 'initBaselineCertificate')]
    deps += ['initBaselineCertificateTheory', 'cv_transLib']
    script = output/'bind.sml'
    script.write_text(author_setup(build, standard, deps, candidates+['baselineLiteralBinding']) +
        'val _ = QUse.use '+json.dumps(str(ROOT/'verifier/literalDecodeLib.sml'))+';\n'+
        'val _ = QUse.use '+json.dumps(str(ROOT/'tools/bind_baseline.sml'))+';\n')
    article = output/'binding.art'
    env = dict(os.environ, HOL_INIT_E_ROM=str(output/'rom.bin'),
               HOL_INIT_E_BINDING_ARTICLE=str(article))
    with (output/'binding.log').open('w') as log:
        result = subprocess.run([str(author/'bin/hol'), '--maxheap', str(args.maxheap_mib), '--gcthreads=1', 'run',
            str(author/'sigobj/holmake_not_interactive.uo'), str(script)],
            cwd=output, env=env, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode or 'BASELINE_LITERAL_BINDING_OK' not in (output/'binding.log').read_text():
        raise RuntimeError(f'Literal binding failed: {output/"binding.log"}')
    compact(article, output/'binding.compact.art')
    (output/'binding.compact.art').replace(article)
    with article.open('rb') as stream:
        digest = hashlib.file_digest(stream, 'sha256').hexdigest()
    (output/'binding.json').write_text(json.dumps({'K':'infinity',
        'rom_sha256':hashlib.sha256(rom).hexdigest(), 'article_sha256':digest}, indent=2)+'\n')
    print('Exported literal binding; independent full-certificate replay is still required.')


if __name__ == '__main__':
    main()
