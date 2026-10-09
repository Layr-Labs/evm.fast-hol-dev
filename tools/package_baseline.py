#!/usr/bin/env python3
"""Assemble exported baseline proof data; this does not verify a submission."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil

from export_baseline import ROOT


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exports', type=Path, default=ROOT/'.export-baseline')
    parser.add_argument('--binding', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    exports = args.exports.resolve()
    binding = args.binding.resolve() if args.binding else exports/'binding'
    plan = json.loads((exports/'plan.json').read_text())
    if not isinstance(plan, list) or not plan or len(set(plan)) != len(plan):
        parser.error('invalid export plan')
    articles = []
    for name in plan:
        if not isinstance(name, str) or not name.isidentifier():
            parser.error('invalid theory name in export plan')
        work = exports/name
        info = json.loads((work/'complete.json').read_text())
        article = work/'proof.art'
        if info['article'] != digest(article):
            parser.error('changed author article: '+name)
        articles.append(article)
    info = json.loads((binding/'binding.json').read_text())
    if info['K'] != 'infinity' or info['rom_sha256'] != digest(binding/'rom.bin') or \
       info['article_sha256'] != digest(binding/'binding.art'):
        parser.error('changed or unsupported literal binding')
    articles.append(binding/'binding.art')
    output = args.output.resolve()
    output.mkdir(mode=0o700, parents=True, exist_ok=False)
    shutil.copyfile(binding/'rom.bin', output/'rom.bin')
    (output/'claim.json').write_text('{"K":"infinity"}\n')
    with (output/'certificate.art').open('wb') as target:
        for article in articles:
            with article.open('rb') as source:
                shutil.copyfileobj(source, target, length=1024*1024)
    print(f'Assembled {len(articles)} articles, {(output/"certificate.art").stat().st_size} bytes.')
    print(f'Not yet verified. Run verifier/verify.py --local {output} --progress')


if __name__ == '__main__':
    main()
