#!/usr/bin/env python3
"""Check author export against independent standard-kernel article replay."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

from compact_article import compact

ROOT = Path(__file__).resolve().parents[1]


def run(hol, script, cwd, marker):
    result = subprocess.run([str(hol/'bin/hol'), 'run',
        str(hol/'sigobj/holmake_not_interactive.uo'), str(script)],
        cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=120, check=False)
    if result.returncode or marker not in result.stdout:
        raise RuntimeError(result.stdout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hol', type=Path, required=True)
    parser.add_argument('--author-hol', type=Path, required=True)
    args = parser.parse_args()
    hol, author = args.hol.resolve(), args.author_hol.resolve()
    if hol == author:
        parser.error('the author and verifier HOL builds must be separate')
    subprocess.run(['python3', str(ROOT/'tools/build.py'), '--hol', str(hol),
                    'replayChecksTheory'], check=True)
    with tempfile.TemporaryDirectory(prefix='init-export-test-') as temp:
        work = Path(temp)
        exporter = work/'export.sml'
        exporter.write_text('TraceMode.mode := TraceMode.TraceOnly;\nload "cv_transLib";\n' +
            'QUse.use '+json.dumps(str(ROOT/'verifier/literalDecodeLib.sml'))+';\n'+
            'QUse.use '+json.dumps(str(ROOT/'tools/export_smoke.sml'))+';\n')
        run(author, exporter, work, 'EXPORT_SMOKE_OK')
        hint_test = work/'hint.sml'
        hint_test.write_text('load "sptreeTheory";\nload "sptreeSyntax";\nload "optionSyntax";\n' +
            'QUse.use '+json.dumps(str(ROOT/'tools/allocationHintLib.sml'))+';\n' +
            'open HolKernel boolLib bossLib;\n' +
            'val value = ``[SOME (sptree$BS sptree$LN 2 (sptree$LS 3)); NONE; ' +
            'SOME (sptree$BN (sptree$LS 1) sptree$LN)] : num sptree$spt option list``;\n' +
            'val _ = allocationHintLib.write "hint.data" value;\n' +
            'val _ = if aconv value (allocationHintLib.read "hint.data") then ' +
            'print "HINT_ROUND_TRIP_OK\\n" else raise Fail "hint differs";\n')
        run(hol, hint_test, work, 'HINT_ROUND_TRIP_OK')
        build = (ROOT/'.build').resolve()
        loader = work/'replay.sml'
        loader.write_text('holpathdb.extend_db {vname="init-e-hol4",path=' +
            json.dumps(str(ROOT)) + '};\nloadPath := ' + json.dumps([str(build/'.hol/objs'),
            str(build)]) + ' @ !loadPath;\n' +
            (ROOT/'tools/replay_smoke.sml').read_text())
        run(hol, loader, work, 'LITERAL_REQUEST_REPLAY_OK')
        compact(work/'cv-smoke.art', work/'compact.art')
        (work/'compact.art').replace(work/'cv-smoke.art')
        run(hol, loader, work, 'LITERAL_REQUEST_REPLAY_OK')
        print('PASS: independent article replay (fresh definitions and CV computation)')


if __name__ == '__main__':
    main()
