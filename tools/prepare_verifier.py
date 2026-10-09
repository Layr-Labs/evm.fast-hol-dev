#!/usr/bin/env python3
"""Build an operator-owned fixed HOL verifier heap. No candidate is involved."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'verifier'))
import verify
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--hol', type=Path, required=True)
a = p.parse_args()
hol = a.hol.resolve()
verify.check_trusted()
pin = json.loads((ROOT/'provenance.json').read_text())['tested_hol']
revision = subprocess.check_output(['git','-C',str(hol),'rev-parse','HEAD'],text=True).strip()
if revision != pin:
    p.error('HOL checkout does not match the tested_hol pin')
subprocess.run([sys.executable,str(ROOT/'tools/build.py'),'--hol',str(hol),
    'initProofLibraryTheory.uo','certificateReplayLib.uo'],check=True)
subprocess.run([str(hol/'bin/hol'),'run',str(hol/'sigobj/holmake_not_interactive.uo'),
    str(ROOT/'verifier/prepareHeap.sml')],cwd=ROOT/'.build',check=True)
heap = ROOT/'.build/verifier.heap'
if not heap.is_file(): raise SystemExit('HOL did not produce the verifier heap')
def digest(path):
    with path.open('rb') as stream: return hashlib.file_digest(stream,'sha256').hexdigest()
info = {'hol':str(hol), 'hol_revision':revision, 'heap_sha256':digest(heap),
        'manifest_sha256':digest(ROOT/'verifier/trusted-files.json')}
(ROOT/'.build/verifier.json').write_text(json.dumps(info,indent=2)+'\n')
print('Prepared fixed verifier heap:',heap)
