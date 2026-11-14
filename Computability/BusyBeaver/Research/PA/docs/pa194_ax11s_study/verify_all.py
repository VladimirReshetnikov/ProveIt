#!/usr/bin/env python3
"""Rebuild and verify PA194AX11S in isolation, using only Python's stdlib.

The report distinguishes executable certificates, relative iPRA source
equivalence, and the still-open absolute iPRA consistency equivalence.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Use Python without -O or PYTHONOPTIMIZE.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    manifest=ROOT/'SHA256SUMS'
    checked=0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            expected,name=line.split('  ',1)
            path=ROOT/name
            if not path.is_file() or sha(path)!=expected:
                raise SystemExit('Integrity failure: '+name)
            checked+=1
    with tempfile.TemporaryDirectory(prefix='pa194ax11s-verify-') as temp:
        work=Path(temp)/'packet'
        work.mkdir()
        for name in ('construction','reference','verification','proof','comparison','machine'):
            shutil.copytree(ROOT/name,work/name,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        shutil.copy2(ROOT/'build.py',work/'build.py')
        def run(label,*argv):
            print(label,flush=True)
            r=subprocess.run([sys.executable,'-B',*map(str,argv)],cwd=work,
                             stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
            if r.returncode:
                print(r.stdout)
                print(r.stderr,file=sys.stderr)
                raise SystemExit(f'{label}: failed with exit {r.returncode}')
        run('Rebuilding and checking all construction contracts','build.py','--output','rebuilt')
        names=('machine.tm','machine.native.tm','raw.native.tm','labels.json','nodes.json',
               'grammar.json','grammar.tree.json','sites.json','instructions.json',
               'folds.json','local_folds.json','source_binding.json','native_changes.json')
        for name in names:
            if (work/'rebuilt'/name).read_bytes()!=(ROOT/'machine'/name).read_bytes():
                raise SystemExit('Reconstruction mismatch: '+name)
        run('Replaying independent literal-tape contracts','verification/check_literal.py',
            '--machine','rebuilt','--output','independent')
        run('Checking exact source boundaries and counter formulas','proof/check_source_equivalence.py')
        run('Checking cofinite collision certificates','proof/check_cofinite_collision.py')
        run('Recomputing the complete frozen novelty frontier','comparison/check_novelty.py',
            '--candidate','rebuilt/machine.tm','--receipt','novelty.json')
        load=lambda p:json.loads((work/p).read_text())
        construction=load('rebuilt/receipt.json')
        independent=load('independent/receipt.json')
        if independent!=json.loads((ROOT/'machine/independent/receipt.json').read_text()):
            raise SystemExit('Independent receipt mismatch.')
        result={'status':'PASS','family':'PA194AX11S','integrity_files_checked':checked,
                'exactly_rebuilt_files':list(names),'working_states':construction['working_states'],
                'transition_rows':construction['transition_rows'],
                'dense_sha256':construction['dense_sha256'],
                'construction_runtime':construction['runtime'],
                'independent_literal_replay':independent,
                'source_proof_check':load('proof/source_equivalence_check.json'),
                'cofinite_collision_status':load('proof/cofinite_collision_check.json')['status'],
                'novelty':load('novelty.json'),
                'kernel_checked':False,'absolute_ipra_consistency_equivalence_established':False,
                'scope':'Complete deterministic replay; absolute calibration remains explicitly open.'}
    text=json.dumps(result,indent=2)+'\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(text)
    print(text,end='')

if __name__=='__main__':
    main()
