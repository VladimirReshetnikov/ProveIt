#!/usr/bin/env python3
"""Freeze the independently reviewed 44-source extension; never runs Lean."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('source freezer rejects optimized Python')
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
ROOT=BASE.parents[1]
MANIFEST=HERE/'source-manifest.json'
SURVEY=HERE/'audit_plan.py'
AUDIT=BASE/'reviews/thirteen-model-parent-current-closure-independent-audit'
PINS={MANIFEST:'815654956ac1033c5314c4c92f692092833552b700db2d42903ad0c60a806e1d',
      SURVEY:'8a41d1437c84ca436f91d1358e24ddcd2854fd268f1dea2b861b0ad9a960139f',
      AUDIT/'CHECK.json':'c2902ee276a1c1dc5c1aaa05015758bf1e9966b79537a1ec53fcea3cc69b48c9',
      AUDIT/'audit.py':'faa450e992b2cc461d5838ad94db27511e08c13880589724499df711c5418768',
      AUDIT/'terminal-observation.json':'d2d6d1eb73f72babfb147219896964f542c9c2fff4e0f1c435c84f5b2c177f5b'}
H=lambda b:hashlib.sha256(b).hexdigest()


def checked_inputs():
    for path,digest in PINS.items():
        if H(path.read_bytes())!=digest:raise ValueError(('pinned input drift',str(path)))
    obs=json.loads((AUDIT/'terminal-observation.json').read_text())
    check=json.loads((AUDIT/'CHECK.json').read_text())
    if obs.get('audit_observed_exit_code')!=0 or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json']:
        raise ValueError('unobserved source survey audit exit')
    if check.get('status')!='PASS_INDEPENDENT_SOURCE_CLOSURE_AUDIT':raise ValueError('bad source audit status')
    plan=json.loads(MANIFEST.read_text())
    if plan.get('additional_project_modules')!=44 or len(plan.get('order',[]))!=44:
        raise ValueError('unexpected source closure size')
    return plan


def run_checks():
    outputs=[]
    for script in (SURVEY,AUDIT/'audit.py'):
        p=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=ROOT,text=True,capture_output=True,timeout=180)
        if p.returncode or p.stderr:raise ValueError(('source audit failure',str(script),p.returncode,p.stdout,p.stderr))
        outputs.append({'path':str(script),'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
    return outputs


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-current-source-'):
        raise ValueError('output must be a fresh /tmp/ipra-thirteen-current-source-* directory')
    if out.exists() or out.is_symlink():raise ValueError('output already exists')
    plan=checked_inputs();before=run_checks();out.mkdir()
    rows={}
    for name in plan['order']:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*',name):
            raise ValueError(('invalid module name',name))
        row=plan['sources'][name]; rel=row['workspace_path']; anchor=plan['source_anchor']
        p=subprocess.run(['git','show',f'{anchor}:{rel}'],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        if p.returncode or H(p.stdout)!=row['sha256'] or H((ROOT/rel).read_bytes())!=row['sha256']:
            raise ValueError(('source drift',name,p.returncode))
        dst=out/'src'/Path(*name.split('.')).with_suffix('.lean')
        dst.parent.mkdir(parents=True,exist_ok=True)
        with dst.open('xb') as f:f.write(p.stdout)
        rows[name]={'snapshot_path':str(dst.relative_to(out)),'workspace_path':rel,'sha256':H(dst.read_bytes()),'imports':row['imports']}
    checked_inputs();after=run_checks()
    if before!=after:raise ValueError('source audit outputs changed')
    for name,row in rows.items():
        if H((out/row['snapshot_path']).read_bytes())!=row['sha256']:
            raise ValueError(('snapshot source changed',name))
    result={'status':'FROZEN_44_SOURCE_EXTENSION_NOT_COMPILED','source_anchor':plan['source_anchor'],
            'source_manifest_sha256':PINS[MANIFEST],'independent_audit_sha256':PINS[AUDIT/'CHECK.json'],
            'parent_manifest_sha256':plan['parent_manifest_sha256'],'order':plan['order'],
            'sources':rows,'direct_parent_boundary':plan['direct_parent_boundary'],'external_direct':plan['external_direct'],
            'source_audit_observations':after,
            'scope':'Frozen source only. No Lean build, actual-zero theorem, transitive/dynamic package audit, or iPRA proof.'}
    with (out/'manifest.json').open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_FROZEN_44_SOURCE_EXTENSION',H((out/'manifest.json').read_bytes()),flush=True)
if __name__=='__main__':main()
