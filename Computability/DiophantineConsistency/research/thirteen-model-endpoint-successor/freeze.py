#!/usr/bin/env python3
"""Freeze the 338-source candidate frontier. No Lean is launched."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('freezer rejects optimized Python')
if not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke with python3 -I -S')
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
ROOT=BASE.parents[1]
PLAN=BASE/'research/thirteen-model-endpoint-closure'
AUDIT=BASE/'reviews/thirteen-model-endpoint-closure-independent-audit'
PARENT=Path('/tmp/ipra-ordinary12-coexistence-source-03/manifest.json')
PINS={PLAN/'source-manifest.json':'de858182dbaab901257fe1ab0f9ede3a0a8e15f39f2b9c8b1d794f28814fc3bb',
      PLAN/'historical-comparison.json':'9dea919924830a514a0bad698ff5a2bf09f97d167f5d5f67e7ee81dc8ceb8de6',
      PLAN/'frontier-plan.json':'73d0ff4eff130c0bf74ae7ba170e591f1b62b2d43dd0fcaf654964a4ba3e2b9e',
      PARENT:'9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded',
      AUDIT/'CHECK.json':'ab2255186de1e61028731a47a1c92e89792835efe7317e4560b86861bc002af7',
      AUDIT/'audit.py':'30ccbcaa1050d3c9e6b9e4b73e930928fd93cba2380bba3ecdb629de755e587c',
      AUDIT/'terminal-observation.json':'ed0c3e7b515f2f0e642f278ac67f44f2eae7cc035e4991b51c96756dc3762dda'}
STATUS='PASS_INDEPENDENT_THIRTEEN_ENDPOINT_CLOSURE_AUDIT'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
NAME=re.compile(r'^[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*$')

def check_inputs():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('pinned input drift',str(p)))
    obs=json.loads((AUDIT/'terminal-observation.json').read_text());check=json.loads((AUDIT/'CHECK.json').read_text())
    if check.get('status')!=STATUS or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json'] or obs.get('observed_exit')!=0:
        raise ValueError('missing independent plan audit')
    plan=json.loads((PLAN/'frontier-plan.json').read_text());survey=json.loads((PLAN/'source-manifest.json').read_text());base=json.loads(PARENT.read_text())
    if plan['status']!='CANDIDATE_FRONTIER_PLAN_NOT_A_BUILD' or plan['rebuild_count']!=338 or plan['reusable_seed_count']!=807:
        raise ValueError('unexpected plan')
    rows=dict(base['sources']);rows.update(survey['sources'])
    if len(plan['rebuild_order'])!=338 or len(set(plan['rebuild_order']))!=338:raise ValueError('frontier order')
    return plan,survey,rows

def check_audit():
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],cwd=ROOT,text=True,capture_output=True,timeout=300)
    if p.returncode or p.stderr:raise ValueError(('independent plan audit failed',p.returncode,p.stdout,p.stderr))
    d=json.loads(p.stdout)
    if d.get('status')!=STATUS:raise ValueError(('plan audit status',d))
    return d

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--preflight-only',action='store_true');a=ap.parse_args()
    out=a.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-endpoint-source-'):
        raise ValueError('output must be a fresh direct /tmp/ipra-thirteen-endpoint-source-* path')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    script=H(Path(__file__));plan,survey,rows=check_inputs();before=check_audit()
    if a.preflight_only:
        print('PREFLIGHT_FROZEN_FRONTIER',len(plan['rebuild_order']),flush=True);return
    out.mkdir();frozen={}
    for name in plan['rebuild_order']:
        if not NAME.fullmatch(name):raise ValueError(('invalid module',name))
        row=rows[name];rel=row['workspace_path'];anchor=survey['source_anchor']
        p=subprocess.run(['git','show',f'{anchor}:{rel}'],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
        digest=hashlib.sha256(p.stdout).hexdigest()
        if p.returncode or digest!=row['sha256'] or H(ROOT/rel)!=digest or plan['all_selected_source_hashes'][name]!=digest:
            raise ValueError(('source drift',name,p.returncode))
        dst=out/'src'/Path(*name.split('.')).with_suffix('.lean');dst.parent.mkdir(parents=True,exist_ok=True)
        with dst.open('xb') as f:f.write(p.stdout)
        frozen[name]={'snapshot_path':str(dst.relative_to(out)),'workspace_path':rel,'sha256':digest,'imports':row['imports']}
    check_inputs();after=check_audit()
    if before!=after or H(Path(__file__))!=script:raise ValueError('audit or freezer drift')
    for n,row in frozen.items():
        if H(out/row['snapshot_path'])!=row['sha256']:raise ValueError(('snapshot drift',n))
    result={'status':'FROZEN_338_SOURCE_FRONTIER_NOT_COMPILED','source_anchor':survey['source_anchor'],'source_manifest_sha256':PINS[PLAN/'source-manifest.json'],
      'frontier_plan_sha256':PINS[PLAN/'frontier-plan.json'],'independent_plan_audit_sha256':PINS[AUDIT/'CHECK.json'],
      'freezer_sha256':script,'order':plan['rebuild_order'],'sources':frozen,'reusable_seeds':plan['reusable_seeds'],
      'audit':after,'scope':'Frozen source only. No Lean build, complete axiom inventory, fixed-port calibration or iPRA endpoint claimed.'}
    with (out/'manifest.json').open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_FROZEN_338_SOURCE_FRONTIER',H(out/'manifest.json'),flush=True)
if __name__=='__main__':main()
