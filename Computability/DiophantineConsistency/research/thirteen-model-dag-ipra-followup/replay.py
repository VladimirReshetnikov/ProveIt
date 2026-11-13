#!/usr/bin/env python3
"""Paired exact-DAG iPRA client over independently audited successor siblings."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
if not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke with python3 -I -S')
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
SOURCE=HERE/'Model69DagIPRADraft.lean'
AUDIT=BASE/'reviews/thirteen-model-endpoint-successor-pair-independent-audit'
PARENT=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
PINS={SOURCE:'235d81f3b1d399593e413587863a531277b9c41b989c8c9d6d663381242de792',
      PARENT/'receipt.json':'8cf5b948a9442105a88627653e99e78d395a8f40f496b88e9adb6e439630e5cd',
      AUDIT/'CHECK.json':'50c18ab38d6393cf784e658b5626bb6ec3cb490dc1652f5b5dcfa2b1adca1cce',AUDIT/'audit.py':'ec4892d88e69a9f53d3d93d48ce9e43cc8a5f9631ed4a885af17a40011858681',
      AUDIT/'terminal-observation.json':'9f65d29fd39bab15653d0f35ebf78dea2d590618502ffe56fed8fa863c9082ba',
      LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
STATUS='PASS_INDEPENDENT_THIRTEEN_ENDPOINT_SUCCESSOR_PAIR_AUDIT'
NAMES=('sameNoZeroDag','bridgeDag','native_equivalenceDag','standard_equivalenceDag','reference_equivalenceDag','standard_translated_consistencyDag')

def check_pins():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    check=json.loads((AUDIT/'CHECK.json').read_text());obs=json.loads((AUDIT/'terminal-observation.json').read_text())
    if check.get('status')!=STATUS or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json'] or obs.get('observed_exit')!=0:
        raise ValueError('parent audit observation')

def audit():
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],text=True,capture_output=True,timeout=900)
    if p.returncode or p.stderr:raise ValueError(('parent audit failed',p.returncode,p.stdout,p.stderr))
    data=json.loads(p.stdout)
    if data.get('status')!=STATUS:raise ValueError(('parent audit status',data))
    return data

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-dag-ipra-pair-'):raise ValueError('invalid output')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    check_pins();before=audit();out.mkdir();runs=[]
    for side in ('author','peer'):
        run=out/side;root=run/'src';root.mkdir(parents=True);src=root/'Model69DagIPRADraft.lean';obj=run/'Model69DagIPRADraft.olean'
        shutil.copyfile(SOURCE,src);lib=PARENT/side/'lib';env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
        cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        p=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=180);output=p.stdout+p.stderr
        reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",output,re.M)
        if p.returncode or p.stderr or 'warning:' in output or 'error:' in output or 'sorryAx' in output:
            raise ValueError(('unexpected Lean result',side,p.returncode,output))
        if [n for n,_ in reports]!=['Model69DagIPRADraft.'+n for n in NAMES] or any({x.strip() for x in a.split(',') if x.strip()}!={'propext','Classical.choice','Quot.sound'} for _,a in reports):
            raise ValueError(('unexpected named axiom reports',side,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean'),str(lib/'Model69EndpointBindingDraft.olean'),str(lib/'DiophantineConsistency/IPRABoundedRhoZFC.olean')}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('direct imports',side,deps.returncode,deps.stdout,deps.stderr))
        if H(src)!=PINS[SOURCE]:raise ValueError(('source drift',side))
        runs.append({'side':side,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'command':cmd,'source_sha256':H(src),'object_sha256':H(obj),'axiom_reports':reports,'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
    if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['stdout']!=runs[1]['stdout']:raise ValueError('sibling outputs differ')
    check_pins();after=audit()
    if before!=after:raise ValueError('parent audit output changed')
    receipt={'status':'PASS_PAIRED_THIRTEEN_DAG_IPRA','runs':runs,'parent_audit':after,
      'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Lean derivability theorems for the exact shifted 69-node 2011 literal in the selected native, standard and reference iPRA presentations, including the standard translated Foundation consistency sentence. Exact encoding and all inherited Foundation, package-transitive/dynamic and external/internal boundaries remain; no minimality or phase-split2471 calibration is claimed.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_DAG_IPRA',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
