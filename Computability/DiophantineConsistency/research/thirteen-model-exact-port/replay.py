#!/usr/bin/env python3
"""Paired exact-port specialization over the independently audited converse."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('replay rejects optimized Python')
if not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke with python3 -I -S')
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
SOURCE=HERE/'Model69ExactPort.lean'
AUDIT=BASE/'reviews/thirteen-model-fresh-graph-independent-audit'
PARENTS=[Path('/tmp')/name for name in ('ipra-thirteen-fresh-graph-pair-01','ipra-thirteen-current-outer-pair-01','ipra-thirteen-current-phase-pair-01','ipra-thirteen-parent-outer-pair-01','ipra-thirteen-parent-growth-replay-01','ipra-thirteen-parent-transport-replay-01','ipra-thirteen-parent-phase-replay-01','ipra-thirteen-retained-norm-pair-01','ipra-thirteen-model-view-pair-01','ipra-thirteen-graph-cut-pair-01')]
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
PINS={SOURCE:'0b7db7e4d5d33435b76832dfca3ff2187187a024abce17960dd059a626e187a9',
      AUDIT/'CHECK.json':'c8c5dff42f52db59d847fb9105fb207ceb9700a4f108d1dd2e8e1010a1d5777e',AUDIT/'audit.py':'415c886889f5fc8dde43bd9e330952c59fc70dc79fb334a33d6c9875d59523ee',AUDIT/'terminal-observation.json':'414fa021e5010616c42ffac8252b2366ad877fc8fceac3c6bc2af938ebbece6f',
      LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
STATUS='PASS_INDEPENDENT_THIRTEEN_FRESH_GRAPH_AUDIT'

def check_pins():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    check=json.loads((AUDIT/'CHECK.json').read_text());obs=json.loads((AUDIT/'terminal-observation.json').read_text())
    if check.get('status')!=STATUS or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json'] or obs.get('observed_exit')!=0:
        raise ValueError('parent audit observation')

def audit():
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],text=True,capture_output=True,timeout=300)
    if p.returncode or p.stderr:raise ValueError(('parent audit failed',p.returncode,p.stdout,p.stderr))
    data=json.loads(p.stdout)
    if data.get('status')!=STATUS:raise ValueError(('parent audit status',data))
    return data

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-exact-port-pair-'):
        raise ValueError('output must be a fresh direct /tmp/ipra-thirteen-exact-port-pair-* path')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    check_pins();before=audit();out.mkdir();runs=[]
    for label in ('author','peer'):
        run=out/label;root=run/'src';root.mkdir(parents=True);src=root/'Model69ExactPort.lean';obj=run/'Model69ExactPort.olean'
        shutil.copyfile(SOURCE,src);env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=':'.join(map(str,[*(p/label for p in PARENTS),PARENTS[0]/label/'lib',PACKAGE]))
        cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        p=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=180);output=p.stdout+p.stderr
        reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
        if p.returncode or p.stderr or 'warning:' in output or 'error:' in output or 'sorryAx' in output or reports!=['propext','propext, Classical.choice, Quot.sound']:
            raise ValueError(('unexpected Lean result',label,p.returncode,output))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean'),str(PARENTS[0]/label/'Model69FreshNorms.olean')}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('direct imports',label,deps.returncode,deps.stdout,deps.stderr))
        if H(src)!=PINS[SOURCE]:raise ValueError(('source drift',label))
        runs.append({'label':label,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'command':cmd,'source_sha256':H(src),'object_sha256':H(obj),'axiom_reports':reports,'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
    if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['stdout']!=runs[1]['stdout']:raise ValueError('sibling outputs differ')
    check_pins();after=audit()
    if before!=after:raise ValueError('audit output changed')
    receipt={'status':'PASS_PAIRED_THIRTEEN_EXACT_PORT','runs':runs,'parent_audit':after,
      'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Actual positive 2011 parent zero yields an exact shifted-69-node 2011 literal zero, without an external port-vector hypothesis. No opposite implication, iPRA proof, phase-split2471 calibration, Foundation outer-wrapper exit, complete inherited prefix/window axiom inventory, or package-transitive/dynamic audit is claimed.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_EXACT_PORT',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
