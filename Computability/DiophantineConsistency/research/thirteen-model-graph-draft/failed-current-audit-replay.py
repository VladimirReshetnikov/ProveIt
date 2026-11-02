#!/usr/bin/env python3
"""Paired conditional generic graph cut over the audited 69-DAG provider."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('replay rejects optimized Python')
if not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke with python3 -I -S')
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
SOURCE=HERE/'Model69GraphCut.lean'
AUDIT=BASE/'reviews/thirteen69-dag-binding-independent-audit'
PROVIDER=Path('/tmp/ipra-thirteen69-dag-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PINS={SOURCE:'9091ab7612135d586e7518a1b61aa9c03d19fed91e961b47834df781b9d92941',
      AUDIT/'audit.py':'bc0944f563fbe66b4fb322e1f59612a849392980a72ff6f7d8ea430bf0ab08da',
      AUDIT/'CHECK.json':'26a42d561a232e2a49dae61f3a1f6f4cd882e3d38b6616aa62ed2ffcb0c081e5',
      AUDIT/'terminal-observation.json':'3556edbc7b3f65a321d47c87a07bcc258da82ca79f66d1cc2afeb64c5bbd7b25',
      LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()


def check_pins():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    obs=json.loads((AUDIT/'terminal-observation.json').read_text());check=json.loads((AUDIT/'CHECK.json').read_text())
    if obs.get('audit_observed_exit_code')!=0 or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json'] or check.get('status')!='PASS_INDEPENDENT_THIRTEEN69_DAG_AUDIT':
        raise ValueError('invalid parent audit')


def audit():
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],text=True,capture_output=True,timeout=180)
    if p.returncode or p.stderr:raise ValueError(('parent audit failed',p.returncode,p.stdout,p.stderr))
    d=json.loads(p.stdout)
    if d.get('status')!='PASS_INDEPENDENT_THIRTEEN69_DAG_AUDIT':raise ValueError(('parent status',d))
    return d


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-graph-cut-pair-'):
        raise ValueError('output must be a fresh direct /tmp/ipra-thirteen-graph-cut-pair-* directory')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    check_pins();before=audit();out.mkdir();runs=[]
    for label in ('author','peer'):
        root=out/label/'src';root.mkdir(parents=True);src=root/'Model69GraphCut.lean';obj=out/label/'Model69GraphCut.olean'
        shutil.copyfile(SOURCE,src);lib=PROVIDER/label/'lib';env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
                env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
        cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        p=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=180);output=p.stdout+p.stderr
        reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
        if p.returncode or p.stderr or 'warning:' in output or 'error:' in output or 'sorryAx' in output or len(reports)!=1:
            raise ValueError(('unexpected Lean result',label,p.returncode,output))
        if {x.strip() for x in reports[0].split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:
            raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency/ThirteenCarrier.olean'),str(PACKAGE/'Mathlib/Tactic/LinearCombination.olean')}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:
            raise ValueError(('unexpected direct imports',label,deps.returncode,deps.stdout,deps.stderr))
        if H(src)!=PINS[SOURCE]:raise ValueError(('source drift',label))
        runs.append({'label':label,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'command':cmd,
                     'source_sha256':H(src),'object_sha256':H(obj),'axiom_reports':reports,
                     'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
    if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['stdout']!=runs[1]['stdout']:
        raise ValueError('sibling outputs differ')
    check_pins();after=audit()
    if before!=after:raise ValueError('parent audit output changed')
    receipt={'status':'PASS_PAIRED_THIRTEEN_GRAPH_CUT','runs':runs,'parent_audit':after,
             'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
             'scope':'Conditional four-norm commutative-ring graph cut only. No actual-zero extraction, model-provider join, rank phase, fixed-port calibration, iPRA theorem, Foundation outer-wrapper exit, or complete package-transitive/dynamic audit is claimed.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_GRAPH_CUT',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
