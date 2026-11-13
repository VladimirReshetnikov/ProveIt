#!/usr/bin/env python3
"""Paired actual-zero retained graph norms over the audited model-view pair."""
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
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=HERE/'Model69RetainedNorm.lean'
AUDIT=ROOT/'reviews/thirteen-model-view-map-independent-audit'
PARENT=Path('/tmp/ipra-thirteen-model-view-pair-01')
GRAPH=Path('/tmp/ipra-thirteen-graph-cut-pair-01')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'dc0fc6b25fdbbab4c47fc560538c40795dd3cfa5c44a5ed6e8e05afe0bcd88ca',
      AUDIT/'audit.py':'f99e47dfd28ef23591a5e3ff3ea5b47a40114faf1e816cb8aa2c0f75655c9d5e',
      AUDIT/'CHECK.json':'4b90ba8d095ba9e0a22343b5a32163e59ada61a34db348102f4e622dbd1aedad',
      AUDIT/'terminal-observation.json':'262108c8cf4aebf766cdd8a0cacc33c3fefbfb0e190a65592d23e0978e8a7abc',
      LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()


def check_pins():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    for audit,status in ((AUDIT,'PASS_INDEPENDENT_THIRTEEN_MODEL_VIEW_AUDIT'),):
        obs=json.loads((audit/'terminal-observation.json').read_text());check=json.loads((audit/'CHECK.json').read_text())
        if obs.get('audit_observed_exit_code')!=0 or obs.get('receipt_sha256')!=PINS[audit/'CHECK.json'] or check.get('status')!=status:
            raise ValueError(('invalid parent audit',str(audit)))


def verify_parents():
    records=[]
    for audit,status in ((AUDIT,'PASS_INDEPENDENT_THIRTEEN_MODEL_VIEW_AUDIT'),):
        p=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'audit.py')],text=True,capture_output=True,timeout=180)
        if p.returncode or p.stderr:raise ValueError(('parent audit failed',str(audit),p.returncode,p.stdout,p.stderr))
        data=json.loads(p.stdout)
        if data.get('status')!=status:raise ValueError(('unexpected parent audit output',str(audit),data))
        records.append(data)
    return records


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-retained-norm-pair-'):
        raise ValueError('output must be a fresh /tmp/ipra-thirteen-retained-norm-pair-* directory')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    check_pins();before=verify_parents();out.mkdir();runs=[]
    for label in ('author','peer'):
        root=out/label/'src';root.mkdir(parents=True);src=root/'Model69RetainedNorm.lean';obj=out/label/'Model69RetainedNorm.olean'
        shutil.copyfile(SOURCE,src)
        parent=PARENT/label;graph=GRAPH/label;lib=parent/'lib'
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
                env.pop(key,None)
        env['LEAN_PATH']=':'.join(map(str,(parent,graph,lib,PACKAGE)))
        cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        p=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=180);output=p.stdout+p.stderr
        reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
        if p.returncode or p.stderr or 'warning:' in output or 'error:' in output or 'sorryAx' in output or len(reports)!=9:
            raise ValueError(('unexpected Lean result',label,p.returncode,output))
        if any({x.strip() for x in report.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for report in reports):
            raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean'),str(parent/'Model69ViewMap.olean')}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:
            raise ValueError(('unexpected direct imports',label,deps.returncode,deps.stdout,deps.stderr))
        if H(src)!=PINS[SOURCE]:raise ValueError(('source drift',label))
        runs.append({'label':label,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'command':cmd,
                     'source_sha256':H(src),'object_sha256':H(obj),'axiom_reports':reports,
                     'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
    if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['stdout']!=runs[1]['stdout']:
        raise ValueError('sibling outputs differ')
    check_pins();after=verify_parents()
    if before!=after:raise ValueError('parent audit output changed')
    receipt={'status':'PASS_PAIRED_THIRTEEN_RETAINED_NORM','runs':runs,'parent_audits':after,
             'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
             'scope':'Actual positive current-2011 zero yields graph P=Q=1 for symbolic model ports with explicit beta, lowPort and highPort+beta equalities; K remains unrestricted. The inherited prefix has no complete axiom inventory; no full 69-operation converse, complete fixed-tuple binding, iPRA proof, phase-split2471 calibration, Foundation outer-wrapper exit, or complete package-transitive/dynamic audit is claimed.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_RETAINED_NORM',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
