#!/usr/bin/env python3
"""Paired scalar outer-data composition over audited growth/transport parents."""
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
SOURCE=HERE/'Model69Outer.lean'
GROWTHAUDIT=ROOT/'reviews/thirteen-model-parent-growth-independent-audit'
TRANSPORTAUDIT=ROOT/'reviews/thirteen-model-parent-transport-independent-audit'
GROWTH=Path('/tmp/ipra-thirteen-parent-growth-replay-01')
TRANSPORT=Path('/tmp/ipra-thirteen-parent-transport-replay-01')
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'4b3e5589fb6df55741cb84599faa34e247d6cdd65c790b5ed2e7d935b19bd133',
      GROWTHAUDIT/'audit.py':'138c95911fdc51f81663f8b6fd1b7b7c2e85867a8c870b6120f5e474b27f041e',
      GROWTHAUDIT/'CHECK.json':'09598aac3944f8d7bd2758954d1dea4cf1c9e9ccd3550f70b520d5a62a24a3b8',
      GROWTHAUDIT/'terminal-observation.json':'8125360db0b1a51abdb40ba6c1587633b3c8a3832f30ca66d5a87df1ebe727fb',
      TRANSPORTAUDIT/'audit.py':'31959a989b8c45ff6d93238246e382da6813137fb03a78385576f850dace5b7b',
      TRANSPORTAUDIT/'CHECK.json':'501224b4a459e8569b63f32d9a2ed5bf3d7a2fbd733003ad0e27f461528c5edc',
      TRANSPORTAUDIT/'terminal-observation.json':'288611ba0d8a7b6d2dfe3d8ae513321e116ceb8c2342da6c310e477aa5e87ca6',
      LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()


def check_pins():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    for audit,status in ((GROWTHAUDIT,'PASS_INDEPENDENT_THIRTEEN_PARENT_GROWTH_AUDIT'),
                         (TRANSPORTAUDIT,'PASS_INDEPENDENT_THIRTEEN_PARENT_TRANSPORT_AUDIT')):
        obs=json.loads((audit/'terminal-observation.json').read_text());check=json.loads((audit/'CHECK.json').read_text())
        if obs.get('audit_observed_exit_code')!=0 or obs.get('receipt_sha256')!=PINS[audit/'CHECK.json'] or check.get('status')!=status:
            raise ValueError(('invalid parent audit',str(audit)))


def verify_parents():
    records=[]
    for audit,status in ((GROWTHAUDIT,'PASS_INDEPENDENT_THIRTEEN_PARENT_GROWTH_AUDIT'),
                         (TRANSPORTAUDIT,'PASS_INDEPENDENT_THIRTEEN_PARENT_TRANSPORT_AUDIT')):
        p=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'audit.py')],text=True,capture_output=True,timeout=180)
        if p.returncode or p.stderr:raise ValueError(('parent audit failed',str(audit),p.returncode,p.stdout,p.stderr))
        data=json.loads(p.stdout)
        if data.get('status')!=status:raise ValueError(('unexpected parent audit output',str(audit),data))
        records.append(data)
    return records


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-parent-outer-pair-'):
        raise ValueError('output must be a fresh /tmp/ipra-thirteen-parent-outer-pair-* directory')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    check_pins();before=verify_parents();out.mkdir();runs=[]
    for label in ('author','peer'):
        root=out/label/'src';root.mkdir(parents=True);src=root/'Model69Outer.lean';obj=out/label/'Model69Outer.olean'
        shutil.copyfile(SOURCE,src)
        growth=GROWTH/label;transport=TRANSPORT/label;lib=PAIR/label/'child-output/lib'
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
                env.pop(key,None)
        env['LEAN_PATH']=':'.join(map(str,(growth,transport,lib,PACKAGE)))
        cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        p=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=180);output=p.stdout+p.stderr
        reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
        if p.returncode or p.stderr or 'warning:' in output or 'error:' in output or 'sorryAx' in output or len(reports)!=1:
            raise ValueError(('unexpected Lean result',label,p.returncode,output))
        if {x.strip() for x in reports[0].split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:
            raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean'),str(growth/'Model69Growth.olean'),str(transport/'Model69Transport.olean'),str(lib/'DiophantineConsistency/ArithmeticPellFirstIndex.olean')}
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
    receipt={'status':'PASS_PAIRED_THIRTEEN_PARENT_OUTER','runs':runs,'parent_audits':after,
             'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
             'scope':'Two bounded model-level scalar composition suffixes over independently audited parent branches. No actual-zero extraction, rank-phase theorem, graph binding, iPRA proof, fixed-port calibration, Foundation outer-wrapper exit, or complete package-transitive/dynamic audit is claimed.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_PARENT_OUTER',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
