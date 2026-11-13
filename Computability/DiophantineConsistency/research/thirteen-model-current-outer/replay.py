#!/usr/bin/env python3
"""Paired actual-zero outer caller over audited scalar and current-prefix parents."""
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
SOURCE=HERE/'Model69CurrentOuter.lean'
PREFIXAUDIT=ROOT/'reviews/thirteen-model-parent-prefix-pair-independent-audit'
OUTERAUDIT=ROOT/'reviews/thirteen-model-parent-outer-independent-audit'
GROWTH=Path('/tmp/ipra-thirteen-parent-growth-replay-01')
TRANSPORT=Path('/tmp/ipra-thirteen-parent-transport-replay-01')
PREFIX=Path('/tmp/ipra-thirteen-parent-prefix-pair-01')
OUTER=Path('/tmp/ipra-thirteen-parent-outer-pair-01')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'c390faa06b821e5e0c3b8b96bf898fbf3ac8230bb0dc0e04cc6b2520cf566441',
      PREFIXAUDIT/'audit.py':'c05d6ce8e72e3ca95c0683c9dbca42c99522165b5f0ae50e7af091a4938734fd',
      PREFIXAUDIT/'CHECK.json':'dcca147c2f1aea76821ae7089da6dc1ceb1096dbdbbb33429d7c50ce40a1945d',
      PREFIXAUDIT/'terminal-observation.json':'4002b74efe53c32e805f294342353780af65d6c397132e07da17f187661834d3',
      OUTERAUDIT/'audit.py':'a5c752d6882174162f75617616e013166b91a55c3310dc56b5d6bc81f5f36734',
      OUTERAUDIT/'CHECK.json':'f5dc903d2fe78878ca53468acbb9a5a4466c7420624fbe68f7ea983e8eaeedfa',
      OUTERAUDIT/'terminal-observation.json':'ba196d38dd78848d0bf98c44773b184ffd2bd1c876225f86e09b7566c3503d2f',
      LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()


def check_pins():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    for audit,status in ((PREFIXAUDIT,'PASS_INDEPENDENT_20_MODULE_PREFIX_PAIR_AUDIT'),
                         (OUTERAUDIT,'PASS_INDEPENDENT_THIRTEEN_PARENT_OUTER_AUDIT')):
        obs=json.loads((audit/'terminal-observation.json').read_text());check=json.loads((audit/'CHECK.json').read_text())
        if obs.get('audit_observed_exit_code')!=0 or obs.get('receipt_sha256')!=PINS[audit/'CHECK.json'] or check.get('status')!=status:
            raise ValueError(('invalid parent audit',str(audit)))


def verify_parents():
    records=[]
    for audit,status in ((PREFIXAUDIT,'PASS_INDEPENDENT_20_MODULE_PREFIX_PAIR_AUDIT'),
                         (OUTERAUDIT,'PASS_INDEPENDENT_THIRTEEN_PARENT_OUTER_AUDIT')):
        p=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'audit.py')],text=True,capture_output=True,timeout=180)
        if p.returncode or p.stderr:raise ValueError(('parent audit failed',str(audit),p.returncode,p.stdout,p.stderr))
        data=json.loads(p.stdout)
        if data.get('status')!=status:raise ValueError(('unexpected parent audit output',str(audit),data))
        records.append(data)
    return records


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-current-outer-pair-'):
        raise ValueError('output must be a fresh /tmp/ipra-thirteen-current-outer-pair-* directory')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    check_pins();before=verify_parents();out.mkdir();runs=[]
    for label in ('author','peer'):
        root=out/label/'src';root.mkdir(parents=True);src=root/'Model69CurrentOuter.lean';obj=out/label/'Model69CurrentOuter.olean'
        shutil.copyfile(SOURCE,src)
        growth=GROWTH/label;transport=TRANSPORT/label;outer=OUTER/label;lib=PREFIX/label/'lib'
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
                env.pop(key,None)
        env['LEAN_PATH']=':'.join(map(str,(outer,growth,transport,lib,PACKAGE)))
        cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        p=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=180);output=p.stdout+p.stderr
        reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
        if p.returncode or p.stderr or 'warning:' in output or 'error:' in output or 'sorryAx' in output or len(reports)!=1:
            raise ValueError(('unexpected Lean result',label,p.returncode,output))
        if {x.strip() for x in reports[0].split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:
            raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean'),str(outer/'Model69Outer.olean'),str(lib/'DiophantineConsistency/ArithmeticHalfBinomial2011.olean')}
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
    receipt={'status':'PASS_PAIRED_THIRTEEN_CURRENT_OUTER','runs':runs,'parent_audits':after,
             'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
             'scope':'Two bounded model-level current-2011 actual-zero suffixes over independently audited parent branches. The prefix audit has no complete axiom inventory; no rank-phase theorem, difference-ring graph binding, iPRA proof, phase-split2471 calibration, Foundation outer-wrapper exit, or complete package-transitive/dynamic audit is claimed.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_CURRENT_OUTER',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
