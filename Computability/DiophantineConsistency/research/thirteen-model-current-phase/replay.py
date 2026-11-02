#!/usr/bin/env python3
"""Paired actual-zero rank phase over audited window/rank and phase parents."""
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
SOURCE=HERE/'Model69CurrentPhase.lean'
PREFIXAUDIT=ROOT/'reviews/thirteen-model-parent-window-pair-independent-audit'
OUTERAUDIT=ROOT/'reviews/thirteen-model-parent-phase-independent-audit'
PREFIX=Path('/tmp/ipra-thirteen-parent-window-pair-01')
OUTER=Path('/tmp/ipra-thirteen-parent-phase-replay-01')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'b9d32d43c44209f9fb29893d48c37094d81e9b8bdeaeb806daef05e5a3e227be',
      PREFIXAUDIT/'audit.py':'679a7680a3e4fbc3a7555bc1ba3a43b543d749311f08760a91ab24433539f4c1',
      PREFIXAUDIT/'CHECK.json':'4a358f8fd09fa3be38d32aa2314ad063406ea2d363f74d1a13f41dedcc3e0ec9',
      PREFIXAUDIT/'terminal-observation.json':'516750a20bddd6d87dc5ecd0bdcd904c6d74deb505b5b8b3c6f4ba111f7a2549',
      OUTERAUDIT/'audit.py':'d37f5dae92eaef498ace065912638dfa80778e55179382f000eb8b8a99a59ba2',
      OUTERAUDIT/'CHECK.json':'2e5692be17c5d7ff16d07706fab9408d3150d72ab7820a518fc89fba01c1e7ea',
      OUTERAUDIT/'terminal-observation.json':'af1a72acb7e904422852eea607eb128e68a8dba5f604cd374c2ce1f6bd3a4024',
      LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()


def check_pins():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    for audit,status in ((PREFIXAUDIT,'PASS_INDEPENDENT_24_MODULE_WINDOW_PAIR_AUDIT'),
                         (OUTERAUDIT,'PASS_INDEPENDENT_THIRTEEN_PARENT_PHASE_AUDIT')):
        obs=json.loads((audit/'terminal-observation.json').read_text());check=json.loads((audit/'CHECK.json').read_text())
        if obs.get('audit_observed_exit_code')!=0 or obs.get('receipt_sha256')!=PINS[audit/'CHECK.json'] or check.get('status')!=status:
            raise ValueError(('invalid parent audit',str(audit)))


def verify_parents():
    records=[]
    for audit,status in ((PREFIXAUDIT,'PASS_INDEPENDENT_24_MODULE_WINDOW_PAIR_AUDIT'),
                         (OUTERAUDIT,'PASS_INDEPENDENT_THIRTEEN_PARENT_PHASE_AUDIT')):
        p=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'audit.py')],text=True,capture_output=True,timeout=180)
        if p.returncode or p.stderr:raise ValueError(('parent audit failed',str(audit),p.returncode,p.stdout,p.stderr))
        data=json.loads(p.stdout)
        if data.get('status')!=status:raise ValueError(('unexpected parent audit output',str(audit),data))
        records.append(data)
    return records


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-current-phase-pair-'):
        raise ValueError('output must be a fresh /tmp/ipra-thirteen-current-phase-pair-* directory')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    check_pins();before=verify_parents();out.mkdir();runs=[]
    for label in ('author','peer'):
        root=out/label/'src';root.mkdir(parents=True);src=root/'Model69CurrentPhase.lean';obj=out/label/'Model69CurrentPhase.olean'
        shutil.copyfile(SOURCE,src)
        outer=OUTER/label;lib=PREFIX/label/'lib'
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
                env.pop(key,None)
        env['LEAN_PATH']=':'.join(map(str,(outer,lib,PACKAGE)))
        cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        p=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=180);output=p.stdout+p.stderr
        reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
        if p.returncode or p.stderr or 'warning:' in output or 'error:' in output or 'sorryAx' in output or len(reports)!=1:
            raise ValueError(('unexpected Lean result',label,p.returncode,output))
        if {x.strip() for x in reports[0].split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:
            raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean'),str(outer/'Model69Phase.olean'),str(lib/'DiophantineConsistency/ArithmeticWindowZero.olean'),str(lib/'DiophantineConsistency/ArithmeticRankForcing2011.olean')}
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
    receipt={'status':'PASS_PAIRED_THIRTEEN_CURRENT_PHASE','runs':runs,'parent_audits':after,
             'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
             'scope':'Two bounded model-level rank-phase callers for the actual current-2011 positive zero over independently audited parent branches. The window/rank and prefix audits have no complete axiom inventory. No 69-operation converse, difference-ring graph join, iPRA proof, phase-split2471 calibration, Foundation outer-wrapper exit, or complete package-transitive/dynamic audit is claimed.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_CURRENT_PHASE',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
