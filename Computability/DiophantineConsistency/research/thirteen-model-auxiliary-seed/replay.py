#!/usr/bin/env python3
"""Guarded paired model-auxiliary replay over the audited strong-seed pair."""
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
SOURCE=HERE/'ModelBAuxiliary.lean'
SQUARED=ROOT/'Lean/DiophantineConsistency/ArithmeticPellSquaredSeed.lean'
AUXILIARY=ROOT/'Lean/DiophantineConsistency/ArithmeticPellAuxiliarySeed.lean'
BASE=ROOT/'research/thirteen-model-strong-seed'
AUDIT=ROOT/'reviews/thirteen-model-strong-seed-independent-audit'
STRONG=Path('/tmp/ipra-thirteen-strong-seed-pair-01')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'b0dcb4f10d58737d380219b1347d5785be38fceea495a68d703541d282d13f78',
      SQUARED:'cb9ebc4a3e3477a1eb672d9ed4665107b4ea5d33e650c9d1a0d3889ce7dfeb05',
      AUXILIARY:'c20a64d1587b74dc7f18c208ba6f96052cbcfbf29da8c0e2567551055501f773',
      BASE/'replay-receipt.json':'9faa32f1c6715ffd6fd5a84330d46c545ad8c8aea3261c64c009144e841501f7',
      AUDIT/'audit.py':'a3fe64729eb226c095477d2a213d97d1aa78ad0dca2ed5b7d75df2922e3a600b',
      AUDIT/'CHECK.json':'5f57f5bbb21646000f020480c2d87749e464361453be34107e530420ca9d5362',
      LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()


def check_pins():
    for p,digest in PINS.items():
        if H(p)!=digest:raise ValueError(('fixed input drift',str(p)))
    observation=json.loads((AUDIT/'terminal-observation.json').read_text())
    check=json.loads((AUDIT/'CHECK.json').read_text())
    if observation.get('audit_observed_exit_code')!=0 or observation.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json']:
        raise ValueError('missing observed independent audit exit')
    if check.get('status')!='PASS_INDEPENDENT_THIRTEEN_MODEL_STRONG_SEED_AUDIT':
        raise ValueError('unexpected strong-seed audit status')


def verify_parent():
    result=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],text=True,capture_output=True,timeout=180)
    if result.returncode or result.stderr:raise ValueError(('parent audit failed',result.returncode,result.stdout,result.stderr))
    data=json.loads(result.stdout)
    if data.get('status')!='PASS_INDEPENDENT_THIRTEEN_MODEL_STRONG_SEED_AUDIT':
        raise ValueError(('unexpected parent audit output',data))
    return data


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-aux-seed-pair-'):
        raise ValueError('output must be a fresh /tmp/ipra-thirteen-aux-seed-pair-* directory')
    if out.exists() or out.is_symlink():raise ValueError('output already exists')
    check_pins();before=verify_parent();out.mkdir()
    runs=[]
    for label in ('author','peer'):
        run=out/label;root=run/'src';srcdir=root/'DiophantineConsistency';project=run/'lib/DiophantineConsistency'
        parent=STRONG/label/'lib'
        srcdir.mkdir(parents=True);project.mkdir(parents=True)
        (run/'lib/BusyBeaver').symlink_to(parent/'BusyBeaver',target_is_directory=True)
        links={}
        for source in (parent/'DiophantineConsistency').glob('*.olean'):
            link=project/source.name;link.symlink_to(source);links[str(link)]=H(source)
        if len(links)!=66:raise ValueError(('unexpected parent link count',label,len(links)))
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
                env.pop(key,None)
        env['LEAN_PATH']=str(run/'lib')+':'+str(PACKAGE)
        row={'label':label,'modules':[]}
        for source in (SQUARED,AUXILIARY,SOURCE):
            src=srcdir/source.name;obj=project/(source.stem+'.olean')
            if obj.exists() or obj.is_symlink():raise ValueError(('unintended inherited object',str(obj)))
            shutil.copyfile(source,src)
            cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
            result=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=240)
            output=result.stdout+result.stderr
            if result.returncode or result.stderr or 'error:' in output or 'warning:' in output or 'sorryAx' in output or 'admit' in output:
                raise ValueError(('Lean failed or unexpected output',label,source.name,result.returncode,output))
            reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
            if source==SOURCE:
                if len(reports)!=1 or {x.strip() for x in reports[0].split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:
                    raise ValueError(('unexpected axiom report',label,reports,output))
            elif reports:
                raise ValueError(('unexpected dependency reports',label,reports))
            deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
            if source==SQUARED:expected={str(PACKAGE/'Init.olean'),str(project/'ArithmeticPellPeriodicity.olean')}
            elif source==AUXILIARY:expected={str(PACKAGE/'Init.olean'),str(project/'ArithmeticPellSquaredSeed.olean'),str(project/'ArithmeticPellHalfIndex.olean')}
            else:expected={str(PACKAGE/'Init.olean'),str(project/'ModelBSeed.olean'),str(project/'ArithmeticPellAuxiliarySeed.olean')}
            if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:
                raise ValueError(('unexpected direct imports',label,source.name,deps.returncode,deps.stdout,deps.stderr))
            if H(src)!=PINS[source]:raise ValueError(('copied source drift',label,source.name))
            row['modules'].append({'name':source.stem,'exit':result.returncode,'stdout':result.stdout,'stderr':result.stderr,
                                   'source_sha256':H(src),'object_sha256':H(obj),'axiom_reports':reports,
                                   'command':cmd,'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
        for link,digest in links.items():
            if not Path(link).is_symlink() or H(link)!=digest:raise ValueError(('parent link drift',link))
        row['parent_links_sha256']=links;runs.append(row)
    if [m['object_sha256'] for m in runs[0]['modules']] != [m['object_sha256'] for m in runs[1]['modules']]:
        raise ValueError('suffix objects do not match')
    if runs[0]['modules'][2]['stdout']!=runs[1]['modules'][2]['stdout']:
        raise ValueError('auxiliary seed axiom reports do not match')
    check_pins();after=verify_parent()
    if before!=after:raise ValueError('parent audit output changed')
    receipt={'status':'PASS_PAIRED_THIRTEEN_AUXILIARY_SEED','runs':runs,'parent_audit':after,
             'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
             'scope':'Two bounded model-level suffix compilations over the independently audited matched b*c² seed pair. No 13-variable converse, graph transport, iPRA proof, fixed-port calibration, Foundation outer-wrapper exit, or full package-transitive/dynamic audit is claimed.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_AUXILIARY_SEED',H(out/'receipt.json'),flush=True)

if __name__=='__main__':main()
