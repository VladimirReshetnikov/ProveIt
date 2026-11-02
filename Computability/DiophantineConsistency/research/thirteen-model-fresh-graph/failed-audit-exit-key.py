#!/usr/bin/env python3
"""Paired actual-zero to current shifted 69-literal proof over four audited branches."""
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
SOURCE=HERE/'Model69FreshNorms.lean'
AUDITS={
 'thirteen-model-current-outer-independent-audit':('PASS_INDEPENDENT_THIRTEEN_CURRENT_OUTER_AUDIT','4ff4a0708b924ab8e336c94c4a4e263697327ea4a2c1d856d1470c39c001ff65','a36146077da97251e8e93e6685ae929e686de7e48974f70a1dc1ac35bc24b92d','3ce968f215ef3e6217a74bc0034b97d135db7a4cf4e4f12fbbe6b9f65ee4aecc'),
 'thirteen-model-current-phase-independent-audit':('PASS_INDEPENDENT_THIRTEEN_CURRENT_PHASE_AUDIT','52a3f594608007c49da26cfbb9e8f667950bd0e1c5e6266be31a830e674ee932','aeb4d4de2a92b557b3dc0f1f13411636b937191eb6c358cce3e04c74bebbb890','a8b26eb6358a0dc12e960b2db8535343da72e372119a3e4181626708e7d17d3a'),
 'thirteen-model-retained-norm-independent-audit':('PASS_INDEPENDENT_THIRTEEN_RETAINED_NORM_AUDIT','01a90bf84c7a211b41e78eef963375f75c83abd5f5e2a532eb467cf7fff681ae','893b128a65f44f8d39f3e105aac98bc7f323aa8ea9e2a135492cdfa5591da370','82e48be5454c9f3231508a56cf800d7b0ccd82573f60327d5ff8db2964bc1295'),
 'thirteen-model-fresh-private-independent-audit':('PASS_INDEPENDENT_THIRTEEN_FRESH_PRIVATE_AUDIT','55affda58bb6286fb34fa082a64a87498ef26d96d928aececc90dcdeec09dd33','d447b7fefa723d836ad62211c6aa20a5fdd756b90ff5755a15d9785569d5538e','212a13bedcec0337cf65538d03b028d5503c36a7f85335f11a31357dcd31c2d2')}
VIEW=Path('/tmp/ipra-thirteen-model-view-pair-01')
FRESH=Path('/tmp/ipra-thirteen-fresh-private-pair-01')
PARENTS=[Path('/tmp')/name for name in ('ipra-thirteen-current-outer-pair-01','ipra-thirteen-current-phase-pair-01','ipra-thirteen-parent-outer-pair-01','ipra-thirteen-parent-growth-replay-01','ipra-thirteen-parent-transport-replay-01','ipra-thirteen-parent-phase-replay-01','ipra-thirteen-retained-norm-pair-01','ipra-thirteen-model-view-pair-01','ipra-thirteen-graph-cut-pair-01')]
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
SOURCE_HASH='815d0304371e78aa4916d657a8e26857ae0faeefab74a524c5a56197c5c966d8'
LEAN_HASH='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
EXPECTED_ADDITIONS={'ArithmeticOddOrdinateResidue.olean','ArithmeticPellAuxiliarySeed.olean','ArithmeticPellPigeonhole.olean','ArithmeticPellSquaredSeed.olean','DiscreteOrderedRingFacts.olean','ModelArithmetic.olean','ModelBAuxiliary.olean','ModelBFreshPrivate.olean','ModelBNegativeResidue.olean','ModelBPositiveCarrier.olean','ModelBSeed.olean'}


def check_pins():
    if H(SOURCE)!=SOURCE_HASH or H(LEAN)!=LEAN_HASH:raise ValueError('source or Lean drift')
    for name,(status,receipt,script,terminal) in AUDITS.items():
        p=BASE/'reviews'/name
        if H(p/'CHECK.json')!=receipt or H(p/'audit.py')!=script or H(p/'terminal-observation.json')!=terminal:
            raise ValueError(('audit input drift',name))
        r=json.loads((p/'CHECK.json').read_text());o=json.loads((p/'terminal-observation.json').read_text())
        if r.get('status')!=status or o.get('audit_observed_exit_code')!=0 or o.get('receipt_sha256')!=receipt:
            raise ValueError(('audit observation',name))


def verify_audits():
    records=[]
    for name,(status,_,_,_) in AUDITS.items():
        script=BASE/'reviews'/name/'audit.py'
        p=subprocess.run([sys.executable,'-I','-S','-B',str(script)],text=True,capture_output=True,timeout=240)
        if p.returncode or p.stderr:raise ValueError(('audit failed',name,p.returncode,p.stdout,p.stderr))
        data=json.loads(p.stdout)
        if data.get('status')!=status:raise ValueError(('audit status',name,data))
        records.append(data)
    return records


def merged_overlay(base,fresh,lib):
    for current,dirs,files in os.walk(base,followlinks=False):
        current=Path(current);out=lib/current.relative_to(base);out.mkdir(parents=True,exist_ok=True)
        for d in list(dirs):
            p=current/d
            if p.is_symlink():(out/d).symlink_to(p);dirs.remove(d)
        for f in files:(out/f).symlink_to(current/f)
    matched={};added={}
    for p in (fresh/'DiophantineConsistency').glob('*.olean'):
        q=lib/'DiophantineConsistency'/p.name
        if os.path.lexists(q):
            if not q.is_file() or H(q)!=H(p):raise ValueError(('project collision',str(p)))
            matched[p.name]=H(p)
        else:
            q.symlink_to(p);added[p.name]=H(p)
    if len(matched)!=65 or set(added)!=EXPECTED_ADDITIONS:
        raise ValueError(('unexpected fresh join coverage',matched.keys(),added.keys()))
    return matched,added


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-fresh-graph-pair-'):
        raise ValueError('output must be a fresh direct /tmp/ipra-thirteen-fresh-graph-pair-* directory')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    check_pins();before=verify_audits();out.mkdir();runs=[]
    for label in ('author','peer'):
        run=out/label;root=run/'src';root.mkdir(parents=True);src=root/'Model69FreshNorms.lean';obj=run/'Model69FreshNorms.olean'
        shutil.copyfile(SOURCE,src);lib=run/'lib'
        matched,added=merged_overlay(VIEW/label/'lib',FRESH/label/'lib',lib)
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
                env.pop(key,None)
        env['LEAN_PATH']=':'.join(map(str,[*(p/label for p in PARENTS),lib,PACKAGE]))
        cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        p=subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=180);output=p.stdout+p.stderr
        reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
        if p.returncode or p.stderr or 'warning:' in output or 'error:' in output or 'sorryAx' in output or len(reports)!=7:
            raise ValueError(('unexpected Lean result',label,p.returncode,output))
        if any({x.strip() for x in report.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for report in reports):
            raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency/ModelBFreshPrivate.olean'),str(lib/'DiophantineConsistency/Thirteen69Cuts.olean'),str(PARENTS[6]/label/'Model69RetainedNorm.olean'),str(PARENTS[0]/label/'Model69CurrentOuter.olean'),str(PARENTS[1]/label/'Model69CurrentPhase.olean')}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:
            raise ValueError(('unexpected direct imports',label,deps.returncode,deps.stdout,deps.stderr))
        if H(src)!=SOURCE_HASH:raise ValueError(('source drift',label))
        runs.append({'label':label,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'command':cmd,'source_sha256':H(src),'object_sha256':H(obj),'axiom_reports':reports,'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'matched_project_objects':matched,'added_fresh_objects':added})
    if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['stdout']!=runs[1]['stdout']:
        raise ValueError('sibling outputs differ')
    check_pins();after=verify_audits()
    if before!=after:raise ValueError('parent audit output changed')
    receipt={'status':'PASS_PAIRED_THIRTEEN_FRESH_GRAPH','runs':runs,'parent_audits':after,'source_sha256':SOURCE_HASH,'lean_sha256':LEAN_HASH,
             'scope':'Actual positive current-2011 parent zero yields a zero of the exact shifted 69-node 2011 literal, for symbolic ports with four explicit 2011-value equalities. No no-port-premise specialization, opposite implication, iPRA proof, phase-split2471 calibration, Foundation outer-wrapper exit, complete axiom inventory for inherited prefix/window, or complete package-transitive/dynamic audit is claimed.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_FRESH_GRAPH',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
