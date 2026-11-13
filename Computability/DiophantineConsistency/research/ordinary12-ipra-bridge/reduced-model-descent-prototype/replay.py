#!/usr/bin/env python3
"""Paired model descent-step replay over audited source-current providers."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent
BASE=HERE.parent
SOURCE=HERE/'ReducedNormBounds.lean'
SQUARE=BASE/'model-square-divisor-prototype'
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'
AUDIT=HERE.parents[2]/'reviews/ordinary12-model-square-divisor-independent-audit/CHECK.json'
SQUARE_RUN=Path('/tmp/ipra-model-square-divisor-replay-46be-02')
PINS={
 SOURCE:'d50d9a57f8529046c6492604683fa6e29eab8cfa74ec5fb7a11ce6685e6bd96d',
 SQUARE/'replay-receipt.json':'b7ea669ad815d9012fbbcc2442488ee883e3197e9ca37b0dbd3cb6f366b548f7',
 SQUARE/'replay.py':'22606fd5754f2d90fb891dc487a314d668cd7515713981f4b9f2f22acbbc6c12',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 AUDIT:'513cbf379c6fcae6ff63d0da4d8d2db5fe3f23e2d2615986f71a03cd32392623',
}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def check_pins():
    for path,sha in PINS.items():
        if H(path)!=sha:raise ValueError(('input drift',str(path)))
    meta=json.loads((SQUARE/'replay-receipt.json').read_text())
    if meta.get('status')!='PASS_PAIRED_MODEL_SQUARE_DIVISOR':raise ValueError('bad square-divisor parent')
    for row in meta['runs']:
        obj=SQUARE_RUN/row['label']/'ModelSquareDivisor.olean'
        if row['exit']!=0 or row['deps_exit']!=0 or H(obj)!=row['object_sha256']:
            raise ValueError(('square-divisor seed drift',row['label']))
    return meta

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True,type=Path);args=ap.parse_args()
    out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-reduced-model-descent-'):
        raise ValueError('use a fresh direct /tmp/ipra-reduced-model-descent-* path')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    meta=check_pins()
    ps=importlib.util.spec_from_file_location('square_parent',SQUARE/'replay.py');parent=importlib.util.module_from_spec(ps);ps.loader.exec_module(parent)
    ms=importlib.util.spec_from_file_location('descent_monitor',MONITOR);monitor=importlib.util.module_from_spec(ms);ms.loader.exec_module(monitor)
    parent.check_pins();before=parent.compare_parent();out.mkdir();rows=[]
    for label in ('author','peer'):
        run=out/label;lib=run/'lib';root=run/'src';root.mkdir(parents=True)
        monitor.overlay(parent.PAIR/label/'child-output/lib',lib)
        seed=lib/'DiophantineConsistency/ModelSquareDivisor.olean'
        if seed.exists() or seed.is_symlink():raise ValueError('seed path occupied')
        shutil.copyfile(SQUARE_RUN/label/'ModelSquareDivisor.olean',seed)
        src=root/'DiophantineConsistency/ReducedNormBounds.lean';src.parent.mkdir(parents=True);shutil.copyfile(SOURCE,src)
        obj=run/'ReducedNormBounds.olean';log=run/'compiler.log'
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(parent.PACKAGE)
        cmd=[str(parent.LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        code,peak,reason=monitor.monitored(cmd,env,log)
        text=log.read_text();reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",text,re.M)
        if code or reason or 'warning:' in text or 'sorryAx' in text or len(reports)!=7:
            raise ValueError(('compiler failure',label,code,reason,text[-8000:]))
        if any({x.strip() for x in r.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for r in reports):raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(parent.LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(parent.PACKAGE/'Init.olean'),str(parent.PACKAGE/'Mathlib/Tactic/Linarith.olean'),str(seed),str(lib/'DiophantineConsistency/ModelDifferenceRing.olean')}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:
            raise ValueError(('unexpected imports',label,deps.returncode,deps.stdout,deps.stderr,sorted(expected)))
        if H(src)!=PINS[SOURCE] or H(seed)!=meta['runs'][0]['object_sha256']:raise ValueError('copied input drift')
        row={'label':label,'compiler_exit':code,'command':cmd,'object_sha256':H(obj),'source_sha256':H(src),
             'seed_sha256':H(seed),'log_sha256':H(log),'stdout':text,'axiom_reports':reports,
             'sampled_peak_rss_bytes':peak,'stop_reason':reason,'deps_exit':deps.returncode,'deps_stdout':deps.stdout}
        rows.append(row);print(label,'exit',code,'peak_RSS',peak,flush=True)
    if rows[0]['object_sha256']!=rows[1]['object_sha256'] or rows[0]['axiom_reports']!=rows[1]['axiom_reports']:
        raise ValueError('sibling objects or reports differ')
    if check_pins()!=meta:raise ValueError('square parent changed')
    parent.check_pins();after=parent.compare_parent()
    if before!=after:raise ValueError('70-source parent changed')
    result={'status':'PASS_PAIRED_REDUCED_MODEL_DESCENT_STEP','runs':rows,'parent_comparison':after,
            'pins':{str(p):sha for p,sha in PINS.items()},
            'scope':'Model-level paired suffix over matched source-current parents. No least-number descent, graph-to-reduced-norm binding, iPRA proof, or package-transitive/dynamic ancestry audit.'}
    with (out/'receipt.json').open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_REDUCED_MODEL_DESCENT_STEP',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
