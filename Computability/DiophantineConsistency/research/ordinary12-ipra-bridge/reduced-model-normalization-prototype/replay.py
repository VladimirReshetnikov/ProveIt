#!/usr/bin/env python3
"""Paired natural normalization suffix over matched induction parents."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent;BASE=HERE.parent
SOURCE=HERE/'ReducedNormNormalization.lean';PREV=BASE/'reduced-model-induction-prototype'
STATE=BASE/'reduced-model-state-prototype'
MEASURE=BASE/'reduced-model-nonzero-prototype'
AUDIT=HERE.parents[2]/'reviews/ordinary12-reduced-model-induction-independent-audit/CHECK.json'
DESCENT=BASE/'reduced-model-descent-prototype';SQUARE=BASE/'model-square-divisor-prototype'
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'
RUN=Path('/tmp/ipra-reduced-model-induction-pair-01')
PINS={SOURCE:'f56190851f7b567d41440b346f37bf8369881d992a052c618f17f9f38c893611',
 PREV/'replay.py':'9737d37410d3b33049362e5b25d02b20ad5fd40061c9d3e8b0f43d5910bfb4cb',
 PREV/'evidence/receipt.json':'298e528a7c814b129ff41e4551f5b18768d52c500bfff86322f430ad4af82199',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 AUDIT:'526dda635b7a17930d78602fa93d552f0bdc36335028f5456580506af16d8d4e'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def check_pins():
    for path,sha in PINS.items():
        if H(path)!=sha:raise ValueError(('input drift',str(path)))
    meta=json.loads((PREV/'evidence/receipt.json').read_text())
    if meta.get('status')!='PASS_PAIRED_REDUCED_MODEL_INTEGRAL_DENOMINATOR':raise ValueError('bad induction parent')
    for row in meta['runs']:
        label=row['label'];seed=RUN/label/'ReducedNormInduction.olean'
        inherited=RUN/label/'lib/DiophantineConsistency/ReducedNormState.olean'
        if row['compiler_exit'] or row['deps_exit'] or H(seed)!=row['object_sha256'] or H(inherited)!=row['seed_sha256']:
            raise ValueError(('induction parent drift',label))
    return meta

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True,type=Path);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-reduced-model-normalization-'):
        raise ValueError('use a fresh direct /tmp/ipra-reduced-model-normalization-* path')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    meta=check_pins();prev=load('induction_parent',PREV/'replay.py');state=load('state_parent',STATE/'replay.py');measure=load('measure_parent',MEASURE/'replay.py');descent=load('descent_parent',DESCENT/'replay.py')
    square=load('square_parent',SQUARE/'replay.py');monitor=load('model_monitor',MONITOR)
    prev.check_pins();state.check_pins();measure.check_pins();descent.check_pins();square.check_pins();before=square.compare_parent();out.mkdir();rows=[]
    for label in ('author','peer'):
        run=out/label;lib=run/'lib';root=run/'src';root.mkdir(parents=True)
        monitor.overlay(RUN/label/'lib',lib)
        seed=lib/'DiophantineConsistency/ReducedNormInduction.olean'
        if seed.exists() or seed.is_symlink():raise ValueError('seed path occupied')
        shutil.copyfile(RUN/label/'ReducedNormInduction.olean',seed)
        src=root/'DiophantineConsistency/ReducedNormNormalization.lean';src.parent.mkdir(parents=True);shutil.copyfile(SOURCE,src)
        obj=run/'ReducedNormNormalization.olean';log=run/'compiler.log';env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(square.PACKAGE)
        cmd=[str(square.LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text()
        reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",text,re.M)
        if code or reason or 'warning:' in text or 'sorryAx' in text or len(reports)!=1:
            raise ValueError(('compiler failure',label,code,reason,text[-8000:]))
        if any({x.strip() for x in r.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for r in reports):raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(square.LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(square.PACKAGE/'Init.olean'),str(seed)}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:
            raise ValueError(('unexpected imports',label,deps.returncode,deps.stdout,deps.stderr,sorted(expected)))
        parent_row=next(r for r in meta['runs'] if r['label']==label)
        if H(src)!=PINS[SOURCE] or H(seed)!=parent_row['object_sha256']:raise ValueError('copied input drift')
        rows.append({'label':label,'compiler_exit':code,'command':cmd,'object_sha256':H(obj),'source_sha256':H(src),
                     'seed_sha256':H(seed),'log_sha256':H(log),'stdout':text,'axiom_reports':reports,
                     'sampled_peak_rss_bytes':peak,'stop_reason':reason,'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
        print(label,'exit',code,'peak_RSS',peak,flush=True)
    if rows[0]['object_sha256']!=rows[1]['object_sha256'] or rows[0]['axiom_reports']!=rows[1]['axiom_reports']:
        raise ValueError('sibling objects or reports differ')
    if check_pins()!=meta:raise ValueError('induction parent changed')
    prev.check_pins();state.check_pins();measure.check_pins();descent.check_pins();square.check_pins();after=square.compare_parent()
    if before!=after:raise ValueError('70-source parent changed')
    result={'status':'PASS_PAIRED_REDUCED_MODEL_NATURAL_NORMALIZATION','runs':rows,'parent_comparison':after,
            'pins':{str(p):sha for p,sha in PINS.items()},
            'scope':'Paired model-level suffix over matched source-current and reduced-norm parents. Natural model numerator is divisible by positive denominator via gcd normalization and reduced integrality; no signed-fraction bridge, graph binding, iPRA proof, or package-transitive/dynamic ancestry audit.'}
    with (out/'receipt.json').open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_REDUCED_MODEL_NATURAL_NORMALIZATION',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
