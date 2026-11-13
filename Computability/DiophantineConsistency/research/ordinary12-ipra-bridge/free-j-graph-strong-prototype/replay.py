#!/usr/bin/env python3
"""Paired strong-norm suffix over the audited graph-integrality join."""
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
SOURCE=HERE/'FreeJGraphStrong.lean';PREV=BASE/'free-j-graph-integrality-prototype'
MONITOR=BASE/'free-j-current-denominator-composition/replay.py';SQUARE=BASE/'model-square-divisor-prototype/replay.py'
AUDIT=HERE.parents[2]/'reviews/ordinary12-freej-graph-integrality-independent-audit/CHECK.json'
RUN=Path('/tmp/ipra-freej-graph-integrality-pair-01')
PINS={SOURCE:'5e8dd0b50d47864f8b786f1c77f5c9373dcc3f4e71f832e4809c56472a71e346',
 PREV/'replay.py':'2c453204d9d5d7aa9d8a432f6ba7d853969b1d594b7324d2cb53857fc3859dc9',
 PREV/'evidence/receipt.json':'61b12fb93bc50e43ee710b3bac6a1d40cb61f1af1a6fbe3f9861985a06d3dc9d',
 AUDIT:'f52064c6cd1fca7221f33c6a3720e667cd9da407d8419cee2a1953096fe104f4',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 SQUARE:'22606fd5754f2d90fb891dc487a314d668cd7515713981f4b9f2f22acbbc6c12'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def check_pins(prev,square):
    for path,sha in PINS.items():
        if H(path)!=sha:raise ValueError(('input drift',str(path)))
    meta=json.loads((PREV/'evidence/receipt.json').read_text())
    if meta.get('status')!='PASS_PAIRED_FREEJ_GRAPH_DIVISIBILITY' or len(meta['runs'])!=2:
        raise ValueError('bad graph integrality parent')
    graph,_=prev.check_inputs()
    for row in meta['runs']:
        label=row['label'];seed=RUN/label/'FreeJGraphIntegrality.olean';lib=RUN/label/'lib'
        if row['compiler_exit'] or row['deps_exit'] or H(seed)!=row['object_sha256']:
            raise ValueError(('graph integrality seed drift',label))
        for name,sha in row['joined_seed_sha256'].items():
            if H(lib/'DiophantineConsistency'/(name+'.olean'))!=sha:raise ValueError(('joined seed drift',label,name))
        for grow in graph['runs']:
            if grow['label']==label:
                obj=lib/(grow['module'].replace('.','/')+'.olean')
                if H(obj)!=grow['object_sha256']:raise ValueError(('graph suffix drift',label,grow['module']))
        state=json.loads((square.PAIR/label/'child-output/state.json').read_text())
        if len(state['records'])!=70:raise ValueError(('unexpected provider row count',label))
        for rec in state['records']:
            obj=lib/(rec['module'].replace('.','/')+'.olean')
            if H(obj)!=rec['object_sha256']:raise ValueError(('current provider drift',label,rec['module']))
    return meta

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True,type=Path);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-freej-graph-strong-'):
        raise ValueError('use a fresh direct /tmp/ipra-freej-graph-strong-* path')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    prev=load('graph_parent',PREV/'replay.py');square=load('square_parent',SQUARE);monitor=load('model_monitor',MONITOR)
    meta=check_pins(prev,square);square.check_pins();before=square.compare_parent();out.mkdir();rows=[]
    for label in ('author','peer'):
        run=out/label;lib=run/'lib';root=run/'src';root.mkdir(parents=True)
        monitor.overlay(RUN/label/'lib',lib)
        seed=lib/'DiophantineConsistency/FreeJGraphIntegrality.olean'
        if seed.exists() or seed.is_symlink():raise ValueError('seed path occupied')
        shutil.copyfile(RUN/label/'FreeJGraphIntegrality.olean',seed)
        src=root/'DiophantineConsistency/FreeJGraphStrong.lean';src.parent.mkdir(parents=True);shutil.copyfile(SOURCE,src)
        obj=run/'FreeJGraphStrong.olean';log=run/'compiler.log';env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(square.PACKAGE)
        cmd=[str(square.LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text()
        reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",text,re.M)
        if code or reason or 'warning:' in text or 'sorryAx' in text or len(reports)!=2:
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
    if check_pins(prev,square)!=meta:raise ValueError('graph parent changed')
    square.check_pins();after=square.compare_parent()
    if before!=after:raise ValueError('70-source parent changed')
    result={'status':'PASS_PAIRED_FREEJ_GRAPH_POSITIVE_STRONG','runs':rows,'parent_comparison':after,
            'pins':{str(p):sha for p,sha in PINS.items()},
            'scope':'Paired model-level suffix over audited graph-integrality join and matched source-current parents. No auxiliary-positive witness, final rank, compact44 calibration, object-level iPRA proof, or package-transitive/dynamic ancestry audit.'}
    with (out/'receipt.json').open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_FREEJ_GRAPH_POSITIVE_STRONG',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
