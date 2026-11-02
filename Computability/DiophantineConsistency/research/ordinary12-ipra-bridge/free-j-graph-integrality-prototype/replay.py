#!/usr/bin/env python3
"""Paired join of audited current-provider graph and signed-integrality suffixes."""
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
SOURCE=HERE/'FreeJGraphIntegrality.lean'
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'
GRAPH=BASE/'free-j-current-denominator-composition/evidence/receipt.json'
GRAPH_AUDIT=HERE.parents[2]/'reviews/ordinary12-current-denominator-independent-audit/CHECK.json'
SIGNED_AUDIT=HERE.parents[2]/'reviews/ordinary12-reduced-model-signed-independent-audit/CHECK.json'
SQUARE=BASE/'model-square-divisor-prototype/replay.py'
GRAPH_RUN=Path('/tmp/ipra-freej-current-denominator-rebuild-04')
SIGNED_RUN=Path('/tmp/ipra-reduced-model-signed-pair-01')
CHAIN=[
 ('ModelSquareDivisor','model-square-divisor-prototype/replay-receipt.json','b7ea669ad815d9012fbbcc2442488ee883e3197e9ca37b0dbd3cb6f366b548f7'),
 ('ReducedNormBounds','reduced-model-descent-prototype/evidence/receipt.json','2a3e44b6579798dd99557fcb050776fef12678479b24528b1f767b513e594742'),
 ('ReducedNormNext','reduced-model-nonzero-prototype/evidence/receipt.json','01af03ae511a9a94c65fb60d1d2a634dc1b502e18bcd6a9584296bdb2d14bedb'),
 ('ReducedNormState','reduced-model-state-prototype/evidence/receipt.json','81eac0378afbc0b9bfba3d84bfba86d54af1cdc196bf9135391c79778a8002ad'),
 ('ReducedNormInduction','reduced-model-induction-prototype/evidence/receipt.json','298e528a7c814b129ff41e4551f5b18768d52c500bfff86322f430ad4af82199'),
 ('ReducedNormNormalization','reduced-model-normalization-prototype/evidence/receipt.json','802096243e8d668abecaf1a59e9132a3f21b3db9bdde5f847ba1b97fb113aa65'),
 ('ReducedNormSigned','reduced-model-signed-prototype/evidence/receipt.json','576041dbd94d2aaa76a63ab4515164e6b783d106f9d92a3891c260c88eb8b30a')]
PINS={SOURCE:'8837d4f9d83f4b9500a99c5c2ed7cca521b4fd383362d1a660eea45fe2e3fd22',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 GRAPH:'a9517710d23a1576f04610ef00f3e16038086eed2956fddc2cd0cf76f006ef7b',
 GRAPH_AUDIT:'5c660c74ddd281fcfafbca9c993e0b53945f30d2322e5216a0f42e8e5d27ee16',
 SIGNED_AUDIT:'2f65a3ebbde03f2d894ee88608c41a2d83eb033f7e485d523e95bd71462de09d',
 SQUARE:'22606fd5754f2d90fb891dc487a314d668cd7515713981f4b9f2f22acbbc6c12'}
for _,rel,sha in CHAIN:PINS[BASE/rel]=sha
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def check_inputs():
    for path,sha in PINS.items():
        if H(path)!=sha:raise ValueError(('input drift',str(path)))
    graph=json.loads(GRAPH.read_text())
    if graph.get('status')!='PASS_PAIRED_CURRENT_DENOMINATOR_COMPOSITION' or len(graph['runs'])!=24:
        raise ValueError('unexpected graph parent')
    for row in graph['runs']:
        cmd=row['command'];src=Path(cmd[-3]);obj=Path(cmd[-1]);log=Path(row['log'])
        if row['exit'] or row['deps_exit'] or H(src)!=row['source_sha256'] or H(obj)!=row['object_sha256'] or H(log)!=row['log_sha256']:
            raise ValueError(('graph parent drift',row['label'],row['module']))
    chain={}
    for name,rel,_ in CHAIN:
        data=json.loads((BASE/rel).read_text());chain[name]=data
        if len(data['runs'])!=2:raise ValueError(('unexpected seed sibling count',name))
        for row in data['runs']:
            label=row['label'];src=(SIGNED_RUN/label/'ReducedNormSigned.olean' if name=='ReducedNormSigned' else SIGNED_RUN/label/'lib/DiophantineConsistency'/(name+'.olean'))
            if row.get('exit',row.get('compiler_exit'))!=0 or row['deps_exit']!=0 or H(src)!=row['object_sha256']:
                raise ValueError(('signed chain drift',name,label))
    return graph,chain

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True,type=Path);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-freej-graph-integrality-'):
        raise ValueError('use a fresh direct /tmp/ipra-freej-graph-integrality-* path')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    graph,chain=check_inputs();square=load('square_parent',SQUARE);monitor=load('model_monitor',MONITOR)
    square.check_pins();before=square.compare_parent();out.mkdir();rows=[]
    for label in ('author','peer'):
        run=out/label;lib=run/'lib';root=run/'src';root.mkdir(parents=True)
        monitor.overlay(GRAPH_RUN/label/'lib',lib)
        for name,_,_ in CHAIN:
            src=(SIGNED_RUN/label/'ReducedNormSigned.olean' if name=='ReducedNormSigned' else SIGNED_RUN/label/'lib/DiophantineConsistency'/(name+'.olean'))
            dst=lib/'DiophantineConsistency'/(name+'.olean')
            if dst.exists() or dst.is_symlink():raise ValueError(('suffix collision',str(dst)))
            shutil.copyfile(src,dst)
        src=root/'DiophantineConsistency/FreeJGraphIntegrality.lean';src.parent.mkdir(parents=True);shutil.copyfile(SOURCE,src)
        obj=run/'FreeJGraphIntegrality.olean';log=run/'compiler.log';env=os.environ.copy()
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
        expected={str(square.PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency/FreeJCurrentDenominator.olean'),str(lib/'DiophantineConsistency/ReducedNormSigned.olean')}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:
            raise ValueError(('unexpected imports',label,deps.returncode,deps.stdout,deps.stderr,sorted(expected)))
        if H(src)!=PINS[SOURCE]:raise ValueError('copied source drift')
        rows.append({'label':label,'compiler_exit':code,'command':cmd,'object_sha256':H(obj),'source_sha256':H(src),
                     'log_sha256':H(log),'stdout':text,'axiom_reports':reports,'sampled_peak_rss_bytes':peak,
                     'stop_reason':reason,'deps_exit':deps.returncode,'deps_stdout':deps.stdout,
                     'joined_seed_sha256':{name:H(lib/'DiophantineConsistency'/(name+'.olean')) for name,_,_ in CHAIN}})
        print(label,'exit',code,'peak_RSS',peak,flush=True)
    if rows[0]['object_sha256']!=rows[1]['object_sha256'] or rows[0]['axiom_reports']!=rows[1]['axiom_reports'] or rows[0]['joined_seed_sha256']!=rows[1]['joined_seed_sha256']:
        raise ValueError('sibling outputs differ')
    graph_after,chain_after=check_inputs();square.check_pins();after=square.compare_parent()
    if graph_after!=graph or chain_after!=chain or before!=after:raise ValueError('parent inputs changed')
    result={'status':'PASS_PAIRED_FREEJ_GRAPH_DIVISIBILITY','runs':rows,'parent_comparison':after,
            'pins':{str(p):sha for p,sha in PINS.items()},
            'scope':'Paired model-level join of separately audited suffixes over the same matched source-current 70-module provider; no ordinary strong norm, checker calibration, object-level iPRA proof, or package-transitive/dynamic ancestry audit.'}
    with (out/'receipt.json').open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_FREEJ_GRAPH_DIVISIBILITY',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
