#!/usr/bin/env python3
"""Paired ordinary-rank suffix over the audited auxiliary-witness parent."""
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
SOURCE=HERE/'FreeJOrdinaryRank.lean';PREV=BASE/'free-j-graph-auxiliary-prototype'
STRONG=BASE/'free-j-graph-strong-prototype/replay.py'
GRAPH=BASE/'free-j-graph-integrality-prototype/replay.py';SQUARE=BASE/'model-square-divisor-prototype/replay.py'
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'
AUDIT=HERE.parents[2]/'reviews/ordinary12-freej-graph-auxiliary-independent-audit/CHECK.json'
RUN=Path('/tmp/ipra-freej-graph-auxiliary-pair-01')
PINS={SOURCE:'1cbc9b564edff3d1c7fe8cbdbb292577cfe6acdb46e280d9983755d53f78e4fc',
 PREV/'replay.py':'a007729cd82c1c5500d10f0af0381c0118a0af27b50f01b54467fe46795ffbc1',
 PREV/'evidence/receipt.json':'db0dce9fb7f47c6d52c18789d717d126b175df14611d05cf9719cb17b85af5f6',
 AUDIT:'f7f557359dca73b583d7dff59db23cc743b59eb7a55c078b89e15ea1a031fe0c',
 STRONG:'1798ec9a9c6c420f096a03e8dd640dab7ea0b1ca79a40b22b4f872bd790e2486',
 GRAPH:'2c453204d9d5d7aa9d8a432f6ba7d853969b1d594b7324d2cb53857fc3859dc9',
 SQUARE:'22606fd5754f2d90fb891dc487a314d668cd7515713981f4b9f2f22acbbc6c12',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def check_pins(prev,strong,graph,square):
    for path,sha in PINS.items():
        if H(path)!=sha:raise ValueError(('input drift',str(path)))
    meta=json.loads((PREV/'evidence/receipt.json').read_text())
    if meta.get('status')!='PASS_PAIRED_FREEJ_GRAPH_POSITIVE_AUXILIARY' or len(meta['runs'])!=2:
        raise ValueError('bad positive auxiliary parent')
    grand=prev.check_pins(strong,graph,square)
    for row in meta['runs']:
        label=row['label'];seed=RUN/label/'FreeJGraphAuxiliary.olean';lib=RUN/label/'lib'
        if row['compiler_exit'] or row['deps_exit'] or H(seed)!=row['object_sha256']:
            raise ValueError(('auxiliary seed drift',label))
        graph_seed=lib/'DiophantineConsistency/FreeJGraphStrong.olean'
        if H(graph_seed)!=row['seed_sha256']:raise ValueError(('inherited graph seed drift',label))
        oldlib=prev.RUN/label/'lib'
        old={p.relative_to(oldlib) for p in oldlib.rglob('*.olean')}
        new={p.relative_to(lib) for p in lib.rglob('*.olean')}
        extra={Path('DiophantineConsistency/FreeJGraphStrong.olean')}
        if new!=old|extra:raise ValueError(('library object set drift',label,sorted(map(str,new^ (old|extra)))))
        for path in old:
            if H(lib/path)!=H(oldlib/path):raise ValueError(('inherited object drift',label,str(path)))
    return meta,grand

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True,type=Path);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-freej-ordinary-rank-'):
        raise ValueError('use a fresh direct /tmp/ipra-freej-ordinary-rank-* path')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    prev=load('auxiliary_parent',PREV/'replay.py');strong=load('strong_parent',STRONG);graph=load('graph_parent',GRAPH);square=load('square_parent',SQUARE);monitor=load('model_monitor',MONITOR)
    meta,grand=check_pins(prev,strong,graph,square);square.check_pins();before=square.compare_parent();out.mkdir();rows=[]
    for label in ('author','peer'):
        run=out/label;lib=run/'lib';root=run/'src';root.mkdir(parents=True)
        monitor.overlay(RUN/label/'lib',lib)
        seed=lib/'DiophantineConsistency/FreeJGraphAuxiliary.olean'
        if seed.exists() or seed.is_symlink():raise ValueError('seed path occupied')
        shutil.copyfile(RUN/label/'FreeJGraphAuxiliary.olean',seed)
        src=root/'DiophantineConsistency/FreeJOrdinaryRank.lean';src.parent.mkdir(parents=True);shutil.copyfile(SOURCE,src)
        obj=run/'FreeJOrdinaryRank.olean';log=run/'compiler.log';env=os.environ.copy()
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
        expected={str(square.PACKAGE/'Init.olean'),str(seed),str(lib/'DiophantineConsistency/ArithmeticPellIntegralSolution.olean')}
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
    if check_pins(prev,strong,graph,square)!=(meta,grand):raise ValueError('auxiliary parent changed')
    square.check_pins();after=square.compare_parent()
    if before!=after:raise ValueError('70-source parent changed')
    result={'status':'PASS_PAIRED_FREEJ_ORDINARY_RANK_INTERMEDIATE','runs':rows,'parent_comparison':after,
            'pins':{str(p):sha for p,sha in PINS.items()},
            'scope':'Paired model-level suffix over audited auxiliary-witness parent and matched source-current parents. Proves a positive ordinary Pell rank divisible by the main index; no exact rank equality, compact44 calibration, iPRA proof, or package-transitive/dynamic ancestry audit.'}
    with (out/'receipt.json').open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_FREEJ_ORDINARY_RANK_INTERMEDIATE',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
