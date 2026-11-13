#!/usr/bin/env python3
"""Paired exact carrier-index suffix over the audited ordinary-rank parent."""
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
SOURCE=HERE/'FreeJExactOrdinary.lean';PREV=BASE/'free-j-ordinary-rank-prototype'
AUX=BASE/'free-j-graph-auxiliary-prototype/replay.py'
STRONG=BASE/'free-j-graph-strong-prototype/replay.py'
GRAPH=BASE/'free-j-graph-integrality-prototype/replay.py';SQUARE=BASE/'model-square-divisor-prototype/replay.py'
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'
AUDIT=HERE.parents[2]/'reviews/ordinary12-freej-ordinary-rank-independent-audit/CHECK.json'
RUN=Path('/tmp/ipra-freej-ordinary-rank-pair-01')
PINS={SOURCE:'f132220a2a5cc38c73858ddc3b7cf943567199de5ab13cbcdec8126f232d7049',
 PREV/'replay.py':'ff32358951b8f32ea9eda9d2cff882f44c645984e8d0d95fb55830ee6f705738',
 PREV/'evidence/receipt.json':'fc8653e042d8a04a0a304820251d9315f43360c915d31116368cd76261a23ee6',
 AUDIT:'76117c3b55df96ae16ff4074d76687c9ffea58ad965b2e05f5db017bb88ad976',
 AUX:'a007729cd82c1c5500d10f0af0381c0118a0af27b50f01b54467fe46795ffbc1',
 STRONG:'1798ec9a9c6c420f096a03e8dd640dab7ea0b1ca79a40b22b4f872bd790e2486',
 GRAPH:'2c453204d9d5d7aa9d8a432f6ba7d853969b1d594b7324d2cb53857fc3859dc9',
 SQUARE:'22606fd5754f2d90fb891dc487a314d668cd7515713981f4b9f2f22acbbc6c12',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def check_pins(prev,aux,strong,graph,square):
    for path,sha in PINS.items():
        if H(path)!=sha:raise ValueError(('input drift',str(path)))
    meta=json.loads((PREV/'evidence/receipt.json').read_text())
    if meta.get('status')!='PASS_PAIRED_FREEJ_ORDINARY_RANK_INTERMEDIATE' or len(meta['runs'])!=2:
        raise ValueError('bad ordinary rank parent')
    grand=prev.check_pins(aux,strong,graph,square)
    for row in meta['runs']:
        label=row['label'];seed=RUN/label/'FreeJOrdinaryRank.olean';lib=RUN/label/'lib'
        if row['compiler_exit'] or row['deps_exit'] or H(seed)!=row['object_sha256']:
            raise ValueError(('ordinary rank seed drift',label))
        oldlib=prev.RUN/label/'lib'
        old={p.relative_to(oldlib) for p in oldlib.rglob('*.olean')}
        new={p.relative_to(lib) for p in lib.rglob('*.olean')}
        extra={Path('DiophantineConsistency/FreeJGraphAuxiliary.olean')}
        if new!=old|extra:raise ValueError(('library object set drift',label,sorted(map(str,new^(old|extra)))))
        for path in old:
            if H(lib/path)!=H(oldlib/path):raise ValueError(('inherited object drift',label,str(path)))
        if H(lib/next(iter(extra)))!=row['seed_sha256']:raise ValueError(('auxiliary seed drift',label))
    return meta,grand

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True,type=Path);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-freej-exact-ordinary-'):
        raise ValueError('use a fresh direct /tmp/ipra-freej-exact-ordinary-* path')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    prev=load('rank_parent',PREV/'replay.py');aux=load('aux_parent',AUX);strong=load('strong_parent',STRONG);graph=load('graph_parent',GRAPH);square=load('square_parent',SQUARE);monitor=load('model_monitor',MONITOR)
    meta,grand=check_pins(prev,aux,strong,graph,square);square.check_pins();before=square.compare_parent();out.mkdir();rows=[]
    for label in ('author','peer'):
        run=out/label;lib=run/'lib';root=run/'src';root.mkdir(parents=True)
        monitor.overlay(RUN/label/'lib',lib)
        seed=lib/'DiophantineConsistency/FreeJOrdinaryRank.olean'
        if seed.exists() or seed.is_symlink():raise ValueError('seed path occupied')
        shutil.copyfile(RUN/label/'FreeJOrdinaryRank.olean',seed)
        src=root/'DiophantineConsistency/FreeJExactOrdinary.lean';src.parent.mkdir(parents=True);shutil.copyfile(SOURCE,src)
        obj=run/'FreeJExactOrdinary.olean';log=run/'compiler.log';env=os.environ.copy()
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
        expected={str(square.PACKAGE/'Init.olean'),str(seed),str(lib/'DiophantineConsistency/ArithmeticPellResidueAux.olean')}
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
    if check_pins(prev,aux,strong,graph,square)!=(meta,grand):raise ValueError('rank parent changed')
    square.check_pins();after=square.compare_parent()
    if before!=after:raise ValueError('70-source parent changed')
    result={'status':'PASS_PAIRED_FREEJ_EXACT_ORDINARY_INDEX','runs':rows,'parent_comparison':after,
            'pins':{str(p):sha for p,sha in PINS.items()},
            'scope':'Conditional model-level exact main-carrier index and first-index equality; not f-exponent equality, compact44 calibration, iPRA proof, or package-transitive/dynamic ancestry audit.'}
    with (out/'receipt.json').open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_FREEJ_EXACT_ORDINARY_INDEX',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
