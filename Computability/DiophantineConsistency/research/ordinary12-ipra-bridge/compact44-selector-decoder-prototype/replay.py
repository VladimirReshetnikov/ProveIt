#!/usr/bin/env python3
"""Paired finite selector/copy decoder over three audited model parents."""
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
HERE=Path(__file__).resolve().parent;BASE=HERE.parent;ROOT=HERE.parents[2]
SOURCE=HERE/'CompactSelectorDecoder.lean'
DIV=BASE/'compact44-selector-div-prototype';COPY=BASE/'compact44-copy-prototype';SUM=BASE/'compact44-selector-sum-prototype'
DIVAUDIT=ROOT/'reviews/compact44-selector-div-independent-audit/CHECK.json'
COPYAUDIT=ROOT/'reviews/compact44-copy-independent-audit/CHECK.json'
SUMAUDIT=ROOT/'reviews/compact44-selector-sum-independent-audit/CHECK.json'
DIVRUN=Path('/tmp/ipra-compact-selector-div-pair-01');COPYRUN=Path('/tmp/ipra-compact-copy-pair-01');SUMRUN=Path('/tmp/ipra-compact-selector-sum-pair-01')
PREFIX=Path('/tmp/ipra-thirteen-parent-window-pair-01')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'96ba4a6ca5855ec86698b1f7fb2fecf4deeeb4fe5df04bb923cc0203242fe970',
 DIV/'replay.py':'869b512560dd855e110186f3e5ec6074bd304f38bd40d61eddd1aa3de3f0a241',DIV/'evidence/receipt.json':'784ad1bd572ca6da2d457dd2e7a726650af9eae767ff55ce5e153bf0ce2d0d37',DIVAUDIT:'11f1729d1dfce570819198a6e2abccb4cf64df4a3f801a11570e74736efc575c',
 COPY/'replay.py':'e191d48c162af2d30d7136045c2a4e56c92b0e8806dbd71ece9d32b6f832eaa6',COPY/'evidence/receipt.json':'92b2822864ae357cbeed9daa14b795edf891b5e0f80f5156c4bc087b87ac1be4',COPYAUDIT:'2be7111fe2d8423681bf473e50a40f3738e4c2a75aa6cf3ed98681dd88e80bc2',
 SUM/'replay.py':'1f53a3b5658ece60462351c08295e101501475a64dd517e1fa468c59c7c751ef',SUM/'evidence/receipt.json':'5a06980410fcf4f0305e4f9f1c5a9ba51b399ebe0bd93a99ea80722d84f52063',SUMAUDIT:'b264e7f68896ecba2564ea62344958b5b51d3e47bb1ecade9b7cc3570d8f125d',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def verify_parents(div,copy,summ):
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    for mod in (div,copy,summ):mod.check_pins()
    checks=[mod.verify_parent() for mod in (div,copy,summ)]
    if not checks[0]==checks[1]==checks[2]:raise ValueError('parents report different window provider')
    div.check_selector()
    receipts=[]
    for directory,run,module,status in ((DIV,DIVRUN,'CompactSelectorDiv','PASS_PAIRED_COMPACT_SELECTOR_DIV'),(COPY,COPYRUN,'CompactCopy','PASS_PAIRED_COMPACT_COPY_CASES'),(SUM,SUMRUN,'CompactSelectorSum','PASS_PAIRED_COMPACT_SELECTOR_SUM')):
        meta=json.loads((directory/'evidence/receipt.json').read_text())
        if meta.get('status')!=status or len(meta['runs'])!=2:raise ValueError(('bad parent receipt',module))
        for row in meta['runs']:
            if row['compiler_exit'] or row['deps_exit'] or H(run/row['label']/(module+'.olean'))!=row['object_sha256']:raise ValueError(('parent seed drift',module,row['label']))
        receipts.append(meta)
    for label in ('author','peer'):
        original=PREFIX/label/'lib';branch=DIVRUN/label/'lib'
        a={p.relative_to(original) for p in original.rglob('*.olean')};b={p.relative_to(branch) for p in branch.rglob('*.olean')}
        extra=Path('DiophantineConsistency/CompactSelector.olean')
        if b!=a|{extra}:raise ValueError(('div parent object set drift',label))
        for p in a:
            if H(original/p)!=H(branch/p):raise ValueError(('inherited object drift',label,str(p)))
        row=next(r for r in receipts[0]['runs'] if r['label']==label)
        if H(branch/extra)!=row['seed_sha256']:raise ValueError(('selector seed drift',label))
    return checks[0],receipts

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-selector-decoder-pair-'):raise ValueError('use a fresh direct /tmp/ipra-compact-selector-decoder-pair-* path')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    div=load('div_parent',DIV/'replay.py');copy=load('copy_parent',COPY/'replay.py');summ=load('sum_parent',SUM/'replay.py');monitor=load('model_monitor',MONITOR)
    before,metas=verify_parents(div,copy,summ);out.mkdir();runs=[]
    for label in ('author','peer'):
        run=out/label;root=run/'src';root.mkdir(parents=True);src=root/'CompactSelectorDecoder.lean';obj=run/'CompactSelectorDecoder.olean';log=run/'compiler.log'
        shutil.copyfile(SOURCE,src);lib=run/'lib';monitor.overlay(DIVRUN/label/'lib',lib)
        seed_hashes={}
        for runpath,module,meta in ((DIVRUN,'CompactSelectorDiv',metas[0]),(COPYRUN,'CompactCopy',metas[1]),(SUMRUN,'CompactSelectorSum',metas[2])):
            seed=lib/'DiophantineConsistency'/(module+'.olean')
            if seed.exists() or seed.is_symlink():raise ValueError(('seed path occupied',module))
            shutil.copyfile(runpath/label/(module+'.olean'),seed)
            row=next(r for r in meta['runs'] if r['label']==label)
            if H(seed)!=row['object_sha256']:raise ValueError(('copied seed drift',module,label))
            seed_hashes[module]=H(seed)
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
        cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text()
        reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",text,re.M)
        if code or reason or 'warning:' in text or 'error:' in text or 'sorryAx' in text or len(reports)!=1:raise ValueError(('compiler failure',label,code,reason,text[-8000:]))
        if {x.strip() for x in reports[0].split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean')}|{str(lib/'DiophantineConsistency'/(m+'.olean')) for m in seed_hashes}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('unexpected direct imports',label,deps.returncode,deps.stdout,deps.stderr))
        if H(src)!=PINS[SOURCE]:raise ValueError(('source drift',label))
        runs.append({'label':label,'compiler_exit':code,'command':cmd,'object_sha256':H(obj),'source_sha256':H(src),'seed_sha256':seed_hashes,'log_sha256':H(log),'stdout':text,'axiom_reports':reports,'sampled_peak_rss_bytes':peak,'stop_reason':reason,'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
        print(label,'exit',code,'peak_RSS',peak,flush=True)
    if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['axiom_reports']!=runs[1]['axiom_reports']:raise ValueError('sibling outputs differ')
    after,metas2=verify_parents(div,copy,summ)
    if before!=after or metas!=metas2:raise ValueError('parents changed')
    receipt={'status':'PASS_PAIRED_COMPACT_SELECTOR_DECODER','runs':runs,'parent_audit':after,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Conditional model decoder for an external finite index type and explicit count, no-carry and value bounds; not compact44 tuple binding, 943-entry machine simulation, checker, iPRA proof, or package-transitive/dynamic ancestry audit. Parent has no complete axiom inventory.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_COMPACT_SELECTOR_DECODER',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
