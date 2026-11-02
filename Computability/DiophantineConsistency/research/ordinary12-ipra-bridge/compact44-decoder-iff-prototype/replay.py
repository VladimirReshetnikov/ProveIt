#!/usr/bin/env python3
"""Paired compact local decoder iff over audited forward and mask parents."""
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
SOURCE=HERE/'CompactDecoderIff.lean';DEC=BASE/'compact44-selector-decoder-prototype';MASK=BASE/'compact44-mask-converse-prototype'
DECAUDIT=ROOT/'reviews/compact44-selector-decoder-independent-audit/CHECK.json';MASKAUDIT=ROOT/'reviews/compact44-mask-converse-independent-audit/CHECK.json'
DECRUN=Path('/tmp/ipra-compact-selector-decoder-pair-01');MASKRUN=Path('/tmp/ipra-compact-mask-converse-pair-01')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'10b6636d29e19d2171035537d14bf8d709b7643ff2c0a71bc4ab490355832962',
 DEC/'replay.py':'bde8c884393b6d30c9af151429ffff33302692c2991920c18970e5e1b6b585b9',DEC/'evidence/receipt.json':'6089c57318e1156c0b110185ec535d65e4193739575441fc168248c587524180',DECAUDIT:'fa8ddafe2fc18e2ef6a77e8687e997bdf53b04cd800574c15958eb8171168db5',
 MASK/'replay.py':'b38135cedeac5a236fce51db8b65baf9da7184becd1dcc9b5e188b552e1ec826',MASK/'evidence/receipt.json':'3be33d52186afef78605cfa08d2f73e95b56e5577b7c229e46d7a6a8e13a8a52',MASKAUDIT:'c4b48496a938ae1de146c8ab3290963f31ec6fcd4c38135778be0e8188f6f602',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def verify_parents(dec,mask,div,copy,summ):
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    before,_=dec.verify_parents(div,copy,summ);mask.check_pins();other=mask.verify_parent()
    if before!=other:raise ValueError('forward and mask providers differ')
    metas=[]
    for directory,run,module,status in ((DEC,DECRUN,'CompactSelectorDecoder','PASS_PAIRED_COMPACT_SELECTOR_DECODER'),(MASK,MASKRUN,'CompactSelectorConverse','PASS_PAIRED_COMPACT_MASK_CONVERSE')):
        meta=json.loads((directory/'evidence/receipt.json').read_text())
        if meta.get('status')!=status or len(meta['runs'])!=2:raise ValueError(('bad parent receipt',module))
        for row in meta['runs']:
            if row['compiler_exit'] or row['deps_exit'] or H(run/row['label']/(module+'.olean'))!=row['object_sha256']:raise ValueError(('parent seed drift',module,row['label']))
        metas.append(meta)
    for label in ('author','peer'):
        base=dec.DIVRUN/label/'lib';branch=DECRUN/label/'lib'
        a={p.relative_to(base) for p in base.rglob('*.olean')};b={p.relative_to(branch) for p in branch.rglob('*.olean')}
        extras={Path('DiophantineConsistency')/(m+'.olean') for m in ('CompactSelectorDiv','CompactCopy','CompactSelectorSum')}
        if b!=a|extras:raise ValueError(('forward overlay object set drift',label))
        for p in a:
            if H(base/p)!=H(branch/p):raise ValueError(('forward inherited object drift',label,str(p)))
        row=next(r for r in metas[0]['runs'] if r['label']==label)
        for p in extras:
            if H(branch/p)!=row['seed_sha256'][p.stem]:raise ValueError(('forward input seed drift',label,str(p)))
    return before,metas

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-decoder-iff-pair-'):raise ValueError('use a fresh direct /tmp/ipra-compact-decoder-iff-pair-* path')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    dec=load('decoder_parent',DEC/'replay.py');mask=load('mask_parent',MASK/'replay.py');div=load('div_parent',dec.DIV/'replay.py');copy=load('copy_parent',dec.COPY/'replay.py');summ=load('sum_parent',dec.SUM/'replay.py');monitor=load('model_monitor',MONITOR)
    before,metas=verify_parents(dec,mask,div,copy,summ);out.mkdir();runs=[]
    for label in ('author','peer'):
        run=out/label;root=run/'src';root.mkdir(parents=True);src=root/'CompactDecoderIff.lean';obj=run/'CompactDecoderIff.olean';log=run/'compiler.log'
        shutil.copyfile(SOURCE,src);lib=run/'lib';monitor.overlay(DECRUN/label/'lib',lib);seed_hashes={}
        for runpath,module,meta in ((DECRUN,'CompactSelectorDecoder',metas[0]),(MASKRUN,'CompactSelectorConverse',metas[1])):
            seed=lib/'DiophantineConsistency'/(module+'.olean')
            if seed.exists() or seed.is_symlink():raise ValueError(('seed path occupied',module))
            shutil.copyfile(runpath/label/(module+'.olean'),seed);row=next(r for r in meta['runs'] if r['label']==label)
            if H(seed)!=row['object_sha256']:raise ValueError(('copied seed drift',module,label))
            seed_hashes[module]=H(seed)
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text();reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",text,re.M)
        if code or reason or 'warning:' in text or 'error:' in text or 'sorryAx' in text or len(reports)!=1:raise ValueError(('compiler failure',label,code,reason,text[-8000:]))
        if {x.strip() for x in reports[0].split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean')}|{str(lib/'DiophantineConsistency'/(m+'.olean')) for m in seed_hashes}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('unexpected direct imports',label,deps.returncode,deps.stdout,deps.stderr))
        if H(src)!=PINS[SOURCE]:raise ValueError(('source drift',label))
        runs.append({'label':label,'compiler_exit':code,'command':cmd,'object_sha256':H(obj),'source_sha256':H(src),'seed_sha256':seed_hashes,'log_sha256':H(log),'stdout':text,'axiom_reports':reports,'sampled_peak_rss_bytes':peak,'stop_reason':reason,'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
        print(label,'exit',code,'peak_RSS',peak,flush=True)
    if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['axiom_reports']!=runs[1]['axiom_reports']:raise ValueError('sibling outputs differ')
    after,metas2=verify_parents(dec,mask,div,copy,summ)
    if before!=after or metas!=metas2:raise ValueError('parents changed')
    receipt={'status':'PASS_PAIRED_COMPACT_DECODER_IFF','runs':runs,'parent_audit':after,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Conditional model local iff for an external finite index type with explicit count and value bounds; not compact44 tuple binding, 943-entry simulation, checker, iPRA proof, or package-transitive/dynamic ancestry audit. Parent has no complete axiom inventory.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_COMPACT_DECODER_IFF',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
