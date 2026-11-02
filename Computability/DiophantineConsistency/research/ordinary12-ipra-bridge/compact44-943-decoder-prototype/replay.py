#!/usr/bin/env python3
"""Paired 943-row local decoder over audited table, range and iff parents."""
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
HERE=Path(__file__).resolve().parent;BASE=HERE.parent;ROOT=HERE.parents[2]
SOURCE=HERE/'Compact943Decoder.lean';IFF=BASE/'compact44-decoder-iff-prototype';TABLE=BASE/'compact44-943-table-prototype';TILE=BASE/'compact44-tile-payload-prototype'
IFFAUDIT=ROOT/'reviews/compact44-decoder-iff-independent-audit/CHECK.json';TABLEAUDIT=ROOT/'reviews/compact44-943-table-independent-audit/CHECK.json';TILEAUDIT=ROOT/'reviews/compact44-tile-payload-independent-audit/CHECK.json'
IFFRUN=Path('/tmp/ipra-compact-decoder-iff-pair-01');TABLERUN=Path('/tmp/ipra-compact943-table-pair-01');TILERUN=Path('/tmp/ipra-compact-tile-payload-pair-01')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'b86cef78ba82bb77e3a5c4f4c5dafeb719f7b8e802ff0527ef31dca4bc62271f',
 IFF/'replay.py':'67bf8ad646afcfeebfa2554dcbfd86a75c4fb1f830bd91528d3e8786999dcc58',IFF/'evidence/receipt.json':'7fdb96e86f0ac5503b68f616fd45591c5d299767e18896704ddbe7811319ad7d',IFFAUDIT:'b3f687cce2cfcd7196d36fe5f07b4d4c21c08fdef8c2e9213b41ebbbb679b533',
 TABLE/'replay.py':'bd936b9ae22de2e6141c4aef9ee91d7a1cf16cf8c512f432c9b1d1451b753970',TABLE/'evidence/receipt.json':'d2b5c30ae68b12c502e7621ef4a26840bb25ce9d9865a5b1fd8d9c4be3625650',TABLEAUDIT:'a4efb0c47a97e78497915c891b0d76be82dc8753eb842c2d15a921f3568ff920',
 TILE/'replay.py':'1d6d7c991e7cb1d772f98ac9d4464f2d33995f1b73633f17dad0124b21d87f99',TILE/'evidence/receipt.json':'74d5ee9ae9b318f4798fdd4efe8278cc0b8318f0d29147ec9bd0c39a0ce28fbd',TILEAUDIT:'2b8415adc827c89f760a88b66a7ec293aeeb8d89d51511e9db7dc85304ae9c22',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def verify_parents(iff,table,tile,dec,mask,div,copy,summ):
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    before,_=iff.verify_parents(dec,mask,div,copy,summ);table.check_pins();tile.check_pins()
    if table.verify_parent()!=before or tile.verify_parent()!=before:raise ValueError('parents report different window provider')
    chk=subprocess.run([sys.executable,'-I','-S','-B',str(table.CHECKER)],text=True,capture_output=True,timeout=30)
    expected=f'PASS_EXACT_ORDERED_943_ROWS {table.PINS[table.DATA]} {table.PINS[table.SOURCE]}'
    if chk.returncode or chk.stderr or chk.stdout.strip()!=expected:raise ValueError(('table check failed',chk.returncode,chk.stdout,chk.stderr))
    metas=[]
    for directory,run,module,status in ((IFF,IFFRUN,'CompactDecoderIff','PASS_PAIRED_COMPACT_DECODER_IFF'),(TABLE,TABLERUN,'Compact943Data','PASS_PAIRED_COMPACT_943_TABLE'),(TILE,TILERUN,'CompactTilePayload','PASS_PAIRED_COMPACT_TILE_PAYLOAD')):
        meta=json.loads((directory/'evidence/receipt.json').read_text())
        if meta.get('status')!=status or len(meta['runs'])!=2:raise ValueError(('bad parent receipt',module))
        for row in meta['runs']:
            if row['compiler_exit'] or row['deps_exit'] or H(run/row['label']/(module+'.olean'))!=row['object_sha256']:raise ValueError(('parent seed drift',module,row['label']))
        metas.append(meta)
    for label in ('author','peer'):
        base=iff.DECRUN/label/'lib';branch=IFFRUN/label/'lib'
        a={p.relative_to(base) for p in base.rglob('*.olean')};b={p.relative_to(branch) for p in branch.rglob('*.olean')}
        extras={Path('DiophantineConsistency')/(m+'.olean') for m in ('CompactSelectorDecoder','CompactSelectorConverse')}
        if b!=a|extras:raise ValueError(('iff overlay object set drift',label))
        for p in a:
            if H(base/p)!=H(branch/p):raise ValueError(('iff inherited object drift',label,str(p)))
        row=next(r for r in metas[0]['runs'] if r['label']==label)
        for p in extras:
            if H(branch/p)!=row['seed_sha256'][p.stem]:raise ValueError(('iff input seed drift',label,str(p)))
    return before,metas,chk.stdout

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact943-decoder-pair-'):raise ValueError('use a fresh direct /tmp/ipra-compact943-decoder-pair-* path')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    iff=load('iff_parent',IFF/'replay.py');table=load('table_parent',TABLE/'replay.py');tile=load('tile_parent',TILE/'replay.py');dec=load('decoder_parent',iff.DEC/'replay.py');mask=load('mask_parent',iff.MASK/'replay.py');div=load('div_parent',dec.DIV/'replay.py');copy=load('copy_parent',dec.COPY/'replay.py');summ=load('sum_parent',dec.SUM/'replay.py');monitor=load('model_monitor',MONITOR)
    before,metas,rows=verify_parents(iff,table,tile,dec,mask,div,copy,summ);out.mkdir();runs=[]
    for label in ('author','peer'):
        run=out/label;root=run/'src';root.mkdir(parents=True);src=root/'Compact943Decoder.lean';obj=run/'Compact943Decoder.olean';log=run/'compiler.log'
        shutil.copyfile(SOURCE,src);lib=run/'lib';monitor.overlay(IFFRUN/label/'lib',lib);seed_hashes={}
        for runpath,module,meta in ((IFFRUN,'CompactDecoderIff',metas[0]),(TABLERUN,'Compact943Data',metas[1]),(TILERUN,'CompactTilePayload',metas[2])):
            seed=lib/'DiophantineConsistency'/(module+'.olean')
            if seed.exists() or seed.is_symlink():raise ValueError(('seed path occupied',module))
            shutil.copyfile(runpath/label/(module+'.olean'),seed);row=next(r for r in meta['runs'] if r['label']==label)
            if H(seed)!=row['object_sha256']:raise ValueError(('copied seed drift',module,label))
            seed_hashes[module]=H(seed)
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text();reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
        if code or reason or 'warning:' in text or 'error:' in text or 'sorryAx' in text or len(reports)!=3:raise ValueError(('compiler failure',label,code,reason,text[-8000:]))
        if {name for name,_ in reports}!={'Compact943Decoder.tileValue_bounds','Compact943Decoder.count_bound','Compact943Decoder.decode_iff'} or any({x.strip() for x in ax.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for _,ax in reports):raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean')}|{str(lib/'DiophantineConsistency'/(m+'.olean')) for m in seed_hashes}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('unexpected direct imports',label,deps.returncode,deps.stdout,deps.stderr))
        if H(src)!=PINS[SOURCE]:raise ValueError(('source drift',label))
        runs.append({'label':label,'compiler_exit':code,'command':cmd,'object_sha256':H(obj),'source_sha256':H(src),'seed_sha256':seed_hashes,'log_sha256':H(log),'stdout':text,'axiom_reports':reports,'sampled_peak_rss_bytes':peak,'stop_reason':reason,'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
        print(label,'exit',code,'peak_RSS',peak,flush=True)
    if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['axiom_reports']!=runs[1]['axiom_reports']:raise ValueError('sibling outputs differ')
    after,metas2,rows2=verify_parents(iff,table,tile,dec,mask,div,copy,summ)
    if before!=after or metas!=metas2 or rows!=rows2:raise ValueError('parents changed')
    receipt={'status':'PASS_PAIRED_COMPACT_943_DECODER','runs':runs,'parent_audit':after,'ordered_rows_stdout':rows,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Conditional local decoder for external Fin 943, with explicit selector and W bounds; table-to-JSON comparison is external, with no K/full tuple binding, graph premise extraction, machine simulation, checker, iPRA proof, or package-transitive/dynamic ancestry audit. Parent has no complete axiom inventory.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_COMPACT_943_DECODER',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
