#!/usr/bin/env python3
"""Paired concrete mask recipe over the audited finite-list parent."""
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
ROOT=HERE.parents[2]
SOURCE=HERE/'CompactConcreteMask.lean'
PREV=HERE.parent/'compact44-list-mask-prototype'
SELAUDIT=ROOT/'reviews/compact44-list-mask-independent-audit/CHECK.json'
SELRUN=Path('/tmp/ipra-compact-list-mask-pair-01')
AUDIT=ROOT/'reviews/thirteen-model-endpoint-successor-pair-independent-audit'
PREFIX=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01')
MONITOR=HERE.parent/'free-j-current-denominator-composition/replay.py'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'7f3c735747e88ecf1dfbf9d6b759a578ec768a857d3d553c06e8656d7be76ece',
 PREV/'replay.py':'ad54969e25f8fc2439790ebbfa830bbe360b93fdfbc4ef480359d94c4db01f94',
 PREV/'evidence/receipt.json':'20d453580cda1086d586996de8be284e498098a7396c4f72741c94c1fecba8ef',
 SELAUDIT:'02c279e26f75784eaa5ccf8e66c392bfbc6d3a4ef144220512cea534fb2bff61',
 AUDIT/'audit.py':'ec4892d88e69a9f53d3d93d48ce9e43cc8a5f9631ed4a885af17a40011858681',
 AUDIT/'CHECK.json':'50c18ab38d6393cf784e658b5626bb6ec3cb490dc1652f5b5dcfa2b1adca1cce',
 AUDIT/'terminal-observation.json':'9f65d29fd39bab15653d0f35ebf78dea2d590618502ffe56fed8fa863c9082ba',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def load(path):
    spec=importlib.util.spec_from_file_location('model_monitor',path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def check_pins():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    obs=json.loads((AUDIT/'terminal-observation.json').read_text());check=json.loads((AUDIT/'CHECK.json').read_text())
    if obs.get('observed_exit')!=0 or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json'] or check.get('status')!='PASS_INDEPENDENT_THIRTEEN_ENDPOINT_SUCCESSOR_PAIR_AUDIT':
        raise ValueError('invalid parent audit')

def check_selector():
    meta=json.loads((PREV/'evidence/receipt.json').read_text())
    review=json.loads(SELAUDIT.read_text())
    if review.get('status')!='PASS_INDEPENDENT_COMPACT44_LIST_MASK_AUDIT' or review.get('recorded_outer_exit')!=0 or review.get('author_receipt_sha256')!=PINS[PREV/'evidence/receipt.json']:
        raise ValueError('invalid scaled-digit parent audit')
    if meta.get('status')!='PASS_PAIRED_COMPACT_LIST_MASK' or len(meta['runs'])!=2:
        raise ValueError('bad selector parent')
    for row in meta['runs']:
        if row['compiler_exit'] or row['deps_exit'] or H(SELRUN/row['label']/'CompactListMask.olean')!=row['object_sha256']:
            raise ValueError(('selector parent drift',row['label']))
    return meta

def verify_parent():
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],text=True,capture_output=True,timeout=900)
    if p.returncode or p.stderr:raise ValueError(('parent audit failed',p.returncode,p.stdout,p.stderr))
    data=json.loads(p.stdout)
    if data.get('status')!='PASS_INDEPENDENT_THIRTEEN_ENDPOINT_SUCCESSOR_PAIR_AUDIT':raise ValueError(('unexpected parent audit',data))
    return data

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-concrete-mask-pair-'):
        raise ValueError('output must be a fresh direct /tmp/ipra-compact-concrete-mask-pair-* directory')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    check_pins();meta=check_selector();before=verify_parent();monitor=load(MONITOR);out.mkdir();runs=[]
    for label in ('author','peer'):
        root=out/label/'src';root.mkdir(parents=True);src=root/'DiophantineConsistency/CompactConcreteMask.lean';src.parent.mkdir(parents=True);obj=out/label/'CompactConcreteMask.olean';log=out/label/'compiler.log'
        shutil.copyfile(SOURCE,src);lib=out/label/'lib';monitor.overlay(PREFIX/label/'lib',lib)
        seed=lib/'DiophantineConsistency/CompactListMask.olean'
        if seed.exists() or seed.is_symlink():raise ValueError('seed path occupied')
        shutil.copyfile(SELRUN/label/'CompactListMask.olean',seed)
        parentrow=next(r for r in meta['runs'] if r['label']==label)
        if H(seed)!=parentrow['object_sha256']:raise ValueError(('selector seed drift',label))
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
        cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text()
        reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",text,re.M)
        if code or reason or 'warning:' in text or 'error:' in text or 'sorryAx' in text or len(reports)!=5:
            raise ValueError(('compiler failure',label,code,reason,text[-8000:]))
        if any({x.strip() for x in r.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for r in reports):raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean'),str(seed)}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('unexpected direct imports',label,deps.returncode,deps.stdout,deps.stderr))
        if H(src)!=PINS[SOURCE]:raise ValueError(('source drift',label))
        runs.append({'label':label,'compiler_exit':code,'command':cmd,'object_sha256':H(obj),'source_sha256':H(src),
          'seed_sha256':H(seed),'log_sha256':H(log),'stdout':text,'axiom_reports':reports,'sampled_peak_rss_bytes':peak,'stop_reason':reason,'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
        print(label,'exit',code,'peak_RSS',peak,flush=True)
    if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['axiom_reports']!=runs[1]['axiom_reports']:raise ValueError('sibling outputs differ')
    check_pins();after=verify_parent()
    if before!=after or meta!=check_selector():raise ValueError('parent audit or selector seeds changed')
    receipt={'status':'PASS_PAIRED_COMPACT_CONCRETE_MASK','runs':runs,'parent_audit':after,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
      'scope':'Concrete interval-support mask recipe and model transfer; no retained MC payload/graph equality, simulation, checker or PRA proof. Provider scope excludes complete package-transitive and dynamic ancestry.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_COMPACT_CONCRETE_MASK',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
