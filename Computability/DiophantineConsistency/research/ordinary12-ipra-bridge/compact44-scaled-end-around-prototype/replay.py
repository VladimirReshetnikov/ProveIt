#!/usr/bin/env python3
"""Paired arbitrary-digit end-around carry over the audited scaled-digit parent."""
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
SOURCE=HERE/'CompactScaledCarry.lean'
PREV=HERE.parent/'compact44-scaled-carry-prototype'
SELAUDIT=ROOT/'reviews/compact44-scaled-carry-independent-audit/CHECK.json'
SELRUN=Path('/tmp/ipra-compact-scaled-carry-pair-01')
AUDIT=ROOT/'reviews/thirteen-model-parent-window-pair-independent-audit'
PREFIX=Path('/tmp/ipra-thirteen-parent-window-pair-01')
MONITOR=HERE.parent/'free-j-current-denominator-composition/replay.py'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'89da94c91351217b89228e4c7794302f82d38d39495f5ce65a784c60f86ff16b',
 PREV/'replay.py':'2f6288cd4e5fa30b1f9d2f2a4c5a51bc806efe74bf1c24708f8f007cc86dbfc4',
 PREV/'evidence/receipt.json':'12adfaa6a0969de59893ce59b6f26ac04d11b87ae03db963e67904a7f06943df',
 SELAUDIT:'d2352465b3c539902040aea3f9ef189f0930cd10b1ddf3b8306444720c5a03bc',
 AUDIT/'audit.py':'679a7680a3e4fbc3a7555bc1ba3a43b543d749311f08760a91ab24433539f4c1',
 AUDIT/'CHECK.json':'4a358f8fd09fa3be38d32aa2314ad063406ea2d363f74d1a13f41dedcc3e0ec9',
 AUDIT/'terminal-observation.json':'516750a20bddd6d87dc5ecd0bdcd904c6d74deb505b5b8b3c6f4ba111f7a2549',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def load(path):
    spec=importlib.util.spec_from_file_location('model_monitor',path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def check_pins():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    obs=json.loads((AUDIT/'terminal-observation.json').read_text());check=json.loads((AUDIT/'CHECK.json').read_text())
    if obs.get('audit_observed_exit_code')!=0 or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json'] or check.get('status')!='PASS_INDEPENDENT_24_MODULE_WINDOW_PAIR_AUDIT':
        raise ValueError('invalid parent audit')

def check_selector():
    meta=json.loads((PREV/'evidence/receipt.json').read_text())
    review=json.loads(SELAUDIT.read_text())
    if review.get('status')!='PASS_INDEPENDENT_COMPACT44_SCALED_CARRY_AUDIT' or review.get('recorded_outer_exit')!=0 or review.get('author_receipt_sha256')!=PINS[PREV/'evidence/receipt.json']:
        raise ValueError('invalid scaled-digit parent audit')
    if meta.get('status')!='PASS_PAIRED_COMPACT_SCALED_CARRY' or len(meta['runs'])!=2:
        raise ValueError('bad selector parent')
    for row in meta['runs']:
        if row['compiler_exit'] or row['deps_exit'] or H(SELRUN/row['label']/'CompactDigitBound.olean')!=row['object_sha256']:
            raise ValueError(('selector parent drift',row['label']))
    return meta

def verify_parent():
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],text=True,capture_output=True,timeout=180)
    if p.returncode or p.stderr:raise ValueError(('parent audit failed',p.returncode,p.stdout,p.stderr))
    data=json.loads(p.stdout)
    if data.get('status')!='PASS_INDEPENDENT_24_MODULE_WINDOW_PAIR_AUDIT':raise ValueError(('unexpected parent audit',data))
    return data

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-scaled-end-around-pair-'):
        raise ValueError('output must be a fresh direct /tmp/ipra-compact-scaled-end-around-pair-* directory')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    check_pins();meta=check_selector();before=verify_parent();monitor=load(MONITOR);out.mkdir();runs=[]
    for label in ('author','peer'):
        root=out/label/'src';root.mkdir(parents=True);src=root/'DiophantineConsistency/CompactScaledCarry.lean';src.parent.mkdir(parents=True);obj=out/label/'CompactScaledCarry.olean';log=out/label/'compiler.log'
        shutil.copyfile(SOURCE,src);lib=out/label/'lib';monitor.overlay(PREFIX/label/'lib',lib)
        seed=lib/'DiophantineConsistency/CompactDigitBound.olean'
        if seed.exists() or seed.is_symlink():raise ValueError('seed path occupied')
        shutil.copyfile(SELRUN/label/'CompactDigitBound.olean',seed)
        parentrow=next(r for r in meta['runs'] if r['label']==label)
        if H(seed)!=parentrow['object_sha256']:raise ValueError(('selector seed drift',label))
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
        cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text()
        reports=re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",text,re.M)
        if code or reason or 'warning:' in text or 'error:' in text or 'sorryAx' in text or len(reports)!=4:
            raise ValueError(('compiler failure',label,code,reason,text[-8000:]))
        if any({x.strip() for x in r.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for r in reports):raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean'),str(seed),str(lib/'DiophantineConsistency/ArithmeticWindowCarry.olean')}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('unexpected direct imports',label,deps.returncode,deps.stdout,deps.stderr))
        if H(src)!=PINS[SOURCE]:raise ValueError(('source drift',label))
        runs.append({'label':label,'compiler_exit':code,'command':cmd,'object_sha256':H(obj),'source_sha256':H(src),
          'seed_sha256':H(seed),'log_sha256':H(log),'stdout':text,'axiom_reports':reports,'sampled_peak_rss_bytes':peak,'stop_reason':reason,'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
        print(label,'exit',code,'peak_RSS',peak,flush=True)
    if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['axiom_reports']!=runs[1]['axiom_reports']:raise ValueError('sibling outputs differ')
    check_pins();after=verify_parent()
    if before!=after or meta!=check_selector():raise ValueError('parent audit or selector seeds changed')
    receipt={'status':'PASS_PAIRED_COMPACT_SCALED_END_AROUND','runs':runs,'parent_audit':after,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
      'scope':'Conditional model end-around carry with arbitrary digit cap. No actual compact digit bounds, mass estimate, clean-predecessor transport, graph binding, simulation, checker, or iPRA proof; no complete provider axiom inventory or package-transitive/dynamic ancestry audit.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_COMPACT_SCALED_END_AROUND',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
