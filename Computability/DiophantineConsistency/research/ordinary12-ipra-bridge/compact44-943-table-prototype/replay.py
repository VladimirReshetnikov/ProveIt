#!/usr/bin/env python3
"""Paired ordered 943-row table and model-independent width proofs."""
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
SOURCE=HERE/'Compact943Data.lean'
CHECKER=HERE/'check_rows.py'
DATA=ROOT/'con-zfc-diophantine-forms/36-small-tuple/coefficients/wang943_tiles.json'
AUDIT=ROOT/'reviews/thirteen-model-parent-window-pair-independent-audit'
PREFIX=Path('/tmp/ipra-thirteen-parent-window-pair-01')
MONITOR=HERE.parent/'free-j-current-denominator-composition/replay.py'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS={SOURCE:'10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8',
 CHECKER:'bfb095af5ad21403e4cbd5cabfc7fb0ba70d872b1f3b33c7fadbab5feb91dcf0',
 DATA:'66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f',
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

def verify_parent():
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],text=True,capture_output=True,timeout=180)
    if p.returncode or p.stderr:raise ValueError(('parent audit failed',p.returncode,p.stdout,p.stderr))
    data=json.loads(p.stdout)
    if data.get('status')!='PASS_INDEPENDENT_24_MODULE_WINDOW_PAIR_AUDIT':raise ValueError(('unexpected parent audit',data))
    return data

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact943-table-pair-'):
        raise ValueError('output must be a fresh direct /tmp/ipra-compact943-table-pair-* directory')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    check_pins();before=verify_parent();monitor=load(MONITOR)
    check=subprocess.run([sys.executable,'-I','-S','-B',str(CHECKER)],text=True,capture_output=True,timeout=30)
    if check.returncode or check.stderr or check.stdout.strip()!=f'PASS_EXACT_ORDERED_943_ROWS {PINS[DATA]} {PINS[SOURCE]}':
        raise ValueError(('ordered row check failed',check.returncode,check.stdout,check.stderr))
    out.mkdir();runs=[]
    for label in ('author','peer'):
        root=out/label/'src';root.mkdir(parents=True);src=root/'Compact943Data.lean';obj=out/label/'Compact943Data.olean';log=out/label/'compiler.log'
        shutil.copyfile(SOURCE,src);lib=PREFIX/label/'lib';env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
        cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text()
        reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",text,re.M)
        if code or reason or 'warning:' in text or 'error:' in text or 'sorryAx' in text or len(reports)!=3:
            raise ValueError(('compiler failure',label,code,reason,text[-8000:]))
        if {name for name,_ in reports}!={'Compact943Data.row_bounds','Compact943Data.rows_length','Compact943Data.row_widths'} or any({x.strip() for x in ax.split(',') if x.strip()}-{'propext','Quot.sound'} for _,ax in reports):raise ValueError(('unexpected axioms',label,reports))
        deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected={str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency/ArithmeticWindowDigits.olean')}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('unexpected direct imports',label,deps.returncode,deps.stdout,deps.stderr))
        if H(src)!=PINS[SOURCE]:raise ValueError(('source drift',label))
        runs.append({'label':label,'compiler_exit':code,'command':cmd,'object_sha256':H(obj),'source_sha256':H(src),
          'log_sha256':H(log),'stdout':text,'axiom_reports':reports,'sampled_peak_rss_bytes':peak,'stop_reason':reason,'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
        print(label,'exit',code,'peak_RSS',peak,flush=True)
    if runs[0]['object_sha256']!=runs[1]['object_sha256'] or runs[0]['axiom_reports']!=runs[1]['axiom_reports']:raise ValueError('sibling outputs differ')
    check_pins();after=verify_parent()
    again=subprocess.run([sys.executable,'-I','-S','-B',str(CHECKER)],text=True,capture_output=True,timeout=30)
    if before!=after or again.returncode or again.stderr or again.stdout!=check.stdout:raise ValueError('parent or ordered rows changed')
    receipt={'status':'PASS_PAIRED_COMPACT_943_TABLE','runs':runs,'parent_audit':after,'ordered_rows_stdout':check.stdout,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
      'scope':'Kernel-checked literal table length and field widths, plus external exact ordered-row comparison to pinned JSON. No internal JSON semantics, K binding, machine simulation, checker, iPRA proof, or package-transitive/dynamic ancestry audit. Parent audit has no complete axiom inventory.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_COMPACT_943_TABLE',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
