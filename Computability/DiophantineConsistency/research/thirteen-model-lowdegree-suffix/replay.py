#!/usr/bin/env python3
"""Paired later-source Forms/Strong/Squares suffix over audited endpoint siblings."""
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
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
if not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke with python3 -I -S')
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
ROOT=BASE.parents[1]
SOURCE=BASE/'Lean/DiophantineConsistency'
AUDIT=BASE/'reviews/thirteen-model-endpoint-successor-pair-independent-audit'
PARENT=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
MONITOR=BASE/'research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py'
ANCHOR='6f8dd13085'
NAMES=('ModelThirteenForms','ModelThirteenStrong','ModelThirteenSquares','ModelThirteenChecks')
SHAS=('98d9dcc48895ffe026c029b2496a61a35b66bca2f7b2fd1b31b8acf43acbfb6f','f68b89af4d639362b5cbff423277f683fd5ff04518678c5b40deff5d436b5897','203ef326964cfc8f7546cc6e13e4e6c4def5d6d0f6027241f7b960adc7ca6700','95d60407a62036e7996fc583353758e9d23f305201e702dd7e81b2a4e2c29667')
PINS={AUDIT/'CHECK.json':'50c18ab38d6393cf784e658b5626bb6ec3cb490dc1652f5b5dcfa2b1adca1cce',
 AUDIT/'audit.py':'ec4892d88e69a9f53d3d93d48ce9e43cc8a5f9631ed4a885af17a40011858681',
 AUDIT/'terminal-observation.json':'9f65d29fd39bab15653d0f35ebf78dea2d590618502ffe56fed8fa863c9082ba',
 PARENT/'receipt.json':'8cf5b948a9442105a88627653e99e78d395a8f40f496b88e9adb6e439630e5cd',
 LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8'}
for name,digest in zip(NAMES,SHAS):PINS[SOURCE/(name+'.lean')]=digest
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
STATUS='PASS_INDEPENDENT_THIRTEEN_ENDPOINT_SUCCESSOR_PAIR_AUDIT'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
REPORTS=[f'DiophantineConsistency.ModelThirteenStrong.{kind}_equivalence{n}' for n in (73,74,72) for kind in ('native','standard','reference')]+[f'DiophantineConsistency.ModelThirteenSquares.{kind}_equivalence{n}' for n in (77,76,75,84) for kind in ('native','standard','reference')]+[f'DiophantineConsistency.ModelThirteenForms.{kind}_equivalence{n}' for n in (70,71) for kind in ('native','standard','reference')]

def check_pins():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    obs=json.loads((AUDIT/'terminal-observation.json').read_text());check=json.loads((AUDIT/'CHECK.json').read_text())
    if obs.get('observed_exit')!=0 or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json'] or check.get('status')!=STATUS:raise ValueError('parent audit observation')
    for name,digest in zip(NAMES,SHAS):
        p=SOURCE/(name+'.lean');git=subprocess.run(['git','show',f'{ANCHOR}:{p.relative_to(ROOT).as_posix()}'],cwd=ROOT,capture_output=True,timeout=30)
        if git.returncode or hashlib.sha256(git.stdout).hexdigest()!=digest:raise ValueError(('anchored source drift',name))

def audit():
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],text=True,capture_output=True,timeout=900)
    if p.returncode or p.stderr:raise ValueError(('parent audit failed',p.returncode,p.stdout,p.stderr))
    data=json.loads(p.stdout)
    if data.get('status')!=STATUS:raise ValueError(('parent audit status',data))
    return data

def overlay(base,dest):
    for current,dirs,files in os.walk(base,followlinks=False):
        current=Path(current);out=dest/current.relative_to(base);out.mkdir(parents=True,exist_ok=True)
        for d in list(dirs):
            p=current/d
            if p.is_symlink():(out/d).symlink_to(p);dirs.remove(d)
        for f in files:(out/f).symlink_to(current/f)

def scan(stem):
    result={}
    for suffix in SUFFIXES:
        p=Path(str(stem)+suffix)
        if os.path.lexists(p):
            if not p.is_file():raise ValueError(('invalid companion',str(p)))
            result[str(p)]={'realpath':str(p.resolve()),'sha256':H(p)}
        else:result[str(p)]=None
    return result

def check_guards(guards):
    for k,v in guards.items():
        p=Path(k)
        if v is None:
            if os.path.lexists(p):raise ValueError(('unexpected companion',k))
        elif not p.is_file() or str(p.resolve())!=v['realpath'] or H(p)!=v['sha256']:
            raise ValueError(('companion drift',k))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();out=args.output.absolute()
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-lowdegree-pair-'):raise ValueError('invalid output')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    driver=H(Path(__file__));check_pins();before=audit()
    if shutil.disk_usage('/tmp').free<4*1024**3:raise ValueError('sampled free space below reserve')
    spec=importlib.util.spec_from_file_location('lowdegree_monitor',MONITOR);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
    out.mkdir();srcroot=out/'src';srcdir=srcroot/'DiophantineConsistency';srcdir.mkdir(parents=True)
    for name,digest in zip(NAMES,SHAS):
        p=srcdir/(name+'.lean');p.write_bytes((SOURCE/(name+'.lean')).read_bytes())
        if H(p)!=digest:raise ValueError(('source copy drift',name))
    rows=[];global_guards={}
    for side in ('author','peer'):
        run=out/side;run.mkdir();lib=run/'lib';overlay(PARENT/side/'lib',lib)
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
        for ix,name in enumerate(NAMES):
            src=srcdir/(name+'.lean');dep='ModelThirteenCarrier' if ix==0 else NAMES[ix-1]
            obj=lib/'DiophantineConsistency'/(name+'.olean');log=run/(name+'.log')
            deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=120)
            expected={str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency'/(dep+'.olean'))}
            if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('dependency mismatch',side,name,deps.returncode,deps.stdout,deps.stderr))
            guards={}
            for item in expected:guards.update(scan(Path(item[:-6])))
            check_guards(guards)
            if os.path.lexists(obj):raise ValueError(('object collision',side,name))
            cmd=[str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={srcroot}',str(src),'-o',str(obj)]
            code,peak,reason=monitor.monitored(cmd,env,log,timeout=600);output=log.read_text()
            reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",output,re.M)
            row={'side':side,'module':name,'command':cmd,'source_sha256':H(src),'exit':code,'stop_reason':reason,'sampled_peak_rss_bytes':peak,'log':str(log),'log_sha256':H(log),'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'axiom_reports':reports}
            rows.append(row);(out/'progress.json').write_text(json.dumps(rows,indent=2)+'\n')
            if code or reason or not obj.is_file() or obj.is_symlink() or re.search(r'(?m)^.*error:|\bsorryAx\b|\bsorry\b',output):raise ValueError(('compiler failure',side,name,code,reason,output[-12000:]))
            if name=='ModelThirteenChecks':
                if [n for n,_ in reports]!=REPORTS or any({x.strip() for x in a.split(',') if x.strip()}!={'propext','Classical.choice','Quot.sound'} for _,a in reports):raise ValueError(('unexpected named reports',side,reports))
            elif reports:raise ValueError(('unexpected reports',side,name,reports))
            if H(src)!=SHAS[ix]:raise ValueError(('source drift',side,name))
            check_guards(guards)
            for k,v in guards.items():
                if k in global_guards and global_guards[k]!=v:raise ValueError(('global companion drift',k))
                global_guards[k]=v
            row['object_sha256']=H(obj);(out/'progress.json').write_text(json.dumps(rows,indent=2)+'\n')
            print(side,ix+1,4,name,'exit',code,'sampled_peak_rss',peak,flush=True)
    for i in range(4):
        a,b=rows[i],rows[i+4]
        if (a['source_sha256'],a['object_sha256'],a['log_sha256'])!=(b['source_sha256'],b['object_sha256'],b['log_sha256']):raise ValueError(('sibling output mismatch',a['module']))
    check_guards(global_guards);check_pins();after=audit()
    if before!=after or H(Path(__file__))!=driver:raise ValueError('audit or driver drift')
    receipt={'status':'PASS_PAIRED_THIRTEEN_LOWDEGREE_SUFFIX','rows':rows,'parent_audit':after,'source_anchor':ANCHOR,
      'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'driver_sha256':driver,'direct_guards':global_guards,
      'scope':'Later-source Forms/Strong/Squares model/iPRA suffix over the audited current endpoint siblings, with 27 named reports. External JSON graph, operation counts, exact degrees, PDF binding, translated-consistency variants and any global minimum remain separate. Sampled compiler guards are not quotas; lean --deps has a leader timeout without group/RSS enforcement. Foundation outer-wrapper and package-transitive/dynamic limits remain.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_LOWDEGREE_SUFFIX',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
