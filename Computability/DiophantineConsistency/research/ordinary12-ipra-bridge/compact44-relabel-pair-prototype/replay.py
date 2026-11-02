#!/usr/bin/env python3
"""Draft paired finite tile correspondence over audited successor siblings."""
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
BASE=HERE.parents[2]
ROOT=BASE.parents[1]
SOURCE=HERE
AUDIT=BASE/'reviews/thirteen-model-endpoint-successor-pair-independent-audit'
PARENT=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
MONITOR=BASE/'research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py'
MANIFEST=HERE/'manifest.json'
MANIFEST_SHA='7f78a6ee9c9f1e3a3e859e0be035ed31c5c3efc29f7c4fcd887881b4a043f0a0'
NAMES=tuple(x['module'] for x in json.loads(MANIFEST.read_bytes()))
SHAS=tuple(x['sha256'] for x in json.loads(MANIFEST.read_bytes()))
PINS={MANIFEST:MANIFEST_SHA,
 AUDIT/'CHECK.json':'50c18ab38d6393cf784e658b5626bb6ec3cb490dc1652f5b5dcfa2b1adca1cce',
 AUDIT/'audit.py':'ec4892d88e69a9f53d3d93d48ce9e43cc8a5f9631ed4a885af17a40011858681',
 AUDIT/'terminal-observation.json':'9f65d29fd39bab15653d0f35ebf78dea2d590618502ffe56fed8fa863c9082ba',
 PARENT/'receipt.json':'8cf5b948a9442105a88627653e99e78d395a8f40f496b88e9adb6e439630e5cd',
 BASE/'reviews/compact44-color-relabel-independent-audit/CHECK.json':'6285783203d28361ca1417509659722a83858467027306e617749bfb34bb44be',
 BASE/'reviews/compact44-color-relabel-independent-audit/audit.py':'24f7643de6e25b7f5626a5712ab2751cdcd8e487492b605b37bb97f900c8e2b9',
 BASE/'reviews/compact44-color-relabel-independent-audit/terminal-observation.json':'57133750b36d5f3bbdea96c7ce476b41950d60a97b4b0de8222b226e09b09690',
 BASE/'reviews/compact44-943-table-independent-audit/CHECK.json':'a4efb0c47a97e78497915c891b0d76be82dc8753eb842c2d15a921f3568ff920',
 BASE/'reviews/compact44-943-table-independent-audit/audit.py':'9d479abf187a75f6e7e6338ac6e86a37583afd4ca9e7a5c8ca8bcf51b36facc9',
 BASE/'reviews/compact44-943-table-independent-audit/terminal-observation.json':'4e25b7bc5f86ad810fbde036598fe01a6b817502f6760c3042eef189357524f7',
 BASE/'research/ordinary12-ipra-bridge/compact44-color-relabel/chunk-drafts/check_arrays.py':'3e604abad98e1a35b39d3ddd3d63358958de8697dfc7d1979e23c2166a1ec1b6',
 BASE/'research/ordinary12-ipra-bridge/compact44-color-relabel/index-drafts/check_inverse.py':'3e94ead263d815fb16e89ac9bb11274e5a4ddc447159afdd74ee8754c0766b4f',
 LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8'}
for item in json.loads(MANIFEST.read_bytes()):PINS[ROOT/item['source']]=item['sha256']
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
EXPECTED_HEAD=None

def check_head():
    if EXPECTED_HEAD is None or not re.fullmatch(r'[0-9a-f]{40}',EXPECTED_HEAD):raise ValueError('expected full HEAD is required')
    q=subprocess.run(['git','rev-parse','HEAD'],cwd=ROOT,capture_output=True,text=True,timeout=30)
    if q.returncode or q.stdout.strip()!=EXPECTED_HEAD:raise ValueError(('HEAD changed',q.returncode,q.stdout,q.stderr))
    q=subprocess.run(['git','diff','--quiet','--ignore-submodules','HEAD','--'],cwd=ROOT,capture_output=True,text=True,timeout=30)
    if q.returncode or q.stderr:raise ValueError(('tracked worktree drift',q.returncode,q.stderr))

STATUS='PASS_INDEPENDENT_THIRTEEN_ENDPOINT_SUCCESSOR_PAIR_AUDIT'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def check_pins():
    for p,h in PINS.items():
        if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
    manifest=json.loads(MANIFEST.read_bytes())
    if len(manifest)!=58 or len(set(NAMES))!=58:raise ValueError('manifest size or duplicate module')
    seen=set()
    for item in manifest:
        imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',(ROOT/item['source']).read_text(),re.M)
        if not imports:raise ValueError(('missing declared import',item['module']))
        for imp in imports:
            if not imp.startswith('DiophantineConsistency.'):raise ValueError(('unsupported external direct import',imp))
            stem=imp.rsplit('.',1)[1]
            if stem in NAMES and stem not in seen:raise ValueError(('import order',item['module'],imp))
            if stem not in NAMES:
                for side in ('author','peer'):
                    if not (PARENT/side/'lib'/Path(*imp.split('.')).with_suffix('.olean')).is_file():raise ValueError(('missing parent object',side,imp))
        for side in ('author','peer'):
            if os.path.lexists(PARENT/side/'lib/DiophantineConsistency'/(item['module']+'.olean')):raise ValueError(('parent object collision',side,item['module']))
        seen.add(item['module'])
        q=subprocess.run(['git','show',item['anchor']+':'+item['source']],cwd=ROOT,capture_output=True,timeout=30)
        if q.returncode or hashlib.sha256(q.stdout).hexdigest()!=item['sha256']:raise ValueError(('source anchor',item['module']))
    obs=json.loads((AUDIT/'terminal-observation.json').read_text());check=json.loads((AUDIT/'CHECK.json').read_text())
    if obs.get('observed_exit')!=0 or obs.get('receipt_sha256')!=PINS[AUDIT/'CHECK.json'] or check.get('status')!=STATUS:raise ValueError('parent audit observation')
    finite=BASE/'reviews/compact44-color-relabel-independent-audit'
    fo=json.loads((finite/'terminal-observation.json').read_text());fc=json.loads((finite/'CHECK.json').read_text())
    if fo.get('observed_exit_codes')!=[0,0] or fo.get('receipt_sha256')!=PINS[finite/'CHECK.json'] or fc.get('status')!='PASS_INDEPENDENT_COMPACT44_RELABEL_FINITE':raise ValueError('finite audit observation')
    table=BASE/'reviews/compact44-943-table-independent-audit'
    to=json.loads((table/'terminal-observation.json').read_text());tc=json.loads((table/'CHECK.json').read_text())
    if to.get('observed_exit')!=0 or to.get('receipt_sha256')!=PINS[table/'CHECK.json'] or tc.get('status')!='PASS_INDEPENDENT_COMPACT44_943_TABLE_AUDIT':raise ValueError('table audit observation')
    for checker in (BASE/'research/ordinary12-ipra-bridge/compact44-color-relabel/chunk-drafts/check_arrays.py',BASE/'research/ordinary12-ipra-bridge/compact44-color-relabel/index-drafts/check_inverse.py'):
        q=subprocess.run([sys.executable,'-I','-S',str(checker)],capture_output=True,text=True,timeout=30)
        if q.returncode or q.stderr or not q.stdout.startswith('PASS_'):raise ValueError(('array binding',str(checker),q.stdout,q.stderr))


def audit():
    p=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],text=True,capture_output=True,timeout=900)
    if p.returncode or p.stderr:raise ValueError(('parent audit failed',p.returncode,p.stdout,p.stderr))
    data=json.loads(p.stdout)
    if data.get('status')!=STATUS:raise ValueError(('parent audit status',data))
    for directory in (BASE/'reviews/compact44-color-relabel-independent-audit',BASE/'reviews/compact44-943-table-independent-audit'):
        q=subprocess.run([sys.executable,'-I','-S','-B',str(directory/'audit.py')],capture_output=True,text=True,timeout=900)
        if q.returncode or q.stderr or json.loads(q.stdout)!=json.loads((directory/'CHECK.json').read_text()):raise ValueError(('audit rerun',str(directory),q.returncode,q.stdout[-1000:],q.stderr[-1000:]))
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
    global EXPECTED_HEAD
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--expected-head',required=True);ap.add_argument('--preflight',action='store_true');args=ap.parse_args();out=args.output.absolute();EXPECTED_HEAD=args.expected_head
    if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-relabel-pair-'):raise ValueError('invalid output')
    if out.exists() or out.is_symlink():raise ValueError('output exists')
    driver=H(Path(__file__));check_head();check_pins();before=audit();check_head()
    if args.preflight:
        print('PASS_PREFLIGHT_COMPACT_RELABEL',MANIFEST_SHA,EXPECTED_HEAD,flush=True)
        return
    if shutil.disk_usage('/tmp').free<4*1024**3:raise ValueError('sampled free space below reserve')
    spec=importlib.util.spec_from_file_location('lowdegree_monitor',MONITOR);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
    out.mkdir();srcroot=out/'src';srcdir=srcroot/'DiophantineConsistency';srcdir.mkdir(parents=True)
    for item in json.loads(MANIFEST.read_bytes()):
        p=srcdir/(item['module']+'.lean');p.write_bytes((ROOT/item['source']).read_bytes())
        if H(p)!=item['sha256']:raise ValueError(('source copy drift',item['module']))
    rows=[];global_guards={}
    for side in ('author','peer'):
        run=out/side;run.mkdir();lib=run/'lib';overlay(PARENT/side/'lib',lib)
        env=os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
        env['LEAN_PATH']=str(lib)+':'+str(PACKAGE)
        for ix,name in enumerate(NAMES):
            check_head()
            src=srcdir/(name+'.lean')
            obj=lib/'DiophantineConsistency'/(name+'.olean');log=run/(name+'.log')
            deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=120)
            imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M)
            expected={str(PACKAGE/'Init.olean')} | {str(lib/Path(*d.split('.')).with_suffix('.olean')) for d in imports}
            if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('dependency mismatch',side,name,deps.returncode,deps.stdout,deps.stderr))
            guards={}
            for item in expected:guards.update(scan(Path(item[:-6])))
            check_guards(guards)
            if os.path.lexists(obj):raise ValueError(('object collision',side,name))
            cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={srcroot}',str(src),'-o',str(obj)]
            code,peak,reason=monitor.monitored(cmd,env,log,timeout=600);output=log.read_text()
            reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",output,re.M)
            row={'side':side,'module':name,'command':cmd,'source_sha256':H(src),'exit':code,'stop_reason':reason,'sampled_peak_rss_bytes':peak,'log':str(log),'log_sha256':H(log),'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'axiom_reports':reports}
            rows.append(row);(out/'progress.json').write_text(json.dumps(rows,indent=2)+'\n')
            if code or reason or not obj.is_file() or obj.is_symlink() or re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',output):raise ValueError(('compiler failure',side,name,code,reason,output[-12000:]))
            wanted=re.findall(r'^#print axioms\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M)
            reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",output,re.M)
            if [n for n,_ in reports]!=wanted:raise ValueError(('unexpected named reports',side,name,reports,wanted))
            for decl,axs in reports:
                actual={x.strip() for x in axs.split(',') if x.strip()}
                if decl.endswith(('.rows_length','.row_widths')) or re.fullmatch(r'CompactRelabelDraft.forward_\d\d',decl):expected_axioms=set()
                elif decl.endswith(('.row_bounds','.forward_roundtrip')):expected_axioms={'propext','Quot.sound'}
                else:expected_axioms={'propext','Classical.choice','Quot.sound'}
                if actual!=expected_axioms:raise ValueError(('unexpected axiom set',side,decl,actual,expected_axioms))
            row['axiom_reports']=reports
            if H(src)!=SHAS[ix]:raise ValueError(('source drift',side,name))
            check_head();check_guards(guards)
            for k,v in guards.items():
                if k in global_guards and global_guards[k]!=v:raise ValueError(('global companion drift',k))
                global_guards[k]=v
            row['object_sha256']=H(obj);(out/'progress.json').write_text(json.dumps(rows,indent=2)+'\n')
            print(side,ix+1,58,name,'exit',code,'sampled_peak_rss',peak,flush=True)
    for i in range(58):
        a,b=rows[i],rows[i+58]
        if (a['source_sha256'],a['object_sha256'],a['log_sha256'])!=(b['source_sha256'],b['object_sha256'],b['log_sha256']):raise ValueError(('sibling output mismatch',a['module']))
    check_guards(global_guards);check_head();check_pins();after=audit();check_head()
    if before!=after or H(Path(__file__))!=driver:raise ValueError('audit or driver drift')
    receipt={'status':'PASS_PAIRED_COMPACT_RELABEL','rows':rows,'parent_audit':after,
      'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'driver_sha256':driver,'expected_head':EXPECTED_HEAD,'direct_guards':global_guards,
      'scope':'Finite table equality and color/index permutation theorems, not all-model tiling transport, compact44 calibration, or an iPRA endpoint. Sampled compiler guards are not quotas; lean --deps has a leader timeout without group/RSS enforcement. Foundation outer-wrapper and package-transitive/dynamic limits remain.'}
    with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_COMPACT_RELABEL',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
