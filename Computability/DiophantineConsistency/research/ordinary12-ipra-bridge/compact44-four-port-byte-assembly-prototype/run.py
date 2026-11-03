#!/usr/bin/env python3
"""Guarded author check of the four symbolic byte-port decoding equalities."""
from hashlib import sha256
from pathlib import Path
import json
import os
import shutil
import subprocess
import time

HERE=Path(__file__).resolve().parent; B=HERE.parent
SOURCE=HERE/'CompactFourPortByteAssembly.lean'
PREP=HERE/'observations/prepare-attempt01/manifest.json'; OBS=HERE/'observations/attempt01'
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PREP_HASH='ec3f5afc67e4424d9bd026edf0c4a7e5c8a3cb8817bdc29875e81e3ccfe176c8'
SOURCE_HASH='3f11c7dc04b68065da70f7e4743236162ff1f376e85b8cc94019e2f1d3c0d7fc'
SPECS={
 'beta':(B/'compact44-retained-beta-byte-prototype/observations/attempt03/terminal.json',Path('/tmp/compact44-retained-beta-byte-author-ap_xzsq2'),'RetainedBetaBytes'),
 'K':(B/'compact44-k-byte-recipe-prototype/observations/attempt01/terminal.json',Path('/tmp/compact44-k-byte-recipe-y1mp4tiq'),'CompactKernelByteRecipe'),
 'MC':(B/'compact44-low-byte-assembly-attempt2/observations/attempt01/terminal.json',Path('/tmp/compact44-low-byte-assembly-xxmulcse'),'CompactLowByteAssembly'),
 'MF':(B/'compact44-mf-byte-assembly-prototype/observations/attempt01/terminal.json',Path('/tmp/compact44-mf-byte-assembly-g3jgk09k'),'CompactShiftedHighByteAssembly'),
}
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean',
          '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def digest(p): return sha256(Path(p).read_bytes()).hexdigest()
def record(p):
 p=Path(p)
 if not os.path.lexists(p): return None
 if not p.is_file(): raise RuntimeError(f'dangling {p}')
 return {'sha256':digest(p),'resolved':str(p.resolve(strict=True)),
         'link':os.readlink(p) if p.is_symlink() else None}
def selected(m,lib):
 actual={p.relative_to(lib).as_posix():record(p) for p in lib.rglob('*') if p.is_file()}
 return set(actual)==set(m['files']) and all(actual[k]['sha256']==m['files'][k]['sha256'] and
    actual[k]['resolved']==m['files'][k]['resolved'] for k in actual)
def producers_match(m):
 for name,(path,root,module) in SPECS.items():
  if digest(path)!=m['prior_receipt_sha256'][name]: return False
  r=json.loads(path.read_text()); log=path.parent/'compile.log'
  if (digest(root/(module+'.olean'))!=r['object_sha256'] or digest(root/(module+'.lean'))!=r['source_sha256']
      or digest(log)!=r['log_sha256'] or r['exit_code']!=0 or not r['guards_unchanged']): return False
  if any(x in log.read_text() for x in ('error:','warning:','sorryAx')): return False
  if any(record(p)!=old for p,old in r['guards_before'].items()): return False
 for item in m['prior_manifests'].values():
  if digest(item['path'])!=item['sha256']: return False
  if any(record(p)!=old for p,old in item['providers_before'].items()): return False
 return all(record(p)==old for p,old in m['guards_before'].items())

if OBS.exists(): raise RuntimeError('observation exists')
if shutil.disk_usage('/tmp').free<4*1024**3: raise RuntimeError('less than 4 GiB free')
if digest(PREP)!=PREP_HASH or digest(SOURCE)!=SOURCE_HASH: raise RuntimeError('pin drift')
m=json.loads(PREP.read_text());project=Path(m['project']);lib=project/'lib'
if not m['unchanged'] or not selected(m,lib) or not producers_match(m): raise RuntimeError('provider preflight drift')
OBS.mkdir(parents=True);src=project/SOURCE.name;shutil.copyfile(SOURCE,src);shutil.copyfile(SOURCE,OBS/'source.lean')
env={'PATH':'/usr/bin:/bin','LEAN_PATH':f'{lib}:{PACKAGE}','LEAN_NUM_THREADS':'1'}
deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,capture_output=True,text=True,timeout=120)
(OBS/'deps').write_text(deps.stdout);(OBS/'deps.stderr').write_text(deps.stderr)
if deps.returncode!=0 or deps.stderr: raise RuntimeError('dependency scan failed')
guards={}
for line in deps.stdout.splitlines():
 p=Path(line)
 if not p.is_absolute() or not p.is_file() or p.suffix!='.olean': raise RuntimeError(f'bad dependency {line}')
 stem=str(p)[:-len('.olean')]
 for suffix in SUFFIXES: guards[stem+suffix]=record(stem+suffix)
command=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={project}',str(src),'-o',str(project/'CompactFourPortByteAssembly.olean')]
t0=time.monotonic()
try:
 proc=subprocess.run(command,env=env,capture_output=True,text=True,timeout=180)
 code,output=proc.returncode,proc.stdout+proc.stderr
except subprocess.TimeoutExpired as e: code,output=None,str(e.stdout or '')+str(e.stderr or '')
(OBS/'compile.log').write_text(output);obj=project/'CompactFourPortByteAssembly.olean'
result={'command':command,'exit_code':code,'duration_seconds':round(time.monotonic()-t0,3),
 'source_sha256':digest(src),'workspace_source_sha256_after':digest(SOURCE),
 'log_sha256':digest(OBS/'compile.log'),'object_sha256':digest(obj) if obj.is_file() else None,
 'guards_before':guards,'guards_unchanged':all(record(p)==v for p,v in guards.items()),
 'selected_unchanged':selected(m,lib),'producers_unchanged':producers_match(m),
 'manifest_sha256':digest(PREP),'scope':'author-side mixed-provider proof; inherited ancestry'}
(OBS/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:result[k] for k in ('exit_code','duration_seconds','object_sha256','guards_unchanged','selected_unchanged','producers_unchanged')},sort_keys=True))
if code!=0 or not obj.is_file() or not all(result[k] for k in ('guards_unchanged','selected_unchanged','producers_unchanged')) or \
   digest(SOURCE)!=SOURCE_HASH or digest(PREP)!=PREP_HASH or any(x in output for x in ('error:','warning:','sorryAx')):
 raise SystemExit(1)
