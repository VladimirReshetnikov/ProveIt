#!/usr/bin/env python3
"""Bounded mixed-provider author check of the byte-port model equivalence."""
from hashlib import sha256
from pathlib import Path
import json
import os
import shutil
import subprocess
import time

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'CompactBytePortsModelIff.lean'
PREP=HERE/'observations/prepare-attempt01/manifest.json'
OBS=HERE/'observations/attempt03'
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PREP_HASH='d45af4289b21b8d4f18a4eab385d8a39bfe6d4d2690a59fe7cc1c5f83f818abe'
SOURCE_HASH='c6e81cf3ad13e70e55f68a8ab97702815fc78ef025facc06c2143ccecbc61932'
SUFFIXES=('.olean', '.olean.private', '.olean.server', '.ir', '.ilean',
          '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ir.hash', '.ilean.hash')

def digest(path): return sha256(Path(path).read_bytes()).hexdigest()
def record(path):
    p=Path(path)
    if not os.path.lexists(p): return None
    if not p.is_file(): raise RuntimeError(f'dangling guard {p}')
    return {'sha256':digest(p),'resolved':str(p.resolve(strict=True)),
            'link':os.readlink(p) if p.is_symlink() else None}
def selected(manifest,lib):
    actual={p.relative_to(lib).as_posix():record(p) for p in lib.rglob('*') if p.is_file()}
    expected=manifest['files']
    return set(actual)==set(expected) and all(actual[x]['sha256']==expected[x]['sha256'] and
       actual[x]['resolved']==expected[x]['resolved'] for x in expected)
def providers_match(manifest):
    if any(record(path)!=old for path,old in manifest['model_before'].items()): return False
    if any(record(path)!=old for path,old in manifest['model_guards'].items()): return False
    if any(record(path)!=old for path,old in manifest['byte_guards'].items()): return False
    for key in ('byte','model'):
        path=Path(manifest[key+'_receipt_path'])
        if digest(path)!=manifest[key+'_receipt_sha256']: return False
        r=json.loads(path.read_text())
        if r['exit_code']!=0: return False
        module='CompactFourPortByteAssembly2' if key=='byte' else 'FreeJRetainedShiftModel'
        output=Path(r['command'][-1])
        if output.name!=module+'.olean': return False
        root=output.parent
        if digest(root/(module+'.olean'))!=r['object_sha256'] or digest(root/(module+'.lean'))!=r['source_sha256']: return False
    path=Path(manifest['byte_manifest_path'])
    if digest(path)!=manifest['byte_manifest_sha256']: return False
    bm=json.loads(path.read_text())
    if any(record(p)!=v for p,v in bm['guards_before'].items()): return False
    for item in bm['prior_manifests'].values():
        if digest(item['path'])!=item['sha256'] or any(record(p)!=v for p,v in item['providers_before'].items()): return False
    return True

if OBS.exists(): raise RuntimeError('refusing to overwrite prior attempt')
if shutil.disk_usage('/tmp').free < 4*1024**3: raise RuntimeError('less than 4 GiB free')
if digest(PREP)!=PREP_HASH or digest(SOURCE)!=SOURCE_HASH: raise RuntimeError('pin drift')
manifest=json.loads(PREP.read_text());project=Path(manifest['project']);lib=project/'lib'
if not manifest['unchanged'] or not selected(manifest,lib) or not providers_match(manifest):
    raise RuntimeError('provider preflight drift')
OBS.mkdir(parents=True)
src=project/SOURCE.name;shutil.copyfile(SOURCE,src);shutil.copyfile(SOURCE,OBS/'source.lean')
env={'PATH':'/usr/bin:/bin','LEAN_PATH':f'{lib}:{PACKAGE}','LEAN_NUM_THREADS':'1'}
deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,capture_output=True,text=True,timeout=120)
(OBS/'deps').write_text(deps.stdout);(OBS/'deps.stderr').write_text(deps.stderr)
if deps.returncode != 0 or deps.stderr: raise RuntimeError('dependency scan failed')
guards={}
for line in deps.stdout.splitlines():
    p=Path(line)
    if not p.is_absolute() or not p.is_file() or p.suffix!='.olean':
        raise RuntimeError(f'bad dependency {line}')
    stem=str(p)[:-len('.olean')]
    for suffix in SUFFIXES: guards[stem+suffix]=record(stem+suffix)
command=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={project}',str(src),'-o',str(project/'CompactBytePortsModelIff.olean')]
t0=time.monotonic()
try:
    proc=subprocess.run(command,env=env,capture_output=True,text=True,timeout=180)
    code,output=proc.returncode,proc.stdout+proc.stderr
except subprocess.TimeoutExpired as e:
    code,output=None,str(e.stdout or '')+str(e.stderr or '')
(OBS/'compile.log').write_text(output)
obj=project/'CompactBytePortsModelIff.olean'
result={'command':command,'exit_code':code,'duration_seconds':round(time.monotonic()-t0,3),
        'source_sha256':digest(src),'workspace_source_sha256_after':digest(SOURCE),
        'log_sha256':digest(OBS/'compile.log'),'object_sha256':digest(obj) if obj.is_file() else None,
        'guards_before':guards,'guards_unchanged':all(record(p)==r for p,r in guards.items()),
        'selected_unchanged':selected(manifest,lib),'providers_unchanged':providers_match(manifest),
        'manifest_sha256':digest(PREP),
        'scope':'author-side mixed-provider check; inherited package and dynamic ancestry'}
(OBS/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:result[k] for k in ('exit_code','duration_seconds','object_sha256','guards_unchanged','selected_unchanged','providers_unchanged')},sort_keys=True))
if code != 0 or not obj.is_file() or not all(result[k] for k in ('guards_unchanged','selected_unchanged','providers_unchanged')) or \
   digest(SOURCE)!=SOURCE_HASH or digest(PREP)!=PREP_HASH or any(w in output for w in ('error:','warning:','sorryAx')):
    raise SystemExit(1)
