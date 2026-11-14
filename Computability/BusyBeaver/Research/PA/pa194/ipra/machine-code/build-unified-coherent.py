from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

parser=argparse.ArgumentParser(description='Rebuild unified source-step closure in one coherent startup/header output')
parser.add_argument('--repo', type=Path, required=True)
parser.add_argument('--out', type=Path, required=True)
parser.add_argument('--jobs', type=int, default=2)
args=parser.parse_args()
if args.jobs < 1:
    raise SystemExit('--jobs must be positive')
repo=args.repo.resolve()
out=args.out.resolve()
source=repo / 'Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code'
extra={'PA194FetchPrefixBinding': repo / 'Computability/BusyBeaver/Research/PA/pa194-work/pa194-command-source/PA194FetchPrefixBinding.lean'}
logs=out / 'unified-coherent-logs'
logs.mkdir(exist_ok=False)
for path in out.rglob('*'):
    if path.is_symlink():
        raise SystemExit(f'symlink in supposedly fresh coherent build: {path}')
search=os.environ.get('LEAN_PATH','').split(':')
if not search or Path(search[0]).resolve()!=out:
    raise SystemExit('LEAN_PATH must begin with the coherent build directory')
seen=set(); deps={}; src={}; preexisting=set(); missing=[]
def visit(name):
    if name in seen: return
    seen.add(name)
    obj=out / (name.replace('.','/')+'.olean')
    if obj.exists():
        preexisting.add(name)
        return
    f=extra.get(name,source/(name+'.lean'))
    if not f.is_file():
        if name.startswith(('PA194','PA195','PA196','M6.','Packed','Table','Configuration','BinaryTape','PRAEquality')):
            missing.append(name)
        return
    src[name]=f
    imports=[]
    for line in f.read_text().splitlines():
        match=re.match(r'(?:public )?import\s+(\S+)',line)
        if match:
            imports.append(match.group(1)); visit(match.group(1))
    deps[name]=imports
for name in ('PA194UnifiedSourceStepSentence',):
    visit(name)
if missing: raise SystemExit('missing machine source: '+', '.join(missing))
deps={k:set(v)&src.keys() for k,v in deps.items()}
for name in src:
    for suffix in ('.olean','.olean.private','.olean.server','.ir'):
        path=out/(name+suffix)
        if path.exists() or path.is_symlink(): raise SystemExit(f'refusing to overwrite existing object: {path}')
hashes={name:hashlib.sha256(f.read_bytes()).hexdigest() for name,f in src.items()}
manifest={'output':str(out),'lean_search_roots':search,
          'preexisting_modules':sorted(preexisting),'new_sources_sha256':hashes,
          'targets':['PA194UnifiedSourceStepSentence']}
with (out/'unified-coherent-manifest.json').open('x') as f:
    f.write(json.dumps(manifest,indent=2)+'\n')
env=os.environ.copy()
env['LEAN_PATH']=':'.join(search)
def compile_one(name):
    target=out/(name+'.olean'); f=src[name]; log=logs/(name+'.log')
    if target.exists() or target.is_symlink(): return name,False,'target appeared before compile'
    with log.open('w') as fp:
        result=subprocess.run(['lean','-M6000','-j1','-o',str(target),str(f)],cwd=repo,env=env,stdout=fp,stderr=subprocess.STDOUT)
    output=log.read_text()
    return name,result.returncode==0 and 'sorryAx' not in output,output
remaining=set(src); completed=set(); running={}; failed=[]
print(f'Rebuilding {len(remaining)} machine modules; {len(preexisting)} coherent-baseline imports.',flush=True)
with ThreadPoolExecutor(max_workers=args.jobs) as pool:
    while remaining or running:
        ready=sorted(n for n in remaining if deps[n] <= completed)
        while ready and len(running)<args.jobs and not failed:
            name=ready.pop(0);remaining.remove(name);running[pool.submit(compile_one,name)]=name
        if not running:
            if remaining: raise SystemExit('failure or cyclic dependency: '+', '.join(sorted(remaining)[:20]))
            break
        finished,_=wait(running,return_when=FIRST_COMPLETED)
        for f in finished:
            name=running.pop(f); actual,ok,output=f.result()
            print(name, 'passed' if ok else 'FAILED',flush=True)
            if ok: completed.add(name)
            else:
                failed.append(name);print(output,file=sys.stderr,flush=True)
        if failed and not running: break
if failed: raise SystemExit('failed: '+', '.join(failed))
changed=[name for name,f in src.items() if hashlib.sha256(f.read_bytes()).hexdigest()!=hashes[name]]
if changed: raise SystemExit('sources changed during replay: '+', '.join(changed))
expected={'PA194UnifiedSourceStepSentence':('modelSentence','classicalPRA','nativeIPRA'),
          'PA194BothBranchesSentence':('modelSentence','classicalPRA','nativeIPRA'),
          'PA194SelectedInputFile':('selectedFile',),
          'PA194SelectedInputFrame':('selectedInput_eq',)}
for name,theorems in expected.items():
    output=(logs/(name+'.log')).read_text()
    for theorem in theorems:
        if f"'{name}.{theorem}' depends on axioms:" not in output:
            raise SystemExit(f'missing target axiom report: {name}.{theorem}')
    print(output, end='' if output.endswith('\n') else '\n', flush=True)
print('All requested coherent source modules checked; source hashes remained unchanged.',flush=True)
