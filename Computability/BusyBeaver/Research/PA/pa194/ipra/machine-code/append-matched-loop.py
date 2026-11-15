#!/usr/bin/env python3
"""Check the source-side and matched extensions in a completed loop stage."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys
repo,src,out,matched,tail,carry,baseline,fetch,project,package=map(lambda x:Path(x).resolve(),sys.argv[1:11])
for k in ('GIT_DIR','GIT_WORK_TREE','GIT_INDEX_FILE','GIT_OBJECT_DIRECTORY','GIT_ALTERNATE_OBJECT_DIRECTORIES'):
 if k in os.environ: raise SystemExit('Refusing inherited '+k)
receipt=out/'loop-to32-receipt.json'
if not receipt.is_file():raise SystemExit('Missing completed physical-loop receipt')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
inputs=[receipt,out/'PA194PhysicalLoopTo32.olean',out/'PA194Site31PhysicalClock.olean',src/'PA194SourceLoopTo32.lean',src/'PA194MatchedLoopTo32.lean']
before={str(p):digest(p) for p in inputs}
lake=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,text=True).strip()
search=':'.join(map(str,[out,matched,tail,carry,baseline,fetch/'foundation-view',project,package]))+':'+lake
for module,thm in [('PA194SourceLoopTo32','reaches32'),('PA194MatchedLoopTo32','matched')]:
 dest=out/(module+'.lean');obj=out/(module+'.olean')
 if dest.exists() or obj.exists():raise SystemExit('Refusing to overwrite '+module)
 shutil.copyfile(src/(module+'.lean'),dest)
 print('Checking',module,flush=True)
 r=subprocess.run(['lake','env','env','LEAN_PATH='+search,'lean','-M6000','-j1','-R',str(out),'-o',str(obj),str(dest)],cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print(r.stdout,end='',flush=True)
 if r.returncode or 'sorryAx' in r.stdout or f"'{module}.{thm}' depends on axioms:" not in r.stdout:raise SystemExit('Failed '+module)
for name,h in before.items():
 if digest(Path(name))!=h:raise SystemExit('Input changed: '+name)
(out/'matched-loop-extension-receipt.json').write_text(json.dumps({'input_sha256':before},indent=2)+'\n')
print('PASS: matched model-level source/physical loop to site 32; prebuilt foundations remain.',flush=True)
