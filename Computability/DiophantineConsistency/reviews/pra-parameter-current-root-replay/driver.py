#!/usr/bin/env python3
"""Replay a frozen source-current PRA parameter-refactor snapshot.

Usage: python replay.py --parent /tmp/herbrand-universal-preparation-author/lib
An inherited Foundation/mathlib cache remains in scope; this is not a fresh
transitive Foundation build. No Git mutation or shared object overwrite occurs.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,tempfile,time

ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
SRC=ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
HERE=Path(__file__).resolve().parent
MANIFEST=json.loads((HERE/'manifest.json').read_text()); M=MANIFEST['modules']
REBUILD=MANIFEST['rebuild']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--parent',required=True,type=Path);args=ap.parse_args();parent=args.parent.resolve()
for n,row in M.items():
 src=SRC/(n+'.lean')
 if not src.is_file() or sha(src)!=row['source_sha256']:
  raise SystemExit('Source does not match frozen manifest: '+str(src))
 if n not in REBUILD:
  obj=parent/'DiophantineConsistency'/(n+'.olean')
  if not obj.is_file() or sha(obj)!=row['object_sha256']:
   raise SystemExit('Inherited object does not match frozen manifest: '+str(obj))
root=Path(tempfile.mkdtemp(prefix='pra-parameter-independent-'));lib=root/'lib';lib.mkdir();dst=lib/'DiophantineConsistency';dst.mkdir();logs=root/'logs';logs.mkdir();(lib/'Foundation').symlink_to((parent/'Foundation').resolve(),target_is_directory=True)
for f in (parent/'DiophantineConsistency').glob('*.olean'):
 if f.stem not in REBUILD:(dst/f.name).symlink_to(f.resolve())
base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':'+base,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
state={'status':'RUNNING','parent':str(parent),'root':str(root),'records':[],'LEAN_PATH':env['LEAN_PATH'],'qualification':'Inherited Foundation/mathlib cache is not a fresh transitive rebuild.'};(root/'state.json').write_text(json.dumps(state,indent=2)+'\n')
for n in REBUILD:
 src=SRC/(n+'.lean');snapshot=logs/(n+'.lean');snapshot.write_bytes(src.read_bytes());assert sha(snapshot)==M[n]['source_sha256'];obj=dst/(n+'.olean');cmd=['lean','-M6000','-j1','-DElab.async=false',str(src),'-o',str(obj)];start=time.monotonic();p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log=logs/(n+'.log');log.write_text(p.stdout);row={'module':n,'exit':p.returncode,'seconds':time.monotonic()-start,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.is_file() else None,'log_sha256':sha(log),'command':cmd};state['records'].append(row);(root/'state.json').write_text(json.dumps(state,indent=2)+'\n');print(n,p.returncode,flush=True)
 if p.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',p.stdout):
  state['status']='FAILED';(root/'state.json').write_text(json.dumps(state,indent=2)+'\n');raise SystemExit(p.stdout or 'Compile failed')
 if sha(src)!=M[n]['source_sha256']:raise SystemExit('Source changed during build: '+str(src))
 if row['object_sha256']!=M[n]['object_sha256']:raise SystemExit('Object differs from frozen build: '+n)
state['status']='PASS';(root/'state.json').write_text(json.dumps(state,indent=2)+'\n');print('PASS',root,flush=True)
