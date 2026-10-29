#!/usr/bin/env python3
"""Replay universal syntax from a validated independent equivalence overlay.

Usage: python replay.py --parent /tmp/pra-universal-independent-.../lib
Historical probes are not executable inputs. Foundation/mathlib is inherited.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,tempfile,time
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs');SRC=ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';HERE=Path(__file__).resolve().parent;manifest=json.loads((HERE/'manifest.json').read_text());modules=manifest['modules'];parent_modules=manifest['parent_modules'];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();names=['PRAUniversalSyntax','PRAUniversalAxiomSyntax','PRAUniversalSyntaxChecks','PRAUniversalAxiomSyntaxChecks'];ap=argparse.ArgumentParser();ap.add_argument('--parent',required=True,type=Path);parent=ap.parse_args().parent.resolve()
for n,row in parent_modules.items():
 src=SRC/(n+'.lean');obj=parent/'DiophantineConsistency'/(n+'.olean')
 if not src.is_file() or sha(src)!=row['source_sha256']:raise SystemExit('Parent source differs: '+str(src))
 if not obj.is_file() or sha(obj)!=row['object_sha256']:raise SystemExit('Parent object differs: '+str(obj))
for n,row in modules.items():
 src=SRC/(n+'.lean')
 if not src.is_file() or sha(src)!=row['source_sha256']:raise SystemExit('Syntax source differs: '+str(src))
root=Path(tempfile.mkdtemp(prefix='pra-universal-syntax-independent-'));lib=root/'lib';lib.mkdir();dst=lib/'DiophantineConsistency';dst.mkdir();logs=root/'logs';logs.mkdir();(lib/'Foundation').symlink_to((parent/'Foundation').resolve(),target_is_directory=True)
for f in (parent/'DiophantineConsistency').glob('*.olean'):
 if f.stem not in names:(dst/f.name).symlink_to(f.resolve())
base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':'+base,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
state={'status':'RUNNING','parent':str(parent),'root':str(root),'records':[],'LEAN_PATH':env['LEAN_PATH'],'qualification':manifest['qualification']};(root/'state.json').write_text(json.dumps(state,indent=2)+'\n')
for n in names:
 src=SRC/(n+'.lean');snap=logs/(n+'.lean');snap.write_bytes(src.read_bytes());obj=dst/(n+'.olean');cmd=['lean','-M6000','-j1','-DElab.async=false',str(src),'-o',str(obj)];t=time.monotonic();p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log=logs/(n+'.log');log.write_text(p.stdout);row={'module':n,'exit':p.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.is_file() else None,'log_sha256':sha(log),'command':cmd};state['records'].append(row);(root/'state.json').write_text(json.dumps(state,indent=2)+'\n');print(n,p.returncode,flush=True)
 if p.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',p.stdout):state['status']='FAILED';(root/'state.json').write_text(json.dumps(state,indent=2)+'\n');raise SystemExit(p.stdout or 'Compile failed')
 if sha(src)!=modules[n]['source_sha256'] or sha(snap)!=sha(src):raise SystemExit('Source changed during build: '+n)
 if row['object_sha256']!=modules[n]['object_sha256']:raise SystemExit('Object differs from frozen build: '+n)
state['status']='PASS';(root/'state.json').write_text(json.dumps(state,indent=2)+'\n');print('PASS',root,flush=True)
