#!/usr/bin/env python3
"""Rebuild the native positive subtraction implication proof on its authenticated parent."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
ROOT=Path(__file__).resolve().parents[4];PACKET=Path(__file__).resolve().parent
M=json.loads((PACKET/'manifest.json').read_text());PARENT=Path(M['parent']);sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
work=Path(tempfile.mkdtemp(prefix='ipra-induction-nozero-'));src=work/'src/DiophantineConsistency';src.mkdir(parents=True);lib=work/'lib';dest=lib/'DiophantineConsistency';dest.mkdir(parents=True);logs=work/'logs';logs.mkdir()
for n in M['order']:shutil.copyfile(PACKET/'frozen/DiophantineConsistency'/(n+'.lean'),src/(n+'.lean'))
for n in M['parent_objects']:(dest/(n+'.olean')).symlink_to((PARENT/'lib/DiophantineConsistency'/(n+'.olean')).resolve())
for n in ['Foundation','ZFCinPA']:(lib/n).symlink_to((PARENT/'lib'/n).resolve(),target_is_directory=True)
env=dict(os.environ,LEAN_PATH=str(lib)+':'+':'.join(M['package_path']),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
state={'status':'RUNNING','root':str(work),'manifest_sha256':sha(PACKET/'manifest.json'),'parent':str(PARENT),'records':[],'scope':M['scope']}
def save():
 (work/'state.tmp').write_text(json.dumps(state,indent=2)+'\n');(work/'state.tmp').replace(work/'state.json')
def audit():
 assert sha(PACKET/'manifest.json')==state['manifest_sha256'] and sha(PARENT/'state.json')==M['parent_state_sha256']
 assert sha(PACKET/'replay.py') == M['driver_sha256']
 assert sha(Path(M['lean']))==M['lean_sha256']
 assert all(sha(ROOT/p)==h for p,h in M['workspace_sources'].items())
 assert all(sha(src/(n+'.lean'))==h for n,h in M['suffix_sources'].items())
 assert all(sha(dest/(n+'.olean'))==h for n,h in M['parent_objects'].items())
 assert all(sha(lib/p)==h for p,h in M['external_objects'].items())
save();print('ROOT',work,'source guards',len(M['workspace_sources']),'parent objects',len(M['parent_objects']),'external objects',len(M['external_objects']),'suffix',len(M['order']),flush=True)
try:
 audit()
 for n in M['order']:
  state['module']=n;save();f=src/(n+'.lean');obj=dest/(n+'.olean');log=logs/(n+'.log');t=time.monotonic()
  with log.open('w') as o:r=subprocess.run([M['lean'],'-M6000','-j1','-DElab.async=false','--root='+str(src.parent),str(f),'-o',str(obj)],cwd=ROOT,env=env,stdout=o,stderr=subprocess.STDOUT)
  row={'module':n,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(f),'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log)};state['records'].append(row);save()
  if r.returncode!=0 or re.search(r'\b(?:warning|error|sorryAx)\b',log.read_text()):raise RuntimeError('failed '+n)
  print('PASS',n,flush=True)
 audit();report=(logs/'IPRASubSuccZeroNativeChecks.log').read_text();match=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S);assert match and set(re.findall(r'[A-Za-z_.]+',match.group(1))) == {'propext','Classical.choice','Quot.sound'};state.update(status='PASS',module=None);save();print('PASS',work,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
