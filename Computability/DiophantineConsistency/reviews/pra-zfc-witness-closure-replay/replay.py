#!/usr/bin/env python3
"""Build the frozen ZFC axiom witness-bound suffix over the strict project parent."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
ROOT=Path(__file__).resolve().parents[4];PACKET=Path(__file__).resolve().parent
PARENT=Path('/tmp/pra-witness-local-closure-successor-qj4ojxc9');M=json.loads((PACKET/'manifest.json').read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
work=Path(tempfile.mkdtemp(prefix='pra-zfc-witness-closure-'));src=work/'src';lib=work/'lib';logs=work/'logs';logs.mkdir();(lib/'DiophantineConsistency').mkdir(parents=True);(lib/'ZFCinPA').mkdir();(src/'DiophantineConsistency').mkdir(parents=True);(src/'ZFCinPA').mkdir()
for module in M['order']:
 ns,n=module.split('.');shutil.copyfile(PACKET/'frozen'/ns/(n+'.lean'),src/ns/(n+'.lean'))
for n in M['parent_objects']:(lib/'DiophantineConsistency'/(n+'.olean')).symlink_to((PARENT/'lib/DiophantineConsistency'/(n+'.olean')).resolve())
(lib/'Foundation').symlink_to((PARENT/'lib/Foundation').resolve(),target_is_directory=True)
(lib/'ZFCinPA/Instances.olean').symlink_to((PARENT/'lib/ZFCinPA/Instances.olean').resolve())
base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip().split(':');base=[x for x in base if not x.startswith(str(ROOT/'.lake/build/lib/lean'))]
env=dict(os.environ,LEAN_PATH=str(lib)+':'+':'.join(base),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
state={'status':'RUNNING','root':str(work),'manifest_sha256':sha(PACKET/'manifest.json'),'parent':str(PARENT),'records':[],'scope':M['scope']}
def save():
 (work/'state.tmp').write_text(json.dumps(state,indent=2)+'\n');(work/'state.tmp').replace(work/'state.json')
def audit():
 assert sha(PACKET/'manifest.json')==state['manifest_sha256'] and sha(PARENT/'state.json')==M['parent_state_sha256']
 assert all(sha(src/(m.replace('.','/')+'.lean'))==h for m,h in M['source_sha256'].items())
 assert all(sha(lib/'DiophantineConsistency'/(n+'.olean'))==h for n,h in M['parent_objects'].items())
 assert all(sha(lib/p)==h for p,h in M['external_anchors'].items())
save();print('ROOT',work,'project parent',len(M['parent_objects']),'suffix',len(M['order']),flush=True)
try:
 audit()
 for m in M['order']:
  state['module']=m;save();f=src/(m.replace('.','/')+'.lean');obj=lib/(m.replace('.','/')+'.olean');log=logs/(m+'.log');t=time.monotonic()
  with log.open('w') as o:r=subprocess.run(['lean','-M6000','-j1','-DElab.async=false','--root='+str(src),str(f),'-o',str(obj)],cwd=ROOT,env=env,stdout=o,stderr=subprocess.STDOUT)
  row={'module':m,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(f),'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log)};state['records'].append(row);save()
  if r.returncode!=0 or re.search(r'\b(?:warning|error|sorryAx)\b',log.read_text()):raise RuntimeError('failed '+m)
  print('PASS',m,flush=True)
 audit();state.update(status='PASS',module=None);save();print('PASS',work,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
