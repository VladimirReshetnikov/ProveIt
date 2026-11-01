"""Guarded successor-to-x+1 induction conversion in an arbitrary theory.

Parent and package ancestry remain historical, and no backward implication is proved.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4]
SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
P=Path('/tmp/ipra-add-one-general-rvuoq7mn')
PACKAGE=Path('/tmp/ha87-full-source-jrvxi6bb/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
state_parent=json.loads((P/'state.json').read_text()); assert state_parent['status']=='PASS'
parent_hash=sha(P/'state.json');parent_inv_hash=sha(P/'providers.json');assert parent_inv_hash==state_parent['provider_inventory_sha256']
names=['IPRASuccessorInductionConverse','IPRASuccessorInductionConverseChecks']
sourceh={n:sha(SRC/(n+'.lean')) for n in names}; lean_hash=sha(LEAN)
w=Path(tempfile.mkdtemp(prefix='ipra-successor-induction-converse-'));lib=w/'lib';lib.mkdir();(w/'src/DiophantineConsistency').mkdir(parents=True);(w/'logs').mkdir();shutil.copyfile(__file__,w/'driver.py')
for n in names:
 for d in [w/'src/DiophantineConsistency',w/'logs']:shutil.copyfile(SRC/(n+'.lean'),d/(n+'.lean'))
# Preserve the authenticated, actual paths, including symlinked namespaces.
selected={}
for root,dirs,files in os.walk(P/'lib',followlinks=True):
 for f in files:
  if '.olean' in f or f.endswith('.ir'):
   p=Path(root)/f;rel=str(p.relative_to(P/'lib'));selected[rel]={'path':str(p.resolve()),'sha256':sha(p)}
for rel,v in selected.items():
 out=lib/rel;out.parent.mkdir(parents=True,exist_ok=True);out.symlink_to(v['path'])
(w/'providers.json').write_text(json.dumps(selected,indent=2,sort_keys=True)+'\n');inv_hash=sha(w/'providers.json')
state={'status':'RUNNING','private':str(w),'parent':str(P),'parent_state_sha256':parent_hash,'parent_inventory_sha256':parent_inv_hash,'provider_inventory_sha256':inv_hash,'provider_objects':len(selected),'source_sha256':sourceh,'lean_sha256':lean_hash,'scope':'In any intuitionistic theory proving the native defining and equality axiom schemas, any finite-parameter successor-induction instance yields the matching x+1 instance. Add-one is derived from defining/equality schemas without induction. This proves the converse schema direction, not complete standard-iPRA presentation equivalence or complete transitive source provenance. Parent project, Foundation and package ancestry remain historical.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def auth():
 if sha(LEAN)!=lean_hash or sha(P/'state.json')!=parent_hash or sha(P/'providers.json')!=parent_inv_hash or sha(w/'providers.json')!=inv_hash:return False
 if not all(sha(SRC/(n+'.lean'))==h and sha(w/'src/DiophantineConsistency'/(n+'.lean'))==h and sha(w/'logs'/(n+'.lean'))==h for n,h in sourceh.items()):return False
 if not all(sha(v['path'])==v['sha256'] and sha(lib/k)==v['sha256'] for k,v in selected.items()):return False
 for row in state_parent['records']:
  n=row['name']
  obj=P/'lib'/Path(n.replace('.','/')+'.olean') if '.' in n else P/'lib/DiophantineConsistency'/(n+'.olean')
  if sha(obj)!=row['object_sha256'] or sha(P/'logs'/(n+'.log'))!=row['log_sha256']:return False
 return True
save();print('PRIVATE',w,flush=True)
try:
 assert auth();env=dict(os.environ,LEAN_PATH=f'{lib}:{PACKAGE}',LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['records']=[]
 for n in names:
  out=lib/'DiophantineConsistency'/(n+'.olean');assert not out.exists();cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10',str(LEAN),'--root='+str(w/'src'),'-M8000','-j1','-DElab.async=false','-o',str(out),str(w/'src/DiophantineConsistency'/(n+'.lean'))];t=time.monotonic()
  with (w/'logs'/(n+'.log')).open('w') as log:code=subprocess.run(['/usr/bin/time','-v','-o',str(w/'logs'/(n+'.time')),*cmd],cwd=R,env=env,stdout=log,stderr=subprocess.STDOUT).returncode
  state['records'].append(dict(name=n,exit=code,object_sha256=sha(out) if out.exists() else None,log_sha256=sha(w/'logs'/(n+'.log')),seconds=time.monotonic()-t));save();print(n,code,flush=True);assert code==0
 assert auth();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=repr(e));save();raise
