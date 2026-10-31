"""Replay a Pell-index counterexample against a historical boundary."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4]
SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
P=Path('/tmp/adaptive86-machine-compat-rebase-v13-jld1zn0t')
B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl')
names=['AdaptiveGap85SmallIndexExample']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
ps,bs=read(P/'state.json'),read(B/'state.json')
assert ps['status']==bs['status']=='PASS'
sourceh={n:sha(SRC/(n+'.lean')) for n in names}
anchor={str(x):sha(x/'state.json') for x in [P,B]}
inventory=read(P/'providers.json'); inventoryhash=sha(P/'providers.json')
assert len(inventory)==507
pell=next(r for r in ps['records'] if r['name']=='DiophantineConsistency.ArithmeticPellResidueAux')
pellsource=SRC/'ArithmeticPellResidueAux.lean'
assert sha(pellsource)==pell['source_sha256']
w=Path(tempfile.mkdtemp(prefix='adaptive-gap85-small-index-'));lib=w/'lib';lib.mkdir();(w/'logs').mkdir();shutil.copyfile(__file__,w/'driver.py')
for name in names:shutil.copyfile(SRC/(name+'.lean'),w/'logs'/(name+'.lean'))
for top in (P/'lib').iterdir():
 if top.name!='DiophantineConsistency':(lib/top.name).symlink_to(top.resolve(),target_is_directory=top.is_dir());continue
 for root,dirs,files in os.walk(top,followlinks=True):
  for f in files:
   path=Path(root)/f;dest=lib/path.relative_to(P/'lib');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(path.resolve())
state={'status':'RUNNING','private':str(w),'sources':sourceh,'parent_state_sha256':anchor,'provider_inventory_sha256':inventoryhash,'selected_inherited_objects':len(inventory),'parent_outputs':len(ps['records']),'pell_source_sha256':pell['source_sha256'],'records':[],'scope':'One explicit Pell-index example is compiled from current source over an inherited historical v13 model/Foundation/package boundary. It checks no actual factor-unit or full 85-zero claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
def auth():
 return all(sha(SRC/(n+'.lean'))==h and sha(w/'logs'/(n+'.lean'))==h for n,h in sourceh.items()) and all(sha(Path(x)/'state.json')==h for x,h in anchor.items()) and sha(P/'providers.json')==inventoryhash and sha(pellsource)==pell['source_sha256'] and all(sha(x['path'])==x['sha256'] for x in inventory.values()) and all(sha(P/'lib'/(r['name'].replace('.','/')+'.olean'))==r['object_sha256'] and sha(P/'logs'/(r['name'].split('.')[-1]+'.log'))==r['log_sha256'] for r in ps['records'])
save();print('PRIVATE',w,flush=True)
try:
 assert auth();env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for name in names:
  out=lib/'DiophantineConsistency'/(name+'.olean');assert not out.exists();cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(SRC/(name+'.lean'))];start=time.monotonic()
  with (w/'logs'/(name+'.log')).open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(w/'logs'/(name+'.time')),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'name':name,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sourceh[name],'object_sha256':sha(out) if out.exists() else None,'log_sha256':sha(w/'logs'/(name+'.log')),'time_sha256':sha(w/'logs'/(name+'.time'))};state['records'].append(row);save();assert code==0 and auth();print('PASS',name,flush=True)
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=repr(e));save();raise
