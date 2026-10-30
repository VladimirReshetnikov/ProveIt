"""Provisional exact direct-ordinate source rebase on the historical 87 machine provider.

The full selected provider inventory is rehashed before and after. The 87 machine
provider and its inherited package/Foundation boundaries are *not* asserted to
be source-current; the outcome does not prove internal HA/PRA provability.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');SRC=R/'Computability/DiophantineConsistency/Lean';M=Path('/tmp/adaptive-unconditional-equivalence-ptaobui4');B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());ms=read(M/'state.json');bs=read(B/'state.json');assert ms['status']==bs['status']=='PASS';mh=sha(M/'state.json');bh=sha(B/'state.json');seen=set();build=[];boundary=[]
def visit(n):
 if n in seen:return
 seen.add(n);obj=M/'lib'/('/'.join(n.split('.'))+'.olean')
 if obj.is_file():boundary.append(n);return
 p=SRC/('/'.join(n.split('.'))+'.lean')
 if not p.is_file():boundary.append(n);return
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for x in line[7:].split():visit(x)
 build.append(n)
visit('DiophantineConsistency.AdaptiveDirectOrdinate86Machine');assert len(build)==25 and build[-1]=='DiophantineConsistency.AdaptiveDirectOrdinate86Machine';snap={n:sha(SRC/('/'.join(n.split('.'))+'.lean')) for n in build}
# Walk directory symlinks as well; record resolved selected objects, not just leaf overlays.
providers={}
for root,dirs,files in os.walk(M/'lib',followlinks=True):
 for f in files:
  p=Path(root)/f
  if f.endswith('.olean'):
   key=str(p.relative_to(M/'lib'));providers[key]={'path':str(p.resolve()),'sha256':sha(p)}
assert len(providers)==507
for n in boundary:
 key='/'.join(n.split('.'))+'.olean'
 if n.startswith('DiophantineConsistency.'):assert key in providers, n
w=Path(tempfile.mkdtemp(prefix='adaptive86-machine-rebase-'));(w/'logs').mkdir();lib=w/'lib';shutil.copyfile(__file__,w/'driver.py');(w/'providers.json').write_text(json.dumps(providers,indent=2,sort_keys=True)+'\n');ph=sha(w/'providers.json')
for n in build:
 p=SRC/('/'.join(n.split('.'))+'.lean');q=w/'logs'/(n.split('.')[-1]+'.lean');shutil.copyfile(p,q)
for root,dirs,files in os.walk(M/'lib',followlinks=True):
 for f in files:
  p=Path(root)/f;dst=lib/p.relative_to(M/'lib');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(p.resolve())
state={'status':'RUNNING','private':str(w),'machine_state_sha256':mh,'boundary_state_sha256':bh,'provider_inventory_sha256':ph,'selected_provider_count':len(providers),'build_order':build,'direct_boundaries':boundary,'source_sha256':snap,'records':[],'scope':'Provisional 25-module current 86-source rebase on independently replayed historical 87 machine provider; complete selected object bytes reauthenticated, inherited project/package/Foundation source boundaries remain historical; no complete current-source closure or HA/PRA provability claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
def auth():
 return sha(M/'state.json')==mh and sha(B/'state.json')==bh and sha(w/'providers.json')==ph and all(sha(SRC/('/'.join(n.split('.'))+'.lean'))==h for n,h in snap.items()) and all(sha(x['path'])==x['sha256'] for x in providers.values())
save();print('PRIVATE',w,'MODULES',len(build),'PROVIDERS',len(providers),flush=True)
try:
 assert auth();env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in build:
  short=n.split('.')[-1];src=SRC/('/'.join(n.split('.'))+'.lean');out=lib/('/'.join(n.split('.'))+'.olean');log=w/'logs'/(short+'.log');tim=w/'logs'/(short+'.time');assert not out.exists() and sha(src)==snap[n];cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',short,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'name':n,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim),'command':cmd}
  if out.exists():row['object_sha256']=sha(out)
  state['records'].append(row);save();print('DONE',short,code,flush=True)
  if code:raise RuntimeError(n)
 assert auth() and all(sha(w/'logs'/(r['name'].split('.')[-1]+'.lean'))==r['source_sha256'] and sha(lib/('/'.join(r['name'].split('.'))+'.olean'))==r['object_sha256'] and sha(w/'logs'/(r['name'].split('.')[-1]+'.log'))==r['log_sha256'] and sha(w/'logs'/(r['name'].split('.')[-1]+'.time'))==r['time_sha256'] for r in state['records']);state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
