"""Scoped generic one-sided HA assembler replay over a historical provider."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';P=Path('/tmp/ha-expression-assembly-vgttkwsl');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());ps=read(P/'state.json');assert ps['status']=='PASS';ph=sha(P/'state.json');mods=['HAExpressionImplication','HAExpressionImplicationChecks'];snap={n:sha(SRC/(n+'.lean')) for n in mods};inventory={}
# Project namespace directory symlinks are traversed; external Foundation and
# package/Mathlib fallback remain historical boundaries.
for top in (P/'lib').iterdir():
 if top.name in ('Foundation','Mathlib') or not top.is_dir():continue
 for root,dirs,files in os.walk(top,followlinks=True):
  for f in files:
   if f.endswith('.olean'):
    p=Path(root)/f;inventory[str(p.relative_to(P/'lib'))]={'path':str(p.resolve()),'sha256':sha(p)}
assert 'DiophantineConsistency/HAExpressionAssembly.olean' in inventory
w=Path(tempfile.mkdtemp(prefix='ha-expression-implication-'));(w/'logs').mkdir();shutil.copyfile(__file__,w/'driver.py');(w/'providers.json').write_text(json.dumps(inventory,indent=2,sort_keys=True)+'\n');ih=sha(w/'providers.json');lib=w/'lib';lib.mkdir()
for top in (P/'lib').iterdir():
 if top.name!='DiophantineConsistency':(lib/top.name).symlink_to(top.resolve(),target_is_directory=top.is_dir());continue
 for root,dirs,files in os.walk(top,followlinks=True):
  for f in files:
   p=Path(root)/f;q=lib/p.relative_to(P/'lib');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(p.resolve())
for n in mods:shutil.copyfile(SRC/(n+'.lean'),w/'logs'/(n+'.lean'))
state={'status':'RUNNING','private':str(w),'parent_state_sha256':ph,'provider_inventory_sha256':ih,'provider_count':len(inventory),'source_sha256':snap,'records':[],'scope':'Generic conditional one-sided HA proof assembler only. Historical HA/ZFC, Foundation, Mathlib/package and fallback source boundaries remain inherited; no 85 bridge or equivalence is claimed.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
def auth():
 return sha(P/'state.json')==ph and sha(w/'providers.json')==ih and all(sha(SRC/(n+'.lean'))==h for n,h in snap.items()) and all(sha(x['path'])==x['sha256'] for x in inventory.values()) and all(sha(P/'lib/DiophantineConsistency'/(r['module']+'.olean'))==r['object_sha256'] and sha(P/'logs'/(r['module']+'.log'))==r['log_sha256'] for r in ps['records'])
save();print('PRIVATE',w,'PROVIDERS',len(inventory),flush=True)
try:
 assert auth();path=ps['LEAN_PATH'].split(':');assert path[0]==str(P/'lib');env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*path[1:]]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in mods:
  src=SRC/(n+'.lean');out=lib/'DiophantineConsistency'/(n+'.olean');log=w/'logs'/(n+'.log');tim=w/'logs'/(n+'.time');assert not out.exists() and sha(src)==snap[n];cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M8000','-j1','-DElab.async=false','-o',str(out),str(src)];start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  r={'name':n,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim),'command':cmd,'object_sha256':sha(out) if out.is_file() else None};state['records'].append(r);save();print('DONE',n,code,flush=True)
  if code:raise RuntimeError(n)
 assert auth() and all(sha(w/'logs'/(r['name']+'.lean'))==r['source_sha256'] and sha(lib/'DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256'] and sha(w/'logs'/(r['name']+'.log'))==r['log_sha256'] for r in state['records']);state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
