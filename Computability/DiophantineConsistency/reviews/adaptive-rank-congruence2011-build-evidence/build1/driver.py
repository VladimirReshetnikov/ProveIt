from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';S=D/'Lean/DiophantineConsistency';parent=Path('/tmp/adaptive13-factor-three-7_xn03uk')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
s=json.loads((parent/'state.json').read_text());assert s['status']=='PASS'
for row in s['records']:
 assert sha(S/(row['name']+'.lean'))==row['source_sha256'];assert sha(parent/'lib/DiophantineConsistency'/(row['name']+'.olean'))==row['object_sha256']
p=json.loads(Path('/tmp/arithmetic-signed-pairs-peer-f4gz2l0f/inputs.json').read_text());boundary=p['LEAN_PATH'][1:]
assert all('/.lake/packages/' in x or '/toolchains/' in x for x in boundary)
assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive13-rank-congruence-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py');providers=[]
for f in (parent/'lib').rglob('*'):
 if f.is_file():
  dest=lib/f.relative_to(parent/'lib');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve());providers.append({'path':str(f),'sha256':sha(f),'bytes':f.stat().st_size})
rel=Path('Mathlib/Data/ZMod/Basic.olean');first=next(Path(x)/rel for x in boundary if (Path(x)/rel).is_file());providers.append({'path':str(first),'sha256':sha(first),'bytes':first.stat().st_size})
src=R/'.lake/packages/mathlib/Mathlib/Data/ZMod/Basic.lean';providers.append({'path':str(src),'sha256':sha(src),'bytes':src.stat().st_size})
(w/'providers.json').write_text(json.dumps(providers,indent=2)+'\n')
names=['ArithmeticAdaptiveRankCongruence2011','ArithmeticAdaptiveRankCongruence2011Checks']
for n in names:shutil.copyfile(S/(n+'.lean'),logs/(n+'.lean'))
state={'status':'RUNNING','private':str(w),'snapshots':{n:sha(logs/(n+'.lean')) for n in names},'records':[],'providers_sha256':sha(w/'providers.json'),'parent_state_sha256':sha(parent/'state.json')}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True);env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*boundary]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
try:
 for n in names:
  src=S/(n+'.lean');assert sha(src)==state['snapshots'][n];assert shutil.disk_usage('/tmp').free>=512*1024**2
  out=lib/'DiophantineConsistency'/(n+'.olean');assert not out.exists();log=logs/(n+'.log');tim=logs/(n+'.time');cmd=['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',n,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'name':n,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim)}
  if out.exists():row['object_sha256']=sha(out)
  state['records'].append(row);save();print('DONE',n,code,round(row['seconds'],2),flush=True);print(log.read_text(),flush=True)
  if code:raise RuntimeError(n)
  assert sha(src)==state['snapshots'][n]
 for x in providers:assert sha(x['path'])==x['sha256']
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
