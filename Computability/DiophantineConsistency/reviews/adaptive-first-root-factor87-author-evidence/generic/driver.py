from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';parent=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');names=['AdaptiveFirstRootFactor87','AdaptiveFirstRootFactor87Checks']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
ps=read(parent/'state.json');assert ps['status']=='PASS';boundary=ps['boundary'];assert all('/.lake/packages/' in x or '/toolchains/' in x for x in boundary);rel=Path('Mathlib/Tactic/Ring.olean');primary=next(Path(x)/rel for x in boundary if (Path(x)/rel).is_file());mathsrc=R/'.lake/packages/mathlib/Mathlib/Tactic/Ring.lean';assert mathsrc.is_file();assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive-first-root-factor87-lean-'));lib=w/'lib';(lib/'DiophantineConsistency').mkdir(parents=True);logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py')
for n in names:shutil.copyfile(S/(n+'.lean'),logs/(n+'.lean'))
state={'status':'RUNNING','private':str(w),'snapshots':{n:sha(logs/(n+'.lean')) for n in names},'records':[],'boundary':boundary,'primary':str(primary),'primary_sha256':sha(primary),'mathsrc':str(mathsrc),'mathsrc_sha256':sha(mathsrc),'scope':'generic signed-pair identity and arbitrary-context congruence only; no full adaptive literal binding or HA proof'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True);env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*boundary]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
try:
 for n in names:
  src=S/(n+'.lean');assert sha(src)==state['snapshots'][n];out=lib/'DiophantineConsistency'/(n+'.olean');assert not out.exists();log=logs/(n+'.log');tim=logs/(n+'.time');cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M3000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',n,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  r={'name':n,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim)}
  if out.exists():r['object_sha256']=sha(out)
  state['records'].append(r);save();print('DONE',n,code,round(r['seconds'],2),flush=True);print(log.read_text(),flush=True)
  if code:raise RuntimeError(n)
 for n in names:assert sha(S/(n+'.lean'))==state['snapshots'][n]
 assert sha(primary)==state['primary_sha256'] and sha(mathsrc)==state['mathsrc_sha256'];state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
