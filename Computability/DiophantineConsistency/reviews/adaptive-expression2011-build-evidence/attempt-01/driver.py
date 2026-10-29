from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs'); D=R/'Computability/DiophantineConsistency';P=Path('/tmp/adaptive13-refresh-p6h7b6p0');S=D/'Lean/DiophantineConsistency'
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
s=json.loads((P/'state.json').read_text());assert s['status']=='PASS' and len(s['records'])==24
p=json.loads((P/'plan.json').read_text());
for z in p['pins']:assert h(z['path'])==z['sha256'],z['path']
for z in s['records']:
 assert z['exit']==0 and h(P/'lib'/Path(*z['module'].split('.')).with_suffix('.olean'))==z['object_sha256']
assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive13-leaves-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py')
names=['AdaptiveEquationSyntax2011','AdaptiveEquationSyntax2011Checks','NativeAdaptiveExpression2011','NativeAdaptiveExpression2011Checks']
for n in names:shutil.copyfile(S/(n+'.lean'),logs/(n+'.lean'))
state={'status':'RUNNING','records':[],'private':str(w),'snapshots':{n:h(logs/(n+'.lean')) for n in names},'refresh_state_sha256':h(P/'state.json')}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True)
env=dict(os.environ,LEAN_PATH=':'.join([str(lib),str(P/'lib'),*p['boundary_search']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
try:
 for n in names:
  src=S/(n+'.lean');assert h(src)==state['snapshots'][n];assert shutil.disk_usage('/tmp').free>=512*1024**2
  out=lib/'DiophantineConsistency'/(n+'.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists();log=logs/(n+'.log');timing=logs/(n+'.time');cmd=[p['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',n,flush=True); t=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'name':n,'command':cmd,'exit':code,'seconds':time.monotonic()-t,'source_sha256':h(src),'log_sha256':h(log),'time_sha256':h(timing)}
  if out.exists():row['object_sha256']=h(out)
  state['records'].append(row);save();print('DONE',n,code,round(row['seconds'],2),flush=True);print(log.read_text(),flush=True)
  if code:raise RuntimeError(n)
  assert h(src)==state['snapshots'][n]
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
