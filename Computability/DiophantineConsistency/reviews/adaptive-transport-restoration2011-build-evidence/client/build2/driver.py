from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs'); S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
A=Path('/tmp/adaptive13-transport-port-q5fnwwyt'); B=Path('/tmp/adaptive13-radix-div-4ujalh6u')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for base in [A,B]:
 state=json.loads((base/'state.json').read_text());assert state['status']=='PASS'
 for x in state['records']:
  assert sha(S/(x['name']+'.lean'))==x['source_sha256']; assert sha(base/'lib/DiophantineConsistency'/(x['name']+'.olean'))==x['object_sha256']
names=['ArithmeticAdaptiveTransportRestoration2011','ArithmeticAdaptiveTransportRestoration2011Checks']
assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive13-transport-restored-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py');providers={};overlaps=0
for base in [A/'lib',B/'lib']:
 for f in base.rglob('*'):
  if not f.is_file():continue
  rel=f.relative_to(base);dest=lib/rel
  if dest.exists():
   assert sha(dest)==sha(f),str(rel);overlaps+=1;continue
  dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve());providers[str(f)]=sha(f)
print('OVERLAPS',overlaps,flush=True)
for n in names:shutil.copyfile(S/(n+'.lean'),logs/(n+'.lean'))
(w/'providers.json').write_text(json.dumps(providers,indent=2)+'\n')
p=json.loads(Path('/tmp/arithmetic-signed-pairs-peer-f4gz2l0f/inputs.json').read_text());boundary=p['LEAN_PATH'][1:];assert all('/.lake/packages/' in x or '/toolchains/' in x for x in boundary)
state={'status':'RUNNING','private':str(w),'snapshots':{n:sha(logs/(n+'.lean')) for n in names},'records':[],'providers_sha256':sha(w/'providers.json'),'parents':{str(x):sha(x/'state.json') for x in [A,B]},'overlaps':overlaps}
def save(): (w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
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
 for f,h in providers.items():assert sha(f)==h
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
