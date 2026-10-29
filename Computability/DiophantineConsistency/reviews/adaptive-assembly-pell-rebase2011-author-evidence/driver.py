from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';B=Path(os.environ['ADAPTIVE_HALF_BASE']);P=Path('/tmp/adaptive13-assembly-pell-mg258xlh')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
names=['ArithmeticOuterSeed','ArithmeticConstructionBoundPell'];bs=read(B/'state.json');assert bs['status']=='PASS';assert shutil.disk_usage('/tmp').free>=512*1024**2
for r in bs['records']:assert sha(S/(r['name']+'.lean'))==r['source_sha256'] and sha(B/'lib/DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256']
w=Path(tempfile.mkdtemp(prefix='adaptive13-assembly-pell-rebase-'));logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py');shutil.copyfile('/tmp/adaptive13-assembly-pell-rebase-audit.py',w/'audit.py');print('PRIVATE',w,flush=True);env=dict(os.environ,ADAPTIVE_HALF_BASE=str(B),ADAPTIVE_PELL_REBASE_AUDIT_OUT=str(w/'audit.json'))
with (w/'audit.log').open('w') as f:code=subprocess.run(['python3',str(w/'audit.py')],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
assert code==0,(w/'audit.log').read_text();a=read(w/'audit.json');assert a['base_state_sha256']==sha(B/'state.json') and a['seed_state_sha256']==sha(P/'state.json')
lib=w/'lib';lib.mkdir();providers=[]
for f in (B/'lib').rglob('*'):
 if f.is_file():
  rel=f.relative_to(B/'lib')
  if rel.parent==Path('DiophantineConsistency') and rel.name.split('.')[0] in names:continue
  dest=lib/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve());providers.append({'path':str(f),'sha256':sha(f),'bytes':f.stat().st_size,'origin':'base'})
for row in a['seeds']:
 rel=Path('DiophantineConsistency')/(row['module']+'.olean');dest=lib/rel;src=Path(row['object'])
 if dest.is_file():assert sha(dest)==row['object_sha256'];continue
 assert sha(src)==row['object_sha256'];dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(src.resolve());providers.append({'path':str(src),'sha256':sha(src),'bytes':src.stat().st_size,'origin':'accepted seed'})
(w/'providers.json').write_text(json.dumps(providers,indent=2)+'\n')
for n in names:shutil.copyfile(S/(n+'.lean'),logs/(n+'.lean'))
state={'status':'RUNNING','private':str(w),'snapshots':{n:sha(logs/(n+'.lean')) for n in names},'records':[],'providers_sha256':sha(w/'providers.json'),'base_state_sha256':sha(B/'state.json'),'seed_state_sha256':sha(P/'state.json'),'audit_sha256':sha(w/'audit.json'),'boundary':bs['boundary'],'scope':'two affected Pell prerequisites over current adaptive base and four seed/check objects whose exact DiophantineConsistency dependency closure is unchanged; package and cross-namespace internals inherited boundaries'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
try:
 for n in names:
  src=S/(n+'.lean');assert sha(src)==state['snapshots'][n];assert shutil.disk_usage('/tmp').free>=512*1024**2
  out=lib/'DiophantineConsistency'/(n+'.olean');assert not out.exists();log=logs/(n+'.log');tim=logs/(n+'.time');cmd=['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',n,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'name':n,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim)}
  if out.exists():row['object_sha256']=sha(out)
  state['records'].append(row);save();print('DONE',n,code,round(row['seconds'],2),flush=True);print(log.read_text(),flush=True)
  if code:raise RuntimeError(n)
 for x in providers:assert sha(x['path'])==x['sha256']
 for n in names:assert sha(S/(n+'.lean'))==state['snapshots'][n]
 for row in a['rows']:assert sha(row['source'])==row['source_sha256'] and sha(row['old_object'])==row['object_sha256'] and sha(row['new_object'])==row['object_sha256']
 for row in a['seeds']:assert sha(row['source'])==row['source_sha256'] and sha(row['object'])==row['object_sha256']
 for r in bs['records']:assert sha(S/(r['name']+'.lean'))==r['source_sha256']
 assert sha(B/'state.json')==state['base_state_sha256'] and sha(P/'state.json')==state['seed_state_sha256']
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
