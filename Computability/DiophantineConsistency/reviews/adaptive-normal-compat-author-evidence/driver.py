"""Build three compatibility-dependent modules of the local-normalization proof."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');P=Path(os.environ.get('ASSEMBLY_COMPAT_BUILD','/tmp/adaptive-assembly-compat-7ths2hw9'));N=Path(os.environ.get('NORMAL_INDEPENDENT_BUILD','/tmp/adaptive-normal-independent-eea6brhc'));B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';A=R/'Computability/DiophantineConsistency/research/wang-chunk-full/reauth_assembly_compat.py';T=R/'Computability/DiophantineConsistency/research/wang-chunk-full/reauth_normalization_independent.py';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());ps=read(P/'state.json');ns=read(N/'state.json');bs=read(B/'state.json');assert ps['status']==ns['status']==bs['status']=='PASS' and len(ns['records'])==40 and len(ps['records'])==8;ph=sha(P/'state.json');nh=sha(N/'state.json');ah=sha(A);th=sha(T);names=['ArithmeticLocalNormalizationDigits','ArithmeticLocalNormalizationWorld','ArithmeticLocalNormalization'];snapshots={n:sha(S/(n+'.lean')) for n in names}
w=Path(tempfile.mkdtemp(prefix='adaptive-normal-compat-'));shutil.copyfile(__file__,w/'driver.py');(w/'logs').mkdir()
for n in names:shutil.copyfile(S/(n+'.lean'),w/'logs'/(n+'.lean'))
state={'status':'RUNNING','private':str(w),'assembly_provider':str(P),'assembly_state_sha256':ph,'independent_provider':str(N),'independent_state_sha256':nh,'snapshots':snapshots,'records':[],'scope':'Private source-current build of the local-normalization proof on independently authenticated Assembly and 40-prerequisite providers; no HA proof or canonical integration claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True)
def auth(label):
 for which,script,env in [('assembly',A,dict(os.environ,ASSEMBLY_COMPAT_BUILD=str(P))),('independent',T,dict(os.environ,NORMAL_INDEPENDENT_BUILD=str(N)))]:
  q=subprocess.run(['python3',str(script)],cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(w/(label+'-'+which+'.log')).write_text(q.stdout);assert q.returncode==0,q.stdout;lines=[x for x in q.stdout.splitlines() if x.startswith('PASS ')];assert len(lines)==1;z=Path(lines[0].split()[1]);assert read(z/'state.json')['status']=='PASS';shutil.copyfile(z/'state.json',w/(label+'-'+which+'.json'));state[label+'-'+which]={'audit_path':str(z),'state_sha256':sha(w/(label+'-'+which+'.json')),'log_sha256':sha(w/(label+'-'+which+'.log'))};save();print('AUTH',label,which,z,flush=True)
def check():return sha(P/'state.json')==ph and sha(N/'state.json')==nh and sha(A)==ah and sha(T)==th and all(sha(S/(n+'.lean'))==snapshots[n] for n in names)
try:
 auth('preauth');assert check();lib=w/'lib'
 for f in (P/'lib').rglob('*'):
  if f.is_file():
   rel=f.relative_to(P/'lib')
   if rel.parent==Path('DiophantineConsistency') and any(rel.name.startswith(n+'.') for n in names):continue
   dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve())
 for row in ns['records']:
  rel=Path('DiophantineConsistency')/(row['name']+'.olean');src=N/'lib'/rel;dst=lib/rel
  if dst.exists():assert sha(dst)==row['object_sha256']
  else:dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src.resolve())
 env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in names:
  src=S/(n+'.lean');assert sha(src)==snapshots[n];o=lib/'DiophantineConsistency'/(n+'.olean');assert not o.exists();log=w/'logs'/(n+'.log');tim=w/'logs'/(n+'.time');cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(o),str(src)];print('START',n,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  rec={'name':n,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim),'command':cmd}
  if o.exists():rec['object_sha256']=sha(o)
  state['records'].append(rec);save();print('DONE',n,code,round(rec['seconds'],2),flush=True)
  if code:raise RuntimeError('Lean build failed: '+n)
 auth('postauth');assert check()
 for row in state['records']:
  n=row['name'];assert sha(w/'logs'/(n+'.lean'))==row['source_sha256'] and sha(lib/'DiophantineConsistency'/(n+'.olean'))==row['object_sha256'] and sha(w/'logs'/(n+'.log'))==row['log_sha256'] and sha(w/'logs'/(n+'.time'))==row['time_sha256']
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
