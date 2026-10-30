"""Rebuild the private Assembly and direct reduced-zero construction branch."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=Path(os.environ.get('CELL_COMPAT_BUILD','/tmp/adaptive13-cell-compat-guarded-mfrskqz1'));X=Path('/tmp/adaptive-reduced-provider-audit-cl3b5itk');B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';A=R/'Computability/DiophantineConsistency/research/wang-chunk-full/reauth_cell_compat.py';T=R/'Computability/DiophantineConsistency/research/wang-chunk-full/audit_reduced_provider.py';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());xs=read(X/'state.json');bs=read(B/'state.json');ds=read(D/'state.json');xr=read(X/'result.json');assert xs['status']==ds['status']==bs['status']=='PASS' and sha(X/'result.json')==xs['result_sha256'];dh=sha(D/'state.json');xh=sha(X/'state.json');ah=sha(A);th=sha(T)
names=['ArithmeticRunTrace','ArithmeticTilingTable','ArithmeticTilingRows','ArithmeticTilingBand','ArithmeticTilingWord','ArithmeticPackingCells','ArithmeticConstructionAssembly','ArithmeticAdaptiveConstructionRunDraft2011'];snapshots={n:sha(S/(n+'.lean')) for n in names}
w=Path(tempfile.mkdtemp(prefix='adaptive-assembly-compat-'));shutil.copyfile(__file__,w/'driver.py');(w/'logs').mkdir()
for n in names:shutil.copyfile(S/(n+'.lean'),w/'logs'/(n+'.lean'))
state={'status':'RUNNING','private':str(w),'cell_provider':str(D),'cell_state_sha256':dh,'reduced_audit':str(X),'reduced_audit_state_sha256':xh,'reduced_audit_result_sha256':xs['result_sha256'],'snapshots':snapshots,'records':[],'scope':'Private current-source Assembly and direct 87-gate construction from run and local-normalization premises, using reauthenticated CellWindow and reduced providers; no HA proof or canonical integration.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True)
def reauth(label):
 for which,script,env in [('cell',A,dict(os.environ,CELL_COMPAT_BUILD=str(D))),('reduced',T,dict(os.environ))]:
  p=subprocess.run(['python3',str(script)],cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(w/(label+'-'+which+'.log')).write_text(p.stdout);assert p.returncode==0,p.stdout
  lines=[x for x in p.stdout.splitlines() if x.startswith('PASS ')];assert len(lines)==1;z=Path(lines[0].split()[1]);zs=read(z/'state.json');assert zs['status']=='PASS'
  if which=='reduced':assert zs['result_sha256']==xs['result_sha256']
  shutil.copyfile(z/'state.json',w/(label+'-'+which+'.json'));state[label+'-'+which]={'audit_path':str(z),'state_sha256':sha(w/(label+'-'+which+'.json')),'log_sha256':sha(w/(label+'-'+which+'.log'))};save();print('AUTH',label,which,z,flush=True)
try:
 reauth('preauth');assert sha(D/'state.json')==dh and sha(X/'state.json')==xh and all(sha(S/(n+'.lean'))==snapshots[n] for n in names) and sha(A)==ah and sha(T)==th
 lib=w/'lib'
 for f in (D/'lib').rglob('*'):
  if f.is_file():
   rel=f.relative_to(D/'lib')
   if rel.parent==Path('DiophantineConsistency') and any(rel.name.startswith(n+'.') for n in names):continue
   dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve())
 for rel,src in xr['extras'].items():
  dst=lib/rel;assert not dst.exists();dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src)
 env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in names:
  src=S/(n+'.lean');assert sha(src)==snapshots[n];o=lib/'DiophantineConsistency'/(n+'.olean');assert not o.exists();log=w/'logs'/(n+'.log');tim=w/'logs'/(n+'.time');cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(o),str(src)];print('START',n,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  rec={'name':n,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim),'command':cmd}
  if o.exists():rec['object_sha256']=sha(o)
  state['records'].append(rec);save();print('DONE',n,code,round(rec['seconds'],2),flush=True)
  if code:raise RuntimeError('Lean build failed: '+n)
 reauth('postauth');assert sha(D/'state.json')==dh and sha(X/'state.json')==xh and sha(X/'result.json')==xs['result_sha256'] and all(sha(S/(n+'.lean'))==snapshots[n] for n in names) and sha(A)==ah and sha(T)==th;state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
