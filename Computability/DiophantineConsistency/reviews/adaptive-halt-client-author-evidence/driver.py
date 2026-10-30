"""Build the actual adaptive-zero halting client in an authenticated private overlay."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=Path(os.environ.get('CELL_COMPAT_BUILD','/tmp/adaptive13-cell-compat-guarded-mfrskqz1'));B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticAdaptiveHalt2011.lean';A=R/'Computability/DiophantineConsistency/research/wang-chunk-full/reauth_cell_compat.py';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());ds=read(D/'state.json');bs=read(B/'state.json');assert ds['status']==bs['status']=='PASS';dh=sha(D/'state.json');sh=sha(S);ah=sha(A)
w=Path(tempfile.mkdtemp(prefix='adaptive-halt-client-'));shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(S,w/'source-snapshot.lean');state={'status':'RUNNING','private':str(w),'cell_provider':str(D),'cell_state_sha256':dh,'source_sha256':sh,'reauth_driver_sha256':ah,'scope':'Actual 13-variable natural-expression zero implies bounded represented-machine halting in every IΣ₁ model; no 87-gate transfer, HA proof existence, or canonical integration claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True)
def reauth(label):
 env=dict(os.environ,CELL_COMPAT_BUILD=str(D));p=subprocess.run(['python3',str(A)],cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(w/(label+'.log')).write_text(p.stdout);assert p.returncode==0, p.stdout
 lines=[x for x in p.stdout.splitlines() if x.startswith('PASS ')];assert len(lines)==1;z=Path(lines[0][5:]);assert read(z/'state.json')['status']=='PASS';shutil.copyfile(z/'state.json',w/(label+'.json'));state[label]={'audit_path':str(z),'state_sha256':sha(w/(label+'.json')),'log_sha256':sha(w/(label+'.log'))};save();print('AUTH',label,z,flush=True)
try:
 reauth('preauth');assert sha(D/'state.json')==dh and sha(S)==sh and sha(A)==ah
 lib=w/'lib'
 for f in (D/'lib').rglob('*'):
  if f.is_file():
   rel=f.relative_to(D/'lib')
   if rel.parent==Path('DiophantineConsistency') and rel.name.startswith('ArithmeticAdaptiveHalt2011.'):continue
   dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve())
 o=lib/'DiophantineConsistency/ArithmeticAdaptiveHalt2011.olean';log=w/'build.log';tim=w/'build.time';env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(o),str(S)];state['command']=cmd;save();print('START',flush=True);start=time.monotonic()
 with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 state.update(exit=code,seconds=time.monotonic()-start,log_sha256=sha(log),time_sha256=sha(tim));
 if o.exists():state['object_sha256']=sha(o)
 save();print('DONE',code,flush=True)
 if code:raise RuntimeError('Lean build failed')
 reauth('postauth');assert sha(D/'state.json')==dh and sha(S)==sh and sha(A)==ah;state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
