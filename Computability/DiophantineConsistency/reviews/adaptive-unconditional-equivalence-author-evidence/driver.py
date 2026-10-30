"""Discharge local normalization in the private 87-gate model equivalence."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');P=Path(os.environ.get('NORMAL_COMPAT_BUILD','/tmp/adaptive-normal-compat-li4on2mu'));E=Path(os.environ.get('EQUIV_PROVIDER','/tmp/adaptive-equivalence-client-55isyt4n'));B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';A=R/'Computability/DiophantineConsistency/research/wang-chunk-full/reauth_normalization_compat.py';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());ps=read(P/'state.json');es=read(E/'state.json');bs=read(B/'state.json');H=Path(es['reduced_halt_provider']);hs=read(H/'state.json');N=Path(hs['halt_provider']);ns=read(N/'state.json');assert ps['status']==es['status']==hs['status']==ns['status']==bs['status']=='PASS';assert ps['assembly_state_sha256']==es['assembly_state_sha256'];ph=sha(P/'state.json');eh=sha(E/'state.json');ah=sha(A);src=S/'ArithmeticAdaptiveEquivalenceUnconditional2011.lean';sh=sha(src)
inputs=[('ArithmeticAdaptiveHalt2011',N,ns),('ArithmeticAdaptiveHaltReduced2011',H,hs),('ArithmeticAdaptiveEquivalence2011',E,es)]
def check():
 return (sha(P/'state.json')==ph and sha(E/'state.json')==eh and sha(A)==ah and sha(src)==sh and sha(H/'state.json')==es['reduced_halt_state_sha256'] and sha(N/'state.json')==hs['halt_state_sha256'] and all(sha(S/(n+'.lean'))==st['source_sha256'] and sha(p/'lib/DiophantineConsistency'/(n+'.olean'))==st['object_sha256'] for n,p,st in inputs))
assert check();w=Path(tempfile.mkdtemp(prefix='adaptive-unconditional-equivalence-'));shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(src,w/'source-snapshot.lean');state={'status':'RUNNING','private':str(w),'normalization_provider':str(P),'normalization_state_sha256':ph,'equivalence_provider':str(E),'equivalence_state_sha256':eh,'source_sha256':sh,'scope':'Unconditional all-model 87-gate no-zero iff no represented-machine halt, discharging finite local normalization; no HA proof existence or canonical integration claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True)
def auth(label):
 q=subprocess.run(['python3',str(A)],cwd=R,env=dict(os.environ,NORMAL_COMPAT_BUILD=str(P)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(w/(label+'.log')).write_text(q.stdout);assert q.returncode==0,q.stdout;lines=[x for x in q.stdout.splitlines() if x.startswith('PASS ')];assert len(lines)==1;z=Path(lines[0].split()[1]);assert read(z/'state.json')['status']=='PASS';shutil.copyfile(z/'state.json',w/(label+'.json'));state[label]={'audit_path':str(z),'state_sha256':sha(w/(label+'.json')),'log_sha256':sha(w/(label+'.log'))};save();print('AUTH',label,z,flush=True)
try:
 auth('preauth');assert check();lib=w/'lib'
 for f in (P/'lib').rglob('*'):
  if f.is_file():
   rel=f.relative_to(P/'lib')
   if rel.parent==Path('DiophantineConsistency') and rel.name.startswith('ArithmeticAdaptiveEquivalenceUnconditional2011.'):continue
   dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve())
 for n,p,st in inputs:
  dst=lib/'DiophantineConsistency'/(n+'.olean')
  if dst.exists():assert sha(dst)==st['object_sha256']
  else:dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to((p/'lib/DiophantineConsistency'/(n+'.olean')).resolve())
 o=lib/'DiophantineConsistency/ArithmeticAdaptiveEquivalenceUnconditional2011.olean';log=w/'build.log';tim=w/'build.time';env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(o),str(src)];state['command']=cmd;save();print('START',flush=True);start=time.monotonic()
 with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 state.update(exit=code,seconds=time.monotonic()-start,log_sha256=sha(log),time_sha256=sha(tim));
 if o.exists():state['object_sha256']=sha(o)
 save();print('DONE',code,flush=True)
 if code:raise RuntimeError('Lean build failed')
 auth('postauth');assert check() and sha(o)==state['object_sha256'] and sha(log)==state['log_sha256'];state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
