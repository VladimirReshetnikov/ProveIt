"""Private conditional model equivalence client from audited forward/reverse inputs."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');P=Path(os.environ.get('ASSEMBLY_COMPAT_BUILD','/tmp/adaptive-assembly-compat-7ths2hw9'));H=Path(os.environ.get('REDUCED_HALT_PROVIDER','/tmp/adaptive-reduced-halt-client-pvtfnljn'));B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticAdaptiveEquivalence2011.lean';RS=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticAdaptiveHaltReduced2011.lean';NS=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticAdaptiveHalt2011.lean';A=R/'Computability/DiophantineConsistency/research/wang-chunk-full/reauth_assembly_compat.py';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());ps=read(P/'state.json');hs=read(H/'state.json');bs=read(B/'state.json');N=Path(hs['halt_provider']);ns=read(N/'state.json');assert ps['status']==hs['status']==ns['status']==bs['status']=='PASS';assert sha(H/'lib/DiophantineConsistency/ArithmeticAdaptiveHaltReduced2011.olean')==hs['object_sha256'] and sha(RS)==hs['source_sha256'] and sha(N/'lib/DiophantineConsistency/ArithmeticAdaptiveHalt2011.olean')==ns['object_sha256'] and sha(NS)==ns['source_sha256'] and sha(N/'state.json')==hs['halt_state_sha256'];ph=sha(P/'state.json');hh=sha(H/'state.json');sh=sha(S);ah=sha(A)
w=Path(tempfile.mkdtemp(prefix='adaptive-equivalence-client-'));shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(S,w/'source-snapshot.lean');state={'status':'RUNNING','private':str(w),'assembly_provider':str(P),'assembly_state_sha256':ph,'reduced_halt_provider':str(H),'reduced_halt_state_sha256':hh,'source_sha256':sh,'scope':'Conditional all-model equivalence under LocalNormalization between no 87-gate zero and no represented halting time; no HA proof existence or canonical integration claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True)
def auth(label):
 q=subprocess.run(['python3',str(A)],cwd=R,env=dict(os.environ,ASSEMBLY_COMPAT_BUILD=str(P)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(w/(label+'.log')).write_text(q.stdout);assert q.returncode==0,q.stdout;lines=[x for x in q.stdout.splitlines() if x.startswith('PASS ')];assert len(lines)==1;z=Path(lines[0].split()[1]);assert read(z/'state.json')['status']=='PASS';shutil.copyfile(z/'state.json',w/(label+'.json'));state[label]={'audit_path':str(z),'state_sha256':sha(w/(label+'.json')),'log_sha256':sha(w/(label+'.log'))};save();print('AUTH',label,z,flush=True)
def check():
 return (sha(P/'state.json')==ph and sha(H/'state.json')==hh and sha(S)==sh and sha(A)==ah and sha(RS)==hs['source_sha256'] and sha(NS)==ns['source_sha256'] and sha(H/'lib/DiophantineConsistency/ArithmeticAdaptiveHaltReduced2011.olean')==hs['object_sha256'] and sha(N/'state.json')==hs['halt_state_sha256'] and sha(N/'lib/DiophantineConsistency/ArithmeticAdaptiveHalt2011.olean')==ns['object_sha256'])
try:
 auth('preauth');assert check();lib=w/'lib'
 for f in (P/'lib').rglob('*'):
  if f.is_file():
   rel=f.relative_to(P/'lib')
   if rel.parent==Path('DiophantineConsistency') and rel.name.startswith('ArithmeticAdaptiveEquivalence2011.'):continue
   dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve())
 for n,p in [('ArithmeticAdaptiveHalt2011',N),('ArithmeticAdaptiveHaltReduced2011',H)]:
  dst=lib/'DiophantineConsistency'/(n+'.olean');assert not dst.exists();dst.symlink_to((p/'lib/DiophantineConsistency'/(n+'.olean')).resolve())
 o=lib/'DiophantineConsistency/ArithmeticAdaptiveEquivalence2011.olean';log=w/'build.log';tim=w/'build.time';env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(o),str(S)];state['command']=cmd;save();print('START',flush=True);start=time.monotonic()
 with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 state.update(exit=code,seconds=time.monotonic()-start,log_sha256=sha(log),time_sha256=sha(tim));
 if o.exists():state['object_sha256']=sha(o)
 save();print('DONE',code,flush=True)
 if code:raise RuntimeError('Lean build failed')
 auth('postauth');assert check() and sha(o)==state['object_sha256'] and sha(log)==state['log_sha256'];state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
