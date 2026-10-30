"""Build the 87-gate zero-to-halt client on authenticated private providers."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');H=Path(os.environ.get('HALT_PROVIDER','/tmp/adaptive-halt-client-9uszegm7'));X=Path('/tmp/adaptive-reduced-provider-audit-cl3b5itk');B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticAdaptiveHaltReduced2011.lean';N=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticAdaptiveHalt2011.lean';A=R/'Computability/DiophantineConsistency/research/wang-chunk-full/reauth_cell_compat.py';T=R/'Computability/DiophantineConsistency/research/wang-chunk-full/audit_reduced_provider.py';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());hs=read(H/'state.json');xs=read(X/'state.json');bs=read(B/'state.json');D=Path(hs['cell_provider']);ds=read(D/'state.json');xr=read(X/'result.json');assert hs['status']==xs['status']==ds['status']==bs['status']=='PASS' and sha(X/'result.json')==xs['result_sha256'];assert sha(N)==hs['source_sha256'] and sha(H/'lib/DiophantineConsistency/ArithmeticAdaptiveHalt2011.olean')==hs['object_sha256'] and sha(D/'state.json')==hs['cell_state_sha256'];hh=sha(H/'state.json');xh=sha(X/'state.json');sh=sha(S);ah=sha(A);th=sha(T)
w=Path(tempfile.mkdtemp(prefix='adaptive-reduced-halt-client-'));shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(S,w/'source-snapshot.lean');state={'status':'RUNNING','private':str(w),'halt_provider':str(H),'halt_state_sha256':hh,'reduced_audit':str(X),'reduced_audit_state_sha256':xh,'reduced_audit_result_sha256':xs['result_sha256'],'source_sha256':sh,'scope':'Actual 87-gate natural-expression zero implies bounded represented-machine halt in every IΣ₁ model; no HA proof existence, unconditional converse, or canonical integration claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True)
def reauth(label):
 for which,script,env in [('cell',A,dict(os.environ,CELL_COMPAT_BUILD=str(D))),('reduced',T,dict(os.environ))]:
  p=subprocess.run(['python3',str(script)],cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(w/(label+'-'+which+'.log')).write_text(p.stdout);assert p.returncode==0,p.stdout
  lines=[x for x in p.stdout.splitlines() if x.startswith('PASS ')];assert len(lines)==1;z=Path(lines[0].split()[1]);zs=read(z/'state.json');assert zs['status']=='PASS'
  if which=='reduced':assert zs['result_sha256']==xs['result_sha256']
  shutil.copyfile(z/'state.json',w/(label+'-'+which+'.json'));state[label+'-'+which]={'audit_path':str(z),'state_sha256':sha(w/(label+'-'+which+'.json')),'log_sha256':sha(w/(label+'-'+which+'.log'))};save();print('AUTH',label,which,z,flush=True)
try:
 reauth('preauth');assert sha(H/'state.json')==hh and sha(X/'state.json')==xh and sha(S)==sh and sha(N)==hs['source_sha256'] and sha(A)==ah and sha(T)==th
 lib=w/'lib'
 for f in (D/'lib').rglob('*'):
  if f.is_file():
   rel=f.relative_to(D/'lib')
   if rel.parent==Path('DiophantineConsistency') and rel.name.startswith('ArithmeticAdaptiveHaltReduced2011.'):continue
   dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve())
 for rel,src in xr['extras'].items():
  dst=lib/rel;assert not dst.exists();dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src)
 dst=lib/'DiophantineConsistency/ArithmeticAdaptiveHalt2011.olean';assert not dst.exists();dst.symlink_to((H/'lib/DiophantineConsistency/ArithmeticAdaptiveHalt2011.olean').resolve())
 o=lib/'DiophantineConsistency/ArithmeticAdaptiveHaltReduced2011.olean';log=w/'build.log';tim=w/'build.time';env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(o),str(S)];state['command']=cmd;save();print('START',flush=True);start=time.monotonic()
 with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 state.update(exit=code,seconds=time.monotonic()-start,log_sha256=sha(log),time_sha256=sha(tim));
 if o.exists():state['object_sha256']=sha(o)
 save();print('DONE',code,flush=True)
 if code:raise RuntimeError('Lean build failed')
 reauth('postauth');assert sha(H/'state.json')==hh and sha(X/'state.json')==xh and sha(X/'result.json')==xs['result_sha256'] and sha(S)==sh and sha(N)==hs['source_sha256'] and sha(A)==ah and sha(T)==th;state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
