from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';B=Path(os.environ.get('ADAPTIVE_ASSEMBLY_BASE','/tmp/adaptive13-assembly-recomposed-q9s50zdl'));C=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');names=['ArithmeticAdaptiveConstructionFactorLemmas2011','ArithmeticAdaptiveConstructionFactorLemmas2011Checks']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
bs=read(B/'state.json');cs=read(C/'state.json');assert bs['status']==cs['status']=='PASS';guards=read(C/'guards.json');assert sha(C/'guards.json')==cs['guards_sha256'] and all(sha(p)==h for p,h in guards.items())
for r in bs['records']:assert sha(r['source'])==r['source_sha256'] and sha(B/'lib'/r['namespace']/(r['name']+'.olean'))==r['object_sha256']
assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive-construction-factor-lemmas-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py');providers=[]
for f in (B/'lib').rglob('*'):
 if f.is_file():
  rel=f.relative_to(B/'lib')
  if rel.parent==Path('DiophantineConsistency') and rel.name.split('.')[0] in names:continue
  dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve());providers.append({'path':str(f),'sha256':sha(f),'bytes':f.stat().st_size})
(w/'providers.json').write_text(json.dumps(providers,indent=2)+'\n')
for n in names:shutil.copyfile(S/(n+'.lean'),logs/(n+'.lean'))
state={'status':'RUNNING','private':str(w),'snapshots':{n:sha(logs/(n+'.lean')) for n in names},'records':[],'providers_sha256':sha(w/'providers.json'),'base_state_sha256':sha(B/'state.json'),'canonical_state_sha256':sha(C/'state.json'),'canonical_guards_sha256':sha(C/'guards.json'),'boundary':bs['boundary'],'scope':'model-uniform main-correction quotient from explicit Pell seed identities; no positivity or actual assembly claim'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True);env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
try:
 for n in names:
  src=S/(n+'.lean');assert sha(src)==state['snapshots'][n];out=lib/'DiophantineConsistency'/(n+'.olean');assert not out.exists();log=logs/(n+'.log');tim=logs/(n+'.time');cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',n,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  r={'name':n,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim)}
  if out.exists():r['object_sha256']=sha(out)
  state['records'].append(r);save();print('DONE',n,code,round(r['seconds'],2),flush=True);print(log.read_text(),flush=True)
  if code:raise RuntimeError(n)
 for x in providers:assert sha(x['path'])==x['sha256']
 for n in names:assert sha(S/(n+'.lean'))==state['snapshots'][n]
 for p,h in guards.items():assert sha(p)==h
 assert sha(B/'state.json')==state['base_state_sha256'] and sha(C/'state.json')==state['canonical_state_sha256'];state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
