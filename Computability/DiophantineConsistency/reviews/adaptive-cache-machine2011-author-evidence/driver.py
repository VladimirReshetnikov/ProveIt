from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=Path('/tmp/adaptive13-cache-boundary-decimal-78wm7s_8');C=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');A=Path('/tmp/adaptive13-cache-machine-audit.json');roots={'DiophantineConsistency':R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency','BusyBeaver':R/'Computability/BusyBeaver/Lean/BusyBeaver'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
names=[('BusyBeaver','ZFC/FiniteZipper'),('BusyBeaver','ZFC/TablePerm252'),('BusyBeaver','ZFC/ArithmeticMachinePerm252'),('BusyBeaver','ZFC/ArithmeticMachineGraphPerm252'),('DiophantineConsistency','ArithmeticMachineGraph215'),('BusyBeaver','ZFC/ArithmeticMachineStepPerm252'),('DiophantineConsistency','ArithmeticMachineStep215'),('DiophantineConsistency','ArithmeticMachineRun215')]
bs=read(B/'state.json');cs=read(C/'state.json');a=read(A);assert bs['status']==cs['status']=='PASS' and bs['matches_previous'];assert a['canonical_state_sha256']==sha(C/'state.json') and a['pilot_state_sha256']==sha(B/'state.json');guards=read(C/'guards.json');assert sha(C/'guards.json')==cs['guards_sha256'] and all(sha(p)==h for p,h in guards.items())
for r in a['rows']:assert sha(r['source'])==r['source_sha256'] and sha(r['object'])==r['object_sha256']
assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive13-cache-machine-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(A,w/'audit.json');shutil.copyfile('/tmp/adaptive13-cache-machine-audit.py',w/'audit.py');providers=[];excluded={Path(ns)/(n+'.olean') for ns,n in names}
for f in (B/'lib').rglob('*'):
 if f.is_file():
  rel=f.relative_to(B/'lib')
  if any(rel==x or str(rel).startswith(str(x)+'.') for x in excluded):continue
  dest=lib/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve());providers.append({'path':str(f),'sha256':sha(f),'bytes':f.stat().st_size})
(w/'providers.json').write_text(json.dumps(providers,indent=2)+'\n');old={}
for ns,n in names:
 src=roots[ns]/(n+'.lean');dst=logs/ns/(n+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);old[ns+'.'+n.replace('/','.')]=sha(C/'lib'/ns/(n+'.olean'))
state={'status':'RUNNING','private':str(w),'snapshots':{ns+'.'+n.replace('/','.'):sha(logs/ns/(n+'.lean')) for ns,n in names},'records':[],'previous_objects':old,'providers_sha256':sha(w/'providers.json'),'canonical_state_sha256':sha(C/'state.json'),'canonical_guards_sha256':sha(C/'guards.json'),'pilot_state_sha256':sha(B/'state.json'),'audit_sha256':sha(w/'audit.json'),'boundary':bs['boundary'],'scope':'eight machine-path modules rebuilt over seven independently source-rebuilt cache modules; source closure audited, Foundation/toolchain/package internals inherited boundaries; not yet substituted into accepted composition'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True);env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
try:
 for ns,n in names:
  key=ns+'.'+n.replace('/','.');src=roots[ns]/(n+'.lean');assert sha(src)==state['snapshots'][key];assert shutil.disk_usage('/tmp').free>=512*1024**2
  out=lib/ns/(n+'.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists();log=logs/ns/(n+'.log');tim=logs/ns/(n+'.time');cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M3000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',key,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'namespace':ns,'name':n,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim),'previous_object_sha256':old[key]}
  if out.exists():row.update(object_sha256=sha(out),matches_previous=sha(out)==old[key])
  state['records'].append(row);save();print('DONE',key,code,round(row['seconds'],2),'matches previous',row.get('matches_previous'),flush=True);print(log.read_text(),flush=True)
  if code:raise RuntimeError(key)
 for x in providers:assert sha(x['path'])==x['sha256']
 for ns,n in names:assert sha(roots[ns]/(n+'.lean'))==state['snapshots'][ns+'.'+n.replace('/','.')]
 for r in a['rows']:assert sha(r['source'])==r['source_sha256'] and sha(r['object'])==r['object_sha256']
 for p,h in guards.items():assert sha(p)==h
 assert sha(B/'state.json')==state['pilot_state_sha256'] and sha(C/'state.json')==state['canonical_state_sha256'] and sha(C/'guards.json')==state['canonical_guards_sha256']
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
