from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');A=Path('/tmp/adaptive13-assembly-composed-source-audit.json');roots={'DiophantineConsistency':R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency','BusyBeaver':R/'Computability/BusyBeaver/Lean/BusyBeaver'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
allnames=[('BusyBeaver','Core'),('BusyBeaver','ZFC/KZip'),('BusyBeaver','ZFC/KDenseBridge'),('BusyBeaver','ZFC/KTableCore'),('BusyBeaver','ZFC/KTable215'),('BusyBeaver','ZFC/KDense215'),('DiophantineConsistency','DecimalMachine215')];names=allnames[:5]
bs=read(B/'state.json');assert bs['status']=='PASS';audit=read(A);assert audit['base']==str(B) and not audit['bad'] and not audit['missing'];expected={r['module']:r for r in audit['rows']};old={}
for ns,n in allnames:
 key=ns+'.'+n.replace('/','.');r=expected[key];src=roots[ns]/(n+'.lean');obj=B/'lib'/ns/(n+'.olean');assert r['provenance'].startswith('62ff') and sha(src)==r['source_sha256'] and sha(obj)==r['object_sha256'];old[key]=r['object_sha256']
guards=read(B/'guards.json');assert sha(B/'guards.json')==bs['guards_sha256'];assert all(sha(p)==h for p,h in guards.items());assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive13-cache-boundary-light-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(A,w/'audit.json');providers=[];excluded={Path(ns)/(n+'.olean') for ns,n in allnames}
for f in (B/'lib').rglob('*'):
 if f.is_file():
  rel=f.relative_to(B/'lib')
  if any(rel==x or str(rel).startswith(str(x)+'.') for x in excluded):continue
  dest=lib/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve());providers.append({'path':str(f),'sha256':sha(f),'bytes':f.stat().st_size})
(w/'providers.json').write_text(json.dumps(providers,indent=2)+'\n')
for ns,n in allnames:
 dst=logs/ns/(n+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(roots[ns]/(n+'.lean'),dst)
state={'status':'RUNNING','private':str(w),'snapshots':{ns+'.'+n.replace('/','.'):sha(logs/ns/(n+'.lean')) for ns,n in allnames},'records':[],'previous_objects':old,'providers_sha256':sha(w/'providers.json'),'base_state_sha256':sha(B/'state.json'),'base_guards_sha256':sha(B/'guards.json'),'audit_sha256':sha(w/'audit.json'),'boundary':bs['boundary'],'scope':'five lower-cost cache-boundary source rebuilds, sequential low-priority; two kernel-heavy modules excluded, all descendants remain inherited and unrefreshed'}
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
 for ns,n in allnames:assert sha(roots[ns]/(n+'.lean'))==state['snapshots'][ns+'.'+n.replace('/','.')]
 for p,h in guards.items():assert sha(p)==h
 assert sha(B/'state.json')==state['base_state_sha256'] and sha(B/'guards.json')==state['base_guards_sha256']
 state['status']='PASS_FIVE';save();print('PASS_FIVE',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
