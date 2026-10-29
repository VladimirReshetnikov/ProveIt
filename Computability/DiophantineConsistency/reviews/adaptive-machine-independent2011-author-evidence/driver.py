from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=Path(os.environ['ADAPTIVE_ASSEMBLY_BASE']);D=Path('/tmp/adaptive13-cell-root-parent-wnvsel13');roots={'DiophantineConsistency':R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency','BusyBeaver':R/'Computability/BusyBeaver/Lean/BusyBeaver','FirstOrder':R/'Logic/FirstOrder/Lean/FirstOrder','PAHF':R/'Logic/Interpretability/PAHF/Lean/PAHF'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
names=[('BusyBeaver','ZFC/ArithmeticMachineStepPerm252'),('DiophantineConsistency','ArithmeticMachineStep215'),('DiophantineConsistency','ArithmeticMachineRun215')]
bs=read(B/'state.json');assert bs['status']=='PASS';assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive13-machine-independent-'));logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py');shutil.copyfile('/tmp/adaptive13-cell-current-resume-driver.py',w/'cell-preflight.py');shutil.copyfile('/tmp/adaptive13-machine-independent-audit.py',w/'audit.py');print('PRIVATE',w,flush=True)
env=dict(os.environ,ADAPTIVE_CELL_BASE=str(B),ADAPTIVE_CELL_PREFLIGHT='1');print('PREFLIGHT',flush=True)
with (w/'preflight.log').open('w') as f:code=subprocess.run(['python3',str(w/'cell-preflight.py')],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
assert code==0,(w/'preflight.log').read_text();env=dict(os.environ,ADAPTIVE_ASSEMBLY_BASE=str(B),ADAPTIVE_PREFIX_AUDIT_OUT=str(w/'audit.json'));print('AUDIT',flush=True)
with (w/'audit.log').open('w') as f:code=subprocess.run(['python3',str(w/'audit.py')],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
assert code==0,(w/'audit.log').read_text();a=read(w/'audit.json');assert a['base_state_sha256']==sha(B/'state.json') and a['prefix_state_sha256']==sha(D/'state.json') and not a['missing'] and not a['bad']
lib=w/'lib';lib.mkdir();providers=[];excluded={Path(ns)/(n+'.olean') for ns,n in names}
for f in (B/'lib').rglob('*'):
 if f.is_file():
  rel=f.relative_to(B/'lib')
  if any(rel==x or str(rel).startswith(str(x)+'.') for x in excluded):continue
  dest=lib/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve());providers.append({'path':str(f),'sha256':sha(f),'bytes':f.stat().st_size,'origin':'base'})
for row in a['rows']:
 if row['provenance']!='authenticated 36-module prefix':continue
 rel=Path(row['module'].replace('.','/')+'.olean');dest=lib/rel
 if dest.is_file():assert sha(dest)==row['object_sha256'];continue
 src=Path(row['object']);assert sha(src)==row['object_sha256'];dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(src.resolve());providers.append({'path':str(src),'sha256':sha(src),'bytes':src.stat().st_size,'origin':'verified prefix'})
(w/'providers.json').write_text(json.dumps(providers,indent=2)+'\n')
for ns,n in names:
 dst=logs/ns/(n+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(roots[ns]/(n+'.lean'),dst)
state={'status':'RUNNING','private':str(w),'snapshots':{ns+'.'+n:sha(logs/ns/(n+'.lean')) for ns,n in names},'records':[],'providers_sha256':sha(w/'providers.json'),'base_state_sha256':sha(B/'state.json'),'prefix_state_sha256':sha(D/'state.json'),'audit_sha256':sha(w/'audit.json'),'preflight_sha256':sha(w/'preflight.log'),'boundary':bs['boundary'],'scope':'three Wang-independent machine-step/run prerequisites over current provider and individually authenticated prefix objects; project sources audited, 62ff cache and Foundation/package internals inherited boundaries'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
try:
 for ns,n in names:
  key=ns+'.'+n;src=roots[ns]/(n+'.lean');assert sha(src)==state['snapshots'][key];assert shutil.disk_usage('/tmp').free>=512*1024**2
  out=lib/ns/(n+'.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists();log=logs/ns/(n+'.log');tim=logs/ns/(n+'.time');cmd=['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',key,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'namespace':ns,'name':n,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim)}
  if out.exists():row['object_sha256']=sha(out)
  state['records'].append(row);save();print('DONE',key,code,round(row['seconds'],2),flush=True);print(log.read_text(),flush=True)
  if code:raise RuntimeError(key)
 for x in providers:assert sha(x['path'])==x['sha256']
 for ns,n in names:assert sha(roots[ns]/(n+'.lean'))==state['snapshots'][ns+'.'+n]
 for row in a['rows']:
  ns,n=row['module'].split('.',1);assert sha(roots[ns]/(n.replace('.','/')+'.lean'))==row['source_sha256'];assert sha(row['object'])==row['object_sha256']
 assert sha(B/'state.json')==state['base_state_sha256'] and sha(D/'state.json')==state['prefix_state_sha256']
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
