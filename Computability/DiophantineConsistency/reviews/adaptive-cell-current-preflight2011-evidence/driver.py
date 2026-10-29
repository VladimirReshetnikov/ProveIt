from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs'); P=Path('/tmp/adaptive13-cell-root-parent-wnvsel13');B=Path(os.environ['ADAPTIVE_CELL_BASE']);OLD=Path('/tmp/adaptive13-window-client-gl1jcjjp/lib')
S={'DiophantineConsistency':R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency','FirstOrder':R/'Logic/FirstOrder/Lean/FirstOrder','PAHF':R/'Logic/Interpretability/PAHF/Lean/PAHF','BusyBeaver':R/'Computability/BusyBeaver/Lean/BusyBeaver'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
s=json.loads((P/'state.json').read_text());assert s['status']=='FAILED';records=s['records'];assert len(records)==37 and records[-1]['name']=='ArithmeticWangTable' and records[-1]['exit']==137
assert sha(P/'providers.json')==s['providers_sha256'];provider=json.loads((P/'providers.json').read_text())
for f,h in provider.items():assert sha(f)==h, f
order=[tuple(x.split('.',1)) for x in s['order']];assert len(order)==46
prefix=records[:-1];assert len(prefix)==36
for i,row in enumerate(prefix):
 ns,n=order[i];assert (ns,n)==(row['namespace'],row['name']) and row['exit']==0
 src=S[ns]/(n+'.lean');snap=P/'logs'/ns/(n+'.lean');obj=P/'lib'/ns/(n+'.olean');log=P/'logs'/ns/(n+'.log');tim=P/'logs'/ns/(n+'.time')
 assert sha(src)==sha(snap)==row['source_sha256'];assert sha(obj)==row['object_sha256'];assert sha(log)==row['log_sha256'];assert sha(tim)==row['time_sha256']
for ns,n in order:
 snap=P/'logs'/ns/(n+'.lean');assert sha(snap)==s['snapshots'][ns+'.'+n];assert sha(S[ns]/(n+'.lean'))==sha(snap)
bs=json.loads((B/'state.json').read_text());assert bs['status']=='PASS'
for row in bs['records']:
 assert sha(S['DiophantineConsistency']/(row['name']+'.lean'))==row['source_sha256']
 assert sha(B/'lib/DiophantineConsistency'/(row['name']+'.olean'))==row['object_sha256']
forbidden={'DiophantineConsistency.ArithmeticCarrierRadix2011','DiophantineConsistency.ArithmeticBinomLegendre','DiophantineConsistency.ArithmeticHalfBinomial','DiophantineConsistency.ArithmeticHalfBinomialSandwich','DiophantineConsistency.ArithmeticAdaptivePopulation2011'};seen=set()
def visit(key):
 if key in seen:return
 assert key not in forbidden,key
 seen.add(key)
 if '.' not in key:return
 ns,n=key.split('.',1)
 if ns not in S:return
 f=S[ns]/(n.replace('.','/')+'.lean')
 if not f.exists():return
 for line in f.read_text().splitlines():
  if line.startswith('import '):
   for child in line[7:].split():visit(child)
for row in prefix:visit(row['namespace']+'.'+row['name'])
changed=[]
for f,h in provider.items():
 q=Path(f)
 if not q.is_relative_to(OLD):continue
 rel=q.relative_to(OLD);cur=B/'lib'/rel;assert cur.is_file(),str(cur)
 if sha(cur)!=h:changed.append(str(rel))
allowed={'DiophantineConsistency/ArithmeticCarrierRadix2011.olean','DiophantineConsistency/ArithmeticBinomLegendre.olean','DiophantineConsistency/ArithmeticHalfBinomial.olean','DiophantineConsistency/ArithmeticHalfBinomialSandwich.olean','DiophantineConsistency/ArithmeticAdaptivePopulation2011.olean'}
assert set(changed)<=allowed,changed
remaining=order[len(prefix):];assert remaining[0]==('DiophantineConsistency','ArithmeticWangTable')
if os.environ.get('ADAPTIVE_CELL_PREFLIGHT')=='1':
 print('PREFLIGHT PASS', 'base', B, 'prefix', len(prefix), 'remaining', len(remaining), 'reachable', len(seen), 'differences', changed, flush=True)
 raise SystemExit(0)
assert shutil.disk_usage('/tmp').free>=512*1024**2
w=Path(tempfile.mkdtemp(prefix='adaptive13-cell-current-resume-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();shutil.copyfile(__file__,w/'driver.py');selected={}
for f in (B/'lib').rglob('*'):
 if not f.is_file():continue
 rel=f.relative_to(B/'lib')
 if any(rel==Path(ns)/(n+'.olean') or str(rel).startswith(str(Path(ns)/(n+'.olean'))+'.') for ns,n in remaining):continue
 dest=lib/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve());selected[str(f)]=sha(f)
for row in prefix:
 ns,n=row['namespace'],row['name'];src=P/'lib'/ns/(n+'.olean');dst=lib/ns/(n+'.olean')
 dst.parent.mkdir(parents=True,exist_ok=True);assert not dst.exists(),str(dst);dst.symlink_to(src.resolve());selected[str(src)]=sha(src)
for ns,n in remaining:
 dst=logs/ns/(n+'.lean');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(P/'logs'/ns/(n+'.lean'),dst)
(w/'providers.json').write_text(json.dumps(selected,indent=2)+'\n')
p=json.loads(Path('/tmp/arithmetic-signed-pairs-peer-f4gz2l0f/inputs.json').read_text());boundary=p['LEAN_PATH'][1:];assert all('/.lake/packages/' in x or '/toolchains/' in x for x in boundary)
state={'status':'RUNNING','private':str(w),'resume_from':str(P),'current_base':str(B),'current_base_state_sha256':sha(B/'state.json'),'old_provider_differences':changed,'prefix_reachable_module_count':len(seen),'parent_state_sha256':sha(P/'state.json'),'parent_provider_sha256':sha(P/'providers.json'),'completed_prefix_count':len(prefix),'completed_prefix':prefix,'failed_attempt':records[-1], 'remaining':[ns+'.'+n for ns,n in remaining],'snapshots':{ns+'.'+n:sha(logs/ns/(n+'.lean')) for ns,n in remaining},'providers_sha256':sha(w/'providers.json'),'records':[]}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,'PREFIX_REUSED',len(prefix),'STARTING',state['remaining'][0],flush=True)
env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*boundary]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
try:
 for ns,n in remaining:
  key=ns+'.'+n;src=S[ns]/(n+'.lean');assert sha(src)==state['snapshots'][key];assert shutil.disk_usage('/tmp').free>=512*1024**2
  out=lib/ns/(n+'.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists();log=logs/ns/(n+'.log');tim=logs/ns/(n+'.time');cmd=['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',key,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'name':n,'namespace':ns,'command':cmd,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim)}
  if out.exists():row['object_sha256']=sha(out)
  state['records'].append(row);save();print('DONE',key,code,round(row['seconds'],2),flush=True);print(log.read_text(),flush=True)
  if code:raise RuntimeError(key)
  assert sha(src)==state['snapshots'][key]
 for f,h in selected.items():assert sha(f)==h
 for f,h in provider.items():assert sha(f)==h
 assert sha(P/'state.json')==state['parent_state_sha256'];assert sha(B/'state.json')==state['current_base_state_sha256']
 for row in bs['records']:assert sha(S['DiophantineConsistency']/(row['name']+'.lean'))==row['source_sha256']
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
