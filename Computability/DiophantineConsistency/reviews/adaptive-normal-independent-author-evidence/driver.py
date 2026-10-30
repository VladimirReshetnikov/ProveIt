"""Source-rebuild WangTable-independent prerequisites of local normalization."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=Path(os.environ.get('CELL_COMPAT_BUILD','/tmp/adaptive13-cell-compat-complete-y4d89y9u'));B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');A=R/'Computability/DiophantineConsistency/research/wang-chunk-full/reauth_cell_compat.py';SRC={'DiophantineConsistency':R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency','FirstOrder':R/'Logic/FirstOrder/Lean/FirstOrder','PAHF':R/'Logic/Interpretability/PAHF/Lean/PAHF','BusyBeaver':R/'Computability/BusyBeaver/Lean/BusyBeaver'};sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());ds=read(D/'state.json');bs=read(B/'state.json');assert ds['status']==bs['status']=='PASS';dh=sha(D/'state.json');ah=sha(A);graph={}
def visit(k):
 if k in graph:return
 ns,_,n=k.partition('.');f=SRC.get(ns,Path('/missing'))/(n.replace('.','/')+'.lean');graph[k]=[]
 if f.is_file():
  graph[k]=[i for line in f.read_text().splitlines() if line.startswith('import ') for i in line[7:].split()]
  for x in graph[k]:visit(x)
target='DiophantineConsistency.ArithmeticLocalNormalization';visit(target);memo={}
def affected(k):
 if k in memo:return memo[k]
 if k=='DiophantineConsistency.ArithmeticWangTable':return True
 memo[k]=False;memo[k]=any(affected(x) for x in graph[k]);return memo[k]
seen=set();names=[];affected_missing=[]
def topo(k):
 if k in seen:return
 seen.add(k)
 for x in graph[k]:topo(x)
 ns,_,n=k.partition('.')
 if ns in SRC and (SRC[ns]/(n.replace('.','/')+'.lean')).is_file() and not (D/'lib'/ns/(n.replace('.','/')+'.olean')).is_file():
  (affected_missing if affected(k) else names).append(k)
topo(target);assert len(names)==40 and affected_missing[-3:]==['DiophantineConsistency.ArithmeticLocalNormalizationDigits','DiophantineConsistency.ArithmeticLocalNormalizationWorld','DiophantineConsistency.ArithmeticLocalNormalization'] and all(k.startswith('DiophantineConsistency.') for k in names)
snapshots={k:sha(SRC[k.partition('.')[0]]/(k.partition('.')[2]+'.lean')) for k in names};w=Path(tempfile.mkdtemp(prefix='adaptive-normal-independent-'));(w/'logs').mkdir();shutil.copyfile(__file__,w/'driver.py')
for k in names:
 ns,_,n=k.partition('.');shutil.copyfile(SRC[ns]/(n+'.lean'),w/'logs'/(n+'.lean'))
state={'status':'RUNNING','private':str(w),'cell_provider':str(D),'cell_state_sha256':dh,'names':names,'affected_missing':affected_missing,'source_graph_count':len(graph),'snapshots':snapshots,'records':[],'scope':'Private current-source rebuild of 40 WangTable-independent local-normalization prerequisites; compatibility-dependent Assembly predecessors and three normalization modules remain unbuilt; no LocalNormalization, equivalence or HA endpoint claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True)
def auth(label):
 q=subprocess.run(['python3',str(A)],cwd=R,env=dict(os.environ,CELL_COMPAT_BUILD=str(D)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(w/(label+'.log')).write_text(q.stdout);assert q.returncode==0,q.stdout;lines=[x for x in q.stdout.splitlines() if x.startswith('PASS ')];assert len(lines)==1;z=Path(lines[0].split()[1]);assert read(z/'state.json')['status']=='PASS';shutil.copyfile(z/'state.json',w/(label+'.json'));state[label]={'audit_path':str(z),'state_sha256':sha(w/(label+'.json')),'log_sha256':sha(w/(label+'.log'))};save();print('AUTH',label,z,flush=True)
try:
 auth('preauth');assert sha(D/'state.json')==dh and sha(A)==ah and all(sha(SRC[k.partition('.')[0]]/(k.partition('.')[2]+'.lean'))==snapshots[k] for k in names);lib=w/'lib'
 for f in (D/'lib').rglob('*'):
  if f.is_file():
   rel=f.relative_to(D/'lib');dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve())
 env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for k in names:
  ns,_,n=k.partition('.');src=SRC[ns]/(n+'.lean');assert sha(src)==snapshots[k];out=lib/ns/(n+'.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists();log=w/'logs'/(n+'.log');tim=w/'logs'/(n+'.time');cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',k,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'name':n,'namespace':ns,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim),'command':cmd}
  if out.exists():row['object_sha256']=sha(out)
  state['records'].append(row);save();print('DONE',k,code,round(row['seconds'],2),flush=True)
  if code:raise RuntimeError(k)
 auth('postauth');assert sha(D/'state.json')==dh and sha(A)==ah
 for row in state['records']:
  ns,n=row['namespace'],row['name'];assert sha(SRC[ns]/(n+'.lean'))==sha(w/'logs'/(n+'.lean'))==row['source_sha256'] and sha(lib/ns/(n+'.olean'))==row['object_sha256'] and sha(w/'logs'/(n+'.log'))==row['log_sha256'] and sha(w/'logs'/(n+'.time'))==row['time_sha256']
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
