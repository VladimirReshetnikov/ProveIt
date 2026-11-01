"""Source-snapshot adaptive equation rebase on the checked native ZFC provider.

No merged overlays: the single parent is provisional until its independent peer
passes. The complete project/package ancestry of that parent remains inherited.
Workspace drift after the frozen snapshot is reported, not called current-source.
"""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4]
SRC=R/'Computability/DiophantineConsistency/Lean'
P=Path('/tmp/ipra-bounded-rho-scoped-2rglb_b4')
PKG=Path('/tmp/ha87-full-source-jrvxi6bb/package-lib')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
parent=json.loads((P/'state.json').read_text());assert parent['status']=='PASS'
parent_hash=sha(P/'state.json');parent_inventory_hash=sha(P/'providers.json');assert parent_inventory_hash==parent['provider_inventory_sha256']
lean_hash=sha(LEAN)
# Pin both literal source identities to independently checked earlier providers;
# the 87 literal object itself is an inherited selected boundary.
L=Path('/tmp/ha87-focused-validator-rebase-q6geuvc7');E86=Path('/tmp/ipra86-translated-join-g2gvcd25');E87=Path('/tmp/ipra86-translated-join-cnrha8ck');C=Path('/tmp/pra86-classical-join-w5g_sfd4')
source_checks={}
for provider,name in [(L,'AdaptiveFirstRootFactor87Literal'),(C,'AdaptiveDirectOrdinate86Literal'),(E86,'IPRA86TranslatedRefutation'),(E87,'IPRA87TranslatedRefutation')]:
 st=json.loads((provider/'state.json').read_text());assert st['status']=='PASS'
 row=next(x for x in st['records'] if x.get('module')=='DiophantineConsistency.'+name)
 path=SRC/'DiophantineConsistency'/(name+'.lean');assert sha(path)==row['source_sha256'],name
 source_checks[name]={'source_sha256':row['source_sha256'],'provider_state_sha256':sha(provider/'state.json'),'provider':str(provider)}
litrow=next(x for x in json.loads((L/'state.json').read_text())['records'] if x.get('module')=='DiophantineConsistency.AdaptiveFirstRootFactor87Literal')
assert sha(P/'lib/DiophantineConsistency/AdaptiveFirstRootFactor87Literal.olean')==litrow['object_sha256']
w=Path(tempfile.mkdtemp(prefix='ipra-adaptive-native-zfc-'));lib=w/'lib';lib.mkdir();(w/'src').mkdir();(w/'logs').mkdir();shutil.copyfile(__file__,w/'driver.py')
# Snapshot reachable workspace project sources down to the inherited-object boundary.
roots=['DiophantineConsistency.IPRAAdaptiveNativeZFCChecks']
graph={};source_hash={}; todo=roots[:]
while todo:
 n=todo.pop()
 if n in graph:continue
 rel=Path(n.replace('.','/')+'.lean');path=SRC/rel
 # Existing selected objects are explicit inherited boundaries, not current source rebuilds.
 if n not in roots and (P/'lib'/Path(n.replace('.','/')+'.olean')).exists():
  graph[n]=[];continue
 if not path.is_file():continue
 data=path.read_bytes(); source_hash[n]=hashlib.sha256(data).hexdigest()
 snap=w/'src'/rel;snap.parent.mkdir(parents=True,exist_ok=True);snap.write_bytes(data)
 text=data.decode();imports=[m.group(1) for line in text.splitlines() if (m:=re.match(r'\s*(?:public\s+)?import\s+([\w.]+)',line))]
 graph[n]=imports;todo.extend(imports)
assert all(sha(SRC/Path(n.replace('.','/')+'.lean'))==h for n,h in source_hash.items())
# Only build nodes absent in the single parent; inherited present nodes are not
# claimed current. The 11 affected bound descendants were built in the parent.
built=[];done=set();active=set()
def visit(n):
 if n in done or n not in graph:return
 if n in active:raise RuntimeError('cycle '+n)
 active.add(n)
 for dep in graph[n]:visit(dep)
 active.remove(n);done.add(n)
 if not (P/'lib'/Path(n.replace('.','/')+'.olean')).exists():built.append(n)
for n in roots:visit(n)
assert len(built)==33, (len(built),built)
assert built[-2:]==['DiophantineConsistency.IPRAAdaptiveNativeZFC','DiophantineConsistency.IPRAAdaptiveNativeZFCChecks']
(w/'graph.json').write_text(json.dumps({'roots':roots,'source_sha256':source_hash,'imports':graph,'build_order':built},indent=2,sort_keys=True)+'\n');graph_hash=sha(w/'graph.json')
selected={}
for base,dirs,files in os.walk(P/'lib',followlinks=True):
 for f in files:
  if '.olean' in f or f.endswith('.ir'):
   p=Path(base)/f;rel=str(p.relative_to(P/'lib'));selected[rel]={'path':str(p.resolve()),'sha256':sha(p)}
for rel,v in selected.items():
 out=lib/rel;out.parent.mkdir(parents=True,exist_ok=True);out.symlink_to(v['path'])
(w/'providers.json').write_text(json.dumps(selected,indent=2,sort_keys=True)+'\n');inventory_hash=sha(w/'providers.json')
state={'status':'RUNNING','private':str(w),'parent':str(P),'parent_state_sha256':parent_hash,'parent_inventory_sha256':parent_inventory_hash,'parent_is_provisional':False,'lean_sha256':lean_hash,'literal_source_checks':source_checks,'inherited_87_literal_object_sha256':litrow['object_sha256'],'graph_sha256':graph_hash,'project_source_count':len(graph),'provider_inventory_sha256':inventory_hash,'provider_objects':len(selected),'build_order':built,'scope':'Fixed-workspace-source snapshot 86/87 equation source rebuild over the independently replayed scoped literal ZFC provider. Actual equation literal source identities are separately checked; other project/Foundation/package ancestry is inherited historical, and complete current-source closure and standard-iPRA identification are not asserted.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def auth():
 if not all(sha(Path(v['provider'])/'state.json')==v['provider_state_sha256'] for v in source_checks.values()):return False
 if sha(LEAN)!=lean_hash or sha(P/'state.json')!=parent_hash or sha(P/'providers.json')!=parent_inventory_hash or sha(w/'providers.json')!=inventory_hash or sha(w/'graph.json')!=graph_hash:return False
 if not all(sha(w/'src'/Path(n.replace('.','/')+'.lean'))==h for n,h in source_hash.items()):return False
 if not all(sha(v['path'])==v['sha256'] and sha(lib/k)==v['sha256'] for k,v in selected.items()):return False
 return all(sha(lib/Path(x['name'].replace('.','/')+'.olean'))==x['object_sha256'] and sha(w/'logs'/(x['name']+'.log'))==x['log_sha256'] for x in state.get('records',[]) if x['exit']==0)
save();print('PRIVATE',w,'BUILD',len(built),flush=True)
try:
 assert auth();env=dict(os.environ,LEAN_PATH=f'{lib}:{PKG}',LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['records']=[]
 for n in built:
  rel=Path(n.replace('.','/'));src=w/'src'/rel.with_suffix('.lean');out=lib/rel.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists()
  log=w/'logs'/(n+'.log');cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10',str(LEAN),'--root='+str(w/'src'),'-M8000','-j1','-DElab.async=false','-o',str(out),str(src)];start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(w/'logs'/(n+'.time')),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  state['records'].append({'name':n,'exit':code,'source_sha256':sha(src),'object_sha256':sha(out) if out.exists() else None,'log_sha256':sha(log),'seconds':time.monotonic()-start});save();print(n,code,flush=True);assert code==0
 assert auth()
 state['literal_workspace_drift']=[n for n,v in source_checks.items() if not (SRC/'DiophantineConsistency'/(n+'.lean')).is_file() or sha(SRC/'DiophantineConsistency'/(n+'.lean'))!=v['source_sha256']]
 state['workspace_drift']=[n for n,h in source_hash.items() if not (SRC/Path(n.replace('.','/')+'.lean')).is_file() or sha(SRC/Path(n.replace('.','/')+'.lean'))!=h]
 state['status']='PASS';save();print('PASS',w,'DRIFT',len(state['workspace_drift']),flush=True)
except BaseException as e:state.update(status='FAILED',failure=repr(e));save();raise
