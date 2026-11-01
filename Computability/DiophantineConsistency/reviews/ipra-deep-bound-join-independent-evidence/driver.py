"""Rebase the actual hbound object descendants onto the historical deep provider.

Read declared imports from every hbound peer olean; choose the deep provider's
five differing shared oleans; recompile all eleven hbound ancestors affected by
that choice from their authenticated historical source snapshots; compile join.
All other project/Foundation/package objects remain inherited historical input.
This is not a current-workspace source-closure or source/object-origin proof.
"""
from pathlib import Path
from collections import deque,defaultdict
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4];SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';HERE=Path(__file__).parent
A=Path('/tmp/ipra-zfc-deep-stability-klwc7iwi');B=Path('/tmp/ipra-induction-nozero-nra7kfs5');PKG=Path('/tmp/ha87-full-source-jrvxi6bb/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());assert read(A/'state.json')['status']==read(B/'state.json')['status']=='PASS'
expected=['IntuitionisticPRABridge','PRAWitnessZFCAxioms','IPRAConditionalComparison','PRAWitnessPositiveCoreZFC','PRAWitnessZFCNegativePiCore','IPRAAxiomPartition','PRAWitnessZFCRefutationBound','IPRAAxiomReduction','IPRAEqualityRemaining','IPRAFullGGTransfer','IPRAZFCRefutationBoundGG']
conflicts={'DiophantineConsistency/FoundationTheoryGG.olean','ZFCinPA/ReplacementDelta1.olean','ZFCinPA/SchemaClosure.olean','ZFCinPA/SeparationDelta1.olean','ZFCinPA/ZFDelta1.olean'}
def inventory(root):
 out={}
 for top in ('DiophantineConsistency','Foundation','ZFCinPA'):
  for base,dirs,files in os.walk(root/top,followlinks=True):
   for f in files:
    if '.olean' in f or f.endswith('.ir'):
     p=Path(base)/f;out[str(p.relative_to(root))]={'path':str(p.resolve()),'sha256':sha(p)}
 return out
ia,ib=inventory(A/'lib'),inventory(B/'lib');shared=set(ia)&set(ib);actual={n for n in shared if ia[n]['sha256']!=ib[n]['sha256']};assert actual==conflicts,(actual,conflicts)
selected={**ib,**ia};assert len(ia)==1669 and len(ib)==911 and len(shared)==571
imports_file=HERE/'bound-join-bound-peer-imports.tsv';reader=HERE/'read-olean-imports.lean';inputh={str(imports_file):sha(imports_file),str(reader):sha(reader),str(LEAN):sha(LEAN)}
rootprefix=str(B/'lib')+'/';graph={}
for line in imports_file.read_text().splitlines():
 path,imps=line.split('\t',1);assert path.startswith(rootprefix);n=path.removeprefix(rootprefix).removesuffix('.olean').replace('/','.');graph[n]=[x for x in imps.split(',') if x]
assert len(graph)==494
seeds={n.removesuffix('.olean').replace('/','.') for n in conflicts};rev=defaultdict(list)
for n,imports in graph.items():
 for x in imports:rev[x].append(n)
desc=set(seeds);q=deque(seeds)
while q:
 for n in rev[q.popleft()]:
  if n not in desc:desc.add(n);q.append(n)
target='DiophantineConsistency.IPRAZFCRefutationBoundGG';anc={target};q=deque([target]);missing=set()
while q:
 n=q.popleft()
 for x in graph.get(n,[]):
  if x.startswith(('DiophantineConsistency.','ZFCinPA.')) and x not in graph:missing.add(x)
  if x in graph and x not in anc:anc.add(x);q.append(x)
assert not missing;need=(anc&desc)-seeds;order=[]
while need:
 ready=sorted(n for n in need if not (set(graph[n])&need));assert ready
 order+=ready;need-=set(ready)
assert [n.split('.')[-1] for n in order]==expected,order
chain=[];p=B
while (p/'state.json').exists():
 st=read(p/'state.json');assert st['status']=='PASS';chain.append((p,st));parent=st.get('parent')
 if not isinstance(parent,str) or not parent or parent==str(p):break
 p=Path(parent)
parents={str(p):sha(p/'state.json') for p,_ in chain};parents[str(A)]=sha(A/'state.json');snapshots={}
for n in expected:
 found=[(p,row) for p,st in chain for row in st.get('records',[]) if row.get('module',row.get('name'))==n];assert found,n
 p,row=found[0];src=p/'src/DiophantineConsistency'/(n+'.lean');obj=B/'lib/DiophantineConsistency'/(n+'.olean');log=p/'logs'/(n+'.log')
 assert src.is_file() and sha(src)==row['source_sha256'] and sha(obj)==row['object_sha256'] and sha(log)==row['log_sha256'],n
 source_imports=set()
 for ln in src.read_text().splitlines():
  m=re.match(r'\s*(?:public\s+)?import\s+(.+)',ln)
  if m:source_imports.update(x for x in m.group(1).split() if re.fullmatch(r'[A-Za-z0-9_.]+',x))
 assert source_imports==set(graph['DiophantineConsistency.'+n]) - {'Init'},n
 snapshots[n]={'path':str(src),'sha256':sha(src),'owner':str(p),'object_sha256':row['object_sha256'],'log_sha256':row['log_sha256']}
joinnames=['IPRADeepBoundJoin','IPRADeepBoundJoinChecks'];joinh={n:sha(SRC/(n+'.lean')) for n in joinnames}
w=Path(tempfile.mkdtemp(prefix='ipra-deep-bound-join-'));lib=w/'lib';lib.mkdir();(w/'src/DiophantineConsistency').mkdir(parents=True);(w/'logs').mkdir();shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(reader,w/'read-olean-imports.lean');shutil.copyfile(imports_file,w/'bound-peer-imports.tsv')
for top in (A/'lib').iterdir():
 if top.name not in ('DiophantineConsistency','Foundation','ZFCinPA'):(lib/top.name).symlink_to(top.resolve(),target_is_directory=top.is_dir())
for rel,v in selected.items():
 out=lib/rel;out.parent.mkdir(parents=True,exist_ok=True);out.symlink_to(v['path'])
for n,v in snapshots.items():shutil.copyfile(v['path'],w/'src/DiophantineConsistency'/(n+'.lean'));shutil.copyfile(v['path'],w/'logs'/(n+'.lean'))
for n in joinnames:shutil.copyfile(SRC/(n+'.lean'),w/'src/DiophantineConsistency'/(n+'.lean'));shutil.copyfile(SRC/(n+'.lean'),w/'logs'/(n+'.lean'))
(w/'providers.json').write_text(json.dumps({'deep':ia,'bound':ib,'selected':selected,'conflicts':sorted(actual)},indent=2,sort_keys=True)+'\n');invh=sha(w/'providers.json')
state={'status':'RUNNING','private':str(w),'parents':parents,'input_hashes':inputh,'historical_source_snapshots':snapshots,'join_source_sha256':joinh,'inventory_sha256':invh,'selected_file_count':len(selected),'bound_object_graph_nodes':len(graph),'bound_endpoint_ancestors':len(anc),'rebuild':expected,'scope':'Historical source-directed rebase of all 11 declared-object descendants of five differing provider objects on deep-selected versions, then exact conditional ZFC bound join. Other project/Foundation/package objects remain inherited historical boundary; no full current-source, source/object-origin, equality decidability, or bounded-stability claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def auth():
 if sha(w/'providers.json')!=invh or not all(sha(p)==h for p,h in inputh.items()) or not all(sha(Path(p)/'state.json')==h for p,h in parents.items()):return False
 if not all(sha(v['path'])==v['sha256'] and sha(w/'src/DiophantineConsistency'/(n+'.lean'))==v['sha256'] and sha(w/'logs'/(n+'.lean'))==v['sha256'] for n,v in snapshots.items()):return False
 if not all(sha(SRC/(n+'.lean'))==h and sha(w/'src/DiophantineConsistency'/(n+'.lean'))==h and sha(w/'logs'/(n+'.lean'))==h for n,h in joinh.items()):return False
 if not all(sha(v['path'])==v['sha256'] for v in ia.values()) or not all(sha(v['path'])==v['sha256'] for v in ib.values()):return False
 rebuilt={r['name'] for r in state.get('records',[]) if r['exit']==0}
 for rel,v in selected.items():
  if rel.startswith('DiophantineConsistency/') and rel.endswith('.olean') and Path(rel).stem in rebuilt:continue
  if not (lib/rel).is_file() or sha(lib/rel)!=v['sha256']:return False
 return all(sha(lib/'DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256'] and sha(w/'logs'/(r['name']+'.log'))==r['log_sha256'] for r in state.get('records',[]) if r['exit']==0)
save();print('PRIVATE',w,flush=True)
try:
 assert auth();paths=sorted(str(B/'lib'/n) for n in ib if n.endswith('.olean'))
 result=subprocess.run([str(LEAN),'-j1','--run',str(reader),*paths],cwd=R,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 (w/'logs/declared-imports.tsv').write_text(result.stdout);(w/'logs/declared-imports.log').write_text(result.stderr)
 assert result.returncode==0 and result.stdout==imports_file.read_text(), 'serialized object import inventory mismatch'
 state['object_imports_sha256']=sha(w/'logs/declared-imports.tsv');save();env=dict(os.environ,LEAN_PATH=':'.join([str(lib),str(PKG)]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['records']=[]
 for n in [*expected,*joinnames]:
  out=lib/'DiophantineConsistency'/(n+'.olean')
  if out.is_symlink():out.unlink()
  assert not out.exists();cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10',str(LEAN),'--root='+str(w/'src'),'-M8000','-j1','-DElab.async=false','-o',str(out),str(w/'src/DiophantineConsistency'/(n+'.lean'))];start=time.monotonic()
  with (w/'logs'/(n+'.log')).open('w') as log:code=subprocess.run(['/usr/bin/time','-v','-o',str(w/'logs'/(n+'.time')),*cmd],cwd=R,env=env,stdout=log,stderr=subprocess.STDOUT).returncode
  state['records'].append(dict(name=n,exit=code,source_sha256=sha(w/'src/DiophantineConsistency'/(n+'.lean')),object_sha256=sha(out) if out.exists() else None,log_sha256=sha(w/'logs'/(n+'.log')),seconds=time.monotonic()-start));save();print(n,code,flush=True);assert code==0
 assert auth();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=repr(e));save();raise
