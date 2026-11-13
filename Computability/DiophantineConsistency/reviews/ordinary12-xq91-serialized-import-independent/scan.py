#!/usr/bin/env python3
"""Bounded serialized-import scan for 91 proof and namespaced alignment."""
from collections import deque
from hashlib import sha256
import json
from pathlib import Path
import subprocess,sys,time
if sys.flags.optimize:raise SystemExit('optimized Python refused')
HERE=Path(__file__).resolve().parent;D=HERE.parents[1]
X=D/'research/ordinary12-xq91-candidate';Q=D/'research/ordinary12-qcube92-candidate'
INV=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/observations/attempt01/result.json'
PRE=D/'research/ordinary12-sum-squares-endpoint-import-preflight/observations/attempt02/result.json'
A1=D/'reviews/ordinary12-qcube92-serialized-import-independent/observations/attempt01/result.json'
A2=D/'reviews/ordinary12-qcube92-module-collision-independent/observations/attempt01/result.json'
HELPER=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');O=HERE/'observations/attempt01'
R={'XQ91':X/'observations/algebra-attempt01/terminal.json','XQ91Model':X/'observations/model-attempt01/terminal.json',
   'QCube92Halt':Q/'observations/halt2-attempt01/terminal.json'}
FIX={INV:'bf812db57d68117d47d3df792e4a0d6879019d442c4f0f2b0fbef8b861f363f2',
 PRE:'b15febdf3f77edc4ecdabddb3da2d9bf8735549d28869c4ec18d0669096a45ce',
 A1:'af847f4a3903770fd50bf7b7f09d597f748fa83ab0c3f4c0b7ae79dff192a615',
 A2:'d3f68298e20708297524c0e0e540091e184d451972fdb801ab9081c227779934',
 HELPER:'886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f',
 R['XQ91']:'647ab4935265c9db60a9f6b4975f3eb48bc14426b2d102fc10c969730232db6a',
 R['XQ91Model']:'bdc4d6cb11c87d0161b0d777f2be050ef6bbf7ca11d6a5ce1b88a345d21ce36b',
 R['QCube92Halt']:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(x,m):
 if not x:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def sample():
 ps=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout;rows=[]
 for line in ps.splitlines():
  f=line.strip().split(None,3)
  if len(f)==4 and f[1]=='lean':rows.append({'pid':int(f[0]),'rss_kib':int(f[2]),'args':f[3]})
 m=next(s for s in Path('/proc/meminfo').read_text().splitlines() if s.startswith('MemAvailable:'))
 return {'time_ns':time.time_ns(),'mem_available_kib':int(m.split()[1]),'lean':rows}
def info(p):
 p=Path(p);return {'path':str(p),'realpath':str(p.resolve(strict=True)),'sha256':sha(p)}
need(not O.exists(),'refusing to overwrite scan')
for p,h in FIX.items():need(sha(p)==h,'fixed hash mismatch '+str(p))
rec={k:json.loads(v.read_text()) for k,v in R.items()};base=rec['QCube92Halt'];inv=json.loads(INV.read_text());pre=json.loads(PRE.read_text());a1=json.loads(A1.read_text());a2=json.loads(A2.read_text())
need(base['exit']==0 and not base['reason'] and base['base_unchanged'] and base['extra_unchanged'] and base['union_unchanged'] and base['union_count']==1291,'invalid 92 halt base')
files={}
for name,r in rec.items():
 need(r['exit']==0 and not r['reason'],'producer failed '+name)
 if name!='QCube92Halt':need(r['selected_provider_unchanged'] and r['before']==r['after'],'producer guard failed '+name)
 p=Path(r['output_root'])/(name+'.olean');need(p.is_file() and sha(p)==r['object_sha256'],'producer object drift '+name);files[name]=p
align='DiophantineConsistency.FreeJRadixAlignment';rel=align.replace('.','/')+'.olean'
need(rel in base['union'],'namespaced alignment absent from halt union');files[align]=Path(base['union'][rel]['resolved'])
need(sha(files[align])==base['union'][rel]['sha256']=='ebc83df3fa0343d2e20f265927c715e9bf813b79cb5338c72540ec3f6dfe84e4','alignment object drift')
for unwanted in ('FreeJRootBinding.olean','QCube92Existence.olean','FreeJRadixAlignment.olean'):
 need(unwanted not in base['union'],'duplicate top-level module in 92 halt base '+unwanted)
pins={str(p):sha(p) for p in list(FIX)+[LEAN,HERE/'scan.py']+list(files.values())}
initial=sample();need(initial['mem_available_kib']>=8*1024**2 and len(initial['lean'])<2,'resource guard refused')
O.mkdir(parents=True);cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER),*[str(p) for p in files.values()]]
t0=time.monotonic();run=subprocess.run(cmd,capture_output=True,text=True,timeout=60);elapsed=time.monotonic()-t0;post=sample()
(O/'stdout').write_text(run.stdout);(O/'stderr').write_text(run.stderr);need(run.returncode==0 and not run.stderr,'header reader failed')
paths={str(p):n for n,p in files.items()};headers={};current=None
for line in run.stdout.splitlines():
 if line.startswith('BEGIN '):
  need(current is None and line[6:] in paths,'unexpected BEGIN');current=paths[line[6:]];need(current not in headers,'duplicate header');headers[current]=[]
 elif line.startswith('IMPORT ') and current is not None:headers[current].append(line[7:])
 elif line=='END' and current is not None:current=None
 else:raise RuntimeError('bad header output')
need(current is None and set(headers)==set(files),'missing header')
need(headers['XQ91']==['Init','Init','QCube92'] and headers['XQ91Model']==['Init','Init','XQ91'],'unexpected 91 direct imports')
graph={n:list(v) for n,v in inv['imports'].items()};graph.update(pre['added_imports'])
for name in ('QCube92','QCube92Model','FreeJRootBinding','QCube92Existence'):graph[name]=a1['headers'][name]
graph.update(a2['headers']);need(headers[align]==graph[align],'alignment header differs from prior inventory');graph.update(headers)
extra={'XQ91':files['XQ91'],'XQ91Model':files['XQ91Model'],'QCube92Halt':files['QCube92Halt']}
def walk(starts):
 todo=deque(starts);seen=set();outside=set()
 while todo:
  n=todo.popleft()
  if n in seen or n in outside:continue
  if n not in graph:outside.add(n);continue
  seen.add(n);todo.extend(graph[n])
 return seen,outside
roots=['XQ91','XQ91Model',align,'QCube92Halt'];results={}
for root in roots:
 seen,outside=walk([root]);need(not ({'FreeJRootBinding','QCube92Existence','FreeJRadixAlignment'}&seen),'duplicate top-level project module '+root)
 roots_paths=rec[root]['lean_path'].split(':')[:-1] if root in rec else base['lean_path'].split(':')[:-1]
 selected={}
 for name in sorted(seen):
  if name==root:continue
  rel=name.replace('.','/')+'.olean'
  if name in extra:expected=sha(extra[name])
  else:
   need(rel in base['union'],'module absent from 92 halt union '+name);expected=base['union'][rel]['sha256']
   if name in a1['objects']:need(expected==a1['objects'][name]['sha256'],'92 extra header hash mismatch '+name)
   elif name=='QCube92NamespacedExistence':need(expected==a2['object']['sha256'],'92 namespaced header hash mismatch')
   else:
    previous=inv['objects'].get(name,pre['added_objects'].get(name));need(previous is not None and previous['sha256']==expected,'prior header object mismatch '+name)
  candidates=[Path(r)/rel for r in roots_paths if (Path(r)/rel).is_file()];need(candidates,'unresolved selected project module '+name)
  need(sha(candidates[0])==expected,'first-selected module hash mismatch '+name);selected[name]=info(candidates[0])
 results[root]={'project_ancestors':sorted(seen),'outside_graph':sorted(outside),'selected':selected}
# The source draft requests these imports. This is a predicted selected-project
# closure only, not a compiled client or a captured client object header.
planned=['XQ91Model','QCube92Halt',align];seen,outside=walk(planned)
need(not ({'FreeJRootBinding','QCube92Existence','FreeJRadixAlignment'}&seen),'duplicate top-level project module in planned closure')
need(align in seen,'namespaced alignment missing')
for path,h in pins.items():need(sha(path)==h,'scan input changed '+path)
for result in results.values():
 for item in result['selected'].values():need(info(item['path'])==item,'selected object changed during scan')
result={'pins':pins,'command':cmd,'exit':run.returncode,'elapsed':elapsed,'preflight':initial,'postflight':post,
 'objects':{k:info(v) for k,v in files.items()},'headers':headers,'roots':results,
 'planned_imports':planned,'planned_project_ancestors':sorted(seen),'planned_outside_graph':sorted(outside),
 'scope':'selected serialized-project headers and predicted client closure; inherited package/dynamic/source-object ancestry'}
(O/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'exit':run.returncode,'roots':{k:{'project':len(v['project_ancestors']),'outside':len(v['outside_graph'])} for k,v in results.items()},
 'planned_project':len(seen),'planned_outside':len(outside),'elapsed':elapsed},indent=2))
