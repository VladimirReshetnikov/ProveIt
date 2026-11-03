#!/usr/bin/env python3
"""Read-only reconstruction of captured 91 proof project-import closures."""
from collections import deque
from hashlib import sha256
import json
from pathlib import Path
import subprocess,sys
H=Path(__file__).resolve().parent;D=H.parents[1];O=H/'observations/attempt01'
INV=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/observations/attempt01/result.json'
PRE=D/'research/ordinary12-sum-squares-endpoint-import-preflight/observations/attempt02/result.json'
A1=D/'reviews/ordinary12-qcube92-serialized-import-independent/observations/attempt01/result.json'
A2=D/'reviews/ordinary12-qcube92-module-collision-independent/observations/attempt01/result.json'
X=D/'research/ordinary12-xq91-candidate';Q=D/'research/ordinary12-qcube92-candidate'
R={'XQ91':X/'observations/algebra-attempt01/terminal.json','XQ91Model':X/'observations/model-attempt01/terminal.json','QCube92Halt':Q/'observations/halt2-attempt01/terminal.json'}
FIX={O/'result.json':'87f7fad28524346b6921bda2f180f763417e98a0209063a7fae7fb579aea3787',
 O/'stdout':'78ec7ee364b856bfa5c7b9a2fa24292248420fdcb3064716bce05b61ee2089a0',
 O/'stderr':'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
 H/'scan.py':'e800804e33ea4a5057363030b58148894b3f54d623b42b68189591217694f103'}
def need(x,m):
 if not x:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,v in FIX.items():need(sha(p)==v,'evidence hash mismatch '+str(p))
r=json.loads((O/'result.json').read_text());inv=json.loads(INV.read_text());pre=json.loads(PRE.read_text());a1=json.loads(A1.read_text());a2=json.loads(A2.read_text());rec={k:json.loads(v.read_text()) for k,v in R.items()};base=rec['QCube92Halt']
for p,v in r['pins'].items():need(sha(p)==v,'scan input drift '+p)
need(r['exit']==0 and not (O/'stderr').read_bytes(),'header reader failed')
need(r['preflight']['mem_available_kib']>=8*1024**2 and len(r['preflight']['lean'])<2,'resource guard mismatch')
need(not r['preflight']['lean'] and not r['postflight']['lean'],'observed Lean overlap')
by_path={x['path']:n for n,x in r['objects'].items()};parsed={};current=None
for line in (O/'stdout').read_text().splitlines():
 if line.startswith('BEGIN '):
  need(current is None and line[6:] in by_path,'unexpected header BEGIN');current=by_path[line[6:]];need(current not in parsed,'duplicate header');parsed[current]=[]
 elif line.startswith('IMPORT ') and current is not None:parsed[current].append(line[7:])
 elif line=='END' and current is not None:current=None
 else:raise SystemExit('unexpected header output')
need(current is None and parsed==r['headers'] and set(parsed)==set(r['objects']),'header record mismatch')
for name,obj in r['objects'].items():
 p=Path(obj['path']);need(p.is_file() and str(p.resolve())==obj['realpath'] and sha(p)==obj['sha256'],'captured object drift '+name)
need(parsed['XQ91']==['Init','Init','QCube92'] and parsed['XQ91Model']==['Init','Init','XQ91'],'91 direct imports differ')
need(parsed['QCube92Halt']==['Init','Init','QCube92NamespacedExistence','CompactSymbolicModelUnconditionalIff','CompactBytePortsModelIff'],'92 halt direct imports differ')
align='DiophantineConsistency.FreeJRadixAlignment';need(parsed[align]==inv['imports'][align],'alignment captured header mismatch')
graph={n:list(v) for n,v in inv['imports'].items()};graph.update(pre['added_imports'])
for name in ('QCube92','QCube92Model','FreeJRootBinding','QCube92Existence'):graph[name]=a1['headers'][name]
graph.update(a2['headers']);graph.update(parsed)
extra={'XQ91':r['objects']['XQ91'],'XQ91Model':r['objects']['XQ91Model'],'QCube92Halt':r['objects']['QCube92Halt']}
def walk(starts):
 todo=deque(starts);seen=set();outside=set()
 while todo:
  n=todo.popleft()
  if n in seen or n in outside:continue
  if n not in graph:outside.add(n);continue
  seen.add(n);todo.extend(graph[n])
 return seen,outside
summary={}
for root,row in r['roots'].items():
 seen,outside=walk([root]);need(seen==set(row['project_ancestors']) and outside==set(row['outside_graph']),'closure mismatch '+root)
 need(set(row['selected'])==seen-{root},'selected set mismatch '+root)
 roots=rec[root]['lean_path'].split(':')[:-1] if root in rec else base['lean_path'].split(':')[:-1]
 for name,item in row['selected'].items():
  rel=name.replace('.','/')+'.olean';choices=[Path(x)/rel for x in roots if (Path(x)/rel).is_file()]
  need(choices and str(choices[0])==item['path'] and str(choices[0].resolve())==item['realpath'] and sha(choices[0])==item['sha256'],'first selected path mismatch '+name)
  if name in extra:expected=extra[name]['sha256']
  else:
   need(rel in base['union'],'module absent from base '+name);expected=base['union'][rel]['sha256']
   if name in a1['objects']:need(expected==a1['objects'][name]['sha256'],'92 proof header mismatch '+name)
   elif name=='QCube92NamespacedExistence':need(expected==a2['object']['sha256'],'namespaced existence header mismatch')
   else:
    prev=inv['objects'].get(name,pre['added_objects'].get(name));need(prev is not None and prev['sha256']==expected,'prior header object mismatch '+name)
  need(item['sha256']==expected,'selected object differs '+name)
 summary[root]={'project':len(seen),'outside':len(outside)}
planned=['XQ91Model','QCube92Halt',align];seen,outside=walk(planned)
need(r['planned_imports']==planned and seen==set(r['planned_project_ancestors']) and outside==set(r['planned_outside_graph']),'planned closure mismatch')
need(not ({'FreeJRootBinding','QCube92Existence','FreeJRadixAlignment','FreeJSignedTransport'}&seen),'duplicate top-level module reachable')
need('DiophantineConsistency.FreeJRootBinding' in seen and 'DiophantineConsistency.FreeJRadixAlignment' in seen,'required namespaced module missing')
need('FreeJOrdinaryTailWitness' not in r['roots']['XQ91']['project_ancestors'] and 'FreeJOrdinaryTailWitness' not in r['roots']['XQ91Model']['project_ancestors'],'91 proof reaches differing tail')
need('FreeJOrdinaryTailWitness' in seen and base['union']['FreeJOrdinaryTailWitness.olean']['sha256']=='3af9bb5c54c1fda2d7ea0daf22e43c4fe02176b5eda32a345b45ded73024304e','expected 92-base tail absent')
for script in (D/'reviews/ordinary12-qcube92-halt-independent/check.py',D/'reviews/ordinary12-xq91-model-independent/check.py'):
 c=subprocess.run([sys.executable,'-I','-S','-B',str(script)],capture_output=True,check=True);need(not c.stderr,'prior review stderr')
for p,v in r['pins'].items():need(sha(p)==v,'scan input changed during review '+p)
for p,v in FIX.items():need(sha(p)==v,'scan evidence changed during review '+str(p))
print(json.dumps({'roots':summary,'planned_project':len(seen),'planned_outside':len(outside),
 '91_project_ancestry_excludes_old_tail':True,'planned_retains_92_tail':True,
 'excluded_duplicate_top_level_modules':True,'prior_model_reviews':'PASS'},indent=2))
