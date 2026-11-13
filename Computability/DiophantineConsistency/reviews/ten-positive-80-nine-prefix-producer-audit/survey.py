#!/usr/bin/env python3
"""Plan the selected-closure rebuild cone downstream of observed drifts."""
from collections import defaultdict, deque
from hashlib import sha256
from pathlib import Path
import json

H=Path(__file__).resolve().parent;D=H.parents[1]
SCAN=D/'reviews/ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'
BASE=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'
DRIFT=H/'observations/attempt01.json';OUT=H/'observations/survey01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(not OUT.exists(),'output exists')
x=json.loads(SCAN.read_text()); b=json.loads(BASE.read_text()); d=json.loads(DRIFT.read_text())
need(x['status']=='PASS' and b['status']=='PASS' and d['status']=='COMPARED_WITH_DRIFTS','input status')
old=b['post_headers']['project']; graph={n:v['imports'] for n,v in old.items() if n in x['project']}
graph.update(x['fresh_headers']);reverse=defaultdict(set)
for n,deps in graph.items():
 for dep in deps:reverse[dep].add(n)
seeds={v['module'] for v in d['drifts']}; affected=set(seeds); todo=deque(seeds)
while todo:
 for client in reverse[todo.popleft()]:
  if client not in affected:affected.add(client);todo.append(client)
need('Direct80SymbolicFixedIPRA' in affected,'endpoint outside cone')
indegree={n:len(set(graph[n])&affected) for n in affected}; ready=deque(sorted(n for n,k in indegree.items() if k==0)); ordered=[]
while ready:
 n=ready.popleft();ordered.append(n)
 for client in sorted(reverse[n]&affected):
  indegree[client]-=1
  if indegree[client]==0:ready.append(client)
need(len(ordered)==len(affected),'cycle in selected headers')
by_basename=defaultdict(list)
for root in (D/'Lean',D/'research'):
 for p in root.rglob('*.lean'):
  if '/observations/' not in str(p):by_basename[p.name].append(str(p))
sources={n:sorted(by_basename.get(n.split('.')[-1]+'.lean',[])) for n in ordered}
result={'status':'PLAN_ONLY','input_sha256':{str(p):sha(p) for p in (SCAN,BASE,DRIFT)},
 'seeds':sorted(seeds),'ordered':ordered,'sources_by_basename':sources,
 'fresh_count':len(affected&set(x['fresh_headers'])),'prior_count':len(affected&set(old)),
 'scope':'reverse reachability in captured selected imports; candidate source basenames are not authenticated or compile order authorization'}
OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'affected':len(affected),'fresh':result['fresh_count'],'prior':result['prior_count'],
 'missing_source_basename':sum(not v for v in sources.values()),'multiple_source_basenames':sum(len(v)>1 for v in sources.values()),
 'result_sha256':sha(OUT)},sort_keys=True))
