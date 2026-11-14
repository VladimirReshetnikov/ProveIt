"""Full Boolean zero/nonzero relation, preserving interregister correlation."""
import sys,json,gzip,time,collections
from pathlib import Path
from paths import INPUTS,OUT
import source_language as L
sites=json.loads((INPUTS/'sites.json').read_text());graph=L.graph_intervals(sites)
seed=(1,0,13,0,0,1,0,0,1);mask=sum(1<<j for j,x in enumerate(seed)if x)

def images(i,p):
 effect,targets=graph[i];kind=effect[0];arg=effect[1]if len(effect)>1 else None
 if kind=='increment':return[(targets[0],p|(1<<arg))]
 if kind=='decrement':
  if p>>arg&1:return[(targets[1],p),(targets[1],p&~(1<<arg))]
  return[(targets[0],p)]
 return[(q,p)for q in targets]
def facts(ps):return[3 if any(p>>j&1 for p in ps)and any(not(p>>j&1)for p in ps)else 2 if any(p>>j&1 for p in ps)else 1 for j in range(9)]if ps else None
started=time.monotonic();seen=[set()for _ in sites];seen[136].add(mask);todo=collections.deque([(136,mask)]);n=0
while todo:
 i,p=todo.popleft();n+=1
 for j,q in images(i,p):
  if q not in seen[j]:seen[j].add(q);todo.append((j,q))
# Check inductivity independently after closure.
for i,ps in enumerate(seen):
 for p in ps:
  for j,q in images(i,p):assert q in seen[j]
casefacts={};refined=[];old=json.loads((OUT/'source_invariant.json').read_text())['facts']
for i,(pc,op,arg)in enumerate(sites):
 for b in([0,1]if op=='CD'else[0]):
  ps=[p for p in seen[i]if op!='CD'or(p>>arg&1)==b];f=facts(ps);casefacts[f'{i}:{b}']=f
  if f is not None and old[i]is not None:
   improve=[j for j in range(9)if old[i][j]==3 and f[j]!=3 and not(op=='CD'and j==arg)]
   if improve:refined.append({'site':i,'positive':b,'improved_registers':improve,'facts':f})
result={'status':'INDUCTIVE_RELATIONAL_ZERO_PATTERN_CLOSURE','initial_ordinal':136,'initial_values':seed,'reachable_abstract_configurations':n,'max_patterns':max(map(len,seen)),'unreachable_sites':[i for i,x in enumerate(seen)if not x],'conditional_facts':casefacts,'refined_cases':refined,'seconds':time.monotonic()-started}
(OUT/'source_relational_invariant.json').write_text(json.dumps(result,indent=2)+'\n');gzip.open(OUT/'source_relational_patterns.json.gz','wt').write(json.dumps([sorted(x)for x in seen]))
print(json.dumps({k:v if k!='refined_cases'else len(v)for k,v in result.items()if k!='conditional_facts'},indent=2))
