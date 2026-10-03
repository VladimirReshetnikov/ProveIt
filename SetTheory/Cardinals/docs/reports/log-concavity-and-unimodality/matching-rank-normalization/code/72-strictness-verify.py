"""Exact finite regressions for the strictness proof, not an asymptotic proof."""
from itertools import product
from pathlib import Path
from collections import Counter
import json

def counts(adj,u,v):
 out=[0]*(min(len(u),len(v))+1)
 for mask in range(1<<len(u)):
  possible={0};weight=1
  for i in range(len(u)):
   if mask>>i&1:
    weight*=u[i]
    possible={S|(1<<j) for S in possible for j in adj[i] if not S>>j&1}
  for S in possible:
   w=weight
   for j in range(len(v)):
    if S>>j&1:w*=v[j]
   out[mask.bit_count()]+=w
 while len(out)>1 and out[-1]==0:out.pop()
 return out

def exception(adj,u,v):
 n=len(u);m=len(v);graph=[set() for _ in range(n+m)]
 for i,A in enumerate(adj):
  for j in A:graph[i].add(n+j);graph[n+j].add(i)
 seen=set();totals=[]
 for start in range(n+m):
  if start in seen or not graph[start]:continue
  comp={start};todo=[start];seen.add(start)
  while todo:
   p=todo.pop()
   for q in graph[p]:
    if q not in seen:seen.add(q);comp.add(q);todo.append(q)
  edges=[(i,j) for i in comp if i<n for j in adj[i]]
  isstar=any(all(k==i or n+j==k for i,j in edges) for k in comp)
  if not isstar:return False
  totals.append(sum(u[i]*v[j] for i,j in edges))
 return len(set(totals))<=1

report=Counter();fields=[((1,1,1),(1,1,1)),((1,2,4),(4,2,1)),((2,3,5),(7,11,13))]
for bits in range(1<<9):
 adj=[{j for j in range(3) if bits>>(3*i+j)&1} for i in range(3)]
 for u,v in fields:
  a=counts(adj,u,v);r=len(a)-1
  if r<2:continue
  gaps=[k*(r-k)*a[k]**2-(k+1)*(r-k+1)*a[k-1]*a[k+1] for k in range(1,r)]
  predicted=exception(adj,u,v)
  assert (all(g==0 for g in gaps) if predicted else all(g>0 for g in gaps)),(bits,u,v,a,gaps,predicted)
  report['weighted_graph_cases']+=1;report['individual_gaps']+=len(gaps)
  report['balanced_star_cases' if predicted else 'strict_cases']+=1
out={'status':'PASS','scope':'All 512 simple 3-by-3 bipartite graphs, three exact positive integer fields; rank zero and one skipped','counts':dict(report),'caveat':'Finite regression only; universal proofs are in strictness_equality.tex'}
Path(__file__).with_name('verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
