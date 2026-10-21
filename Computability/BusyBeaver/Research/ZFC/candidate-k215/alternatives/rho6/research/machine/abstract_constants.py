#!/usr/bin/env python3
"""Finite product abstract interpretation of full register source from calibrated boot.
Masks encode natural values0..cap individually and a >cap tail. Exact finite transfer
relations overapproximate CI/CD on all natural inputs. Join is componentwise union.
"""
from pathlib import Path
from collections import deque,Counter
import sys,json,hashlib,time
P=Path('/workspace/scratch/f42aca38d186/ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k215')
sys.path.insert(0,str(P));import source_language as s
cap=int(sys.argv[1]) if len(sys.argv)>1 else 3
out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=False)
rows=json.loads((P/'sites215.json').read_text());g=s.graph_intervals(rows);assert g==s.graph_arithmetic(rows)[0]
n=len(rows);top=(1<<(cap+2))-1;zero=1;tail=1<<(cap+1)
def abstract(v):return 1<<min(v,cap+1)
def inc(m):
 return ((m<<1)&top)|(tail if m&tail else 0)
def dec_positive(m):
 return (m>>1)|(tail if m&tail else 0)
I=[None]*n;I[0]=tuple(abstract(v)for v in[4,0,0,0,0,0,0,0,0]);todo=deque([0]);queued={0};updates=0
while todo:
 i=todo.popleft();queued.discard(i);vs=I[i];op,r=rows[i][1:];targets=g[i][1];success=[]
 if op=='CI':w=list(vs);w[r]=inc(vs[r]);success.append((targets[0],tuple(w)))
 elif op=='CD':
  if vs[r]&1:w=list(vs);w[r]=1;success.append((targets[0],tuple(w)))
  if vs[r]&~1:w=list(vs);w[r]=dec_positive(vs[r]&~1);success.append((targets[1],tuple(w)))
 elif op!='CH':success=[(targets[0],vs)]
 for j,w in success:
  z=w if I[j]is None else tuple(x|y for x,y in zip(w,I[j]))
  if z!=I[j]:I[j]=z;updates+=1
  else:continue
  if j not in queued:queued.add(j);todo.append(j)
constant=[];positive=[];unreachable=[];nr=[]
for i,(p,op,r)in enumerate(rows):
 if I[i]is None:unreachable.append(i)
 if op=='CD' and I[i] is not None and I[i][r]==1:constant.append(i);nr.append([p,'CB',1])
 else:nr.append([p,op,r])
 if op=='CD' and I[i]is not None and not(I[i][r]&1):positive.append(i)
T=s.tree(nr)
r={'status':'PRODUCT_ABSTRACT_FIXED_POINT','cap':cap,'updates':updates,'constant_zero_CD':constant,'always_positive_CD':positive,'unreachable':unreachable,'old_metrics':s.metrics(s.tree(rows)),'new_metrics':s.metrics(T),'source_sha256':hashlib.sha256(s.compact(nr)).hexdigest(),'invariant':I}
(out/'result.json').write_text(json.dumps(r,indent=2)+'\n');(out/'sites.json').write_bytes(s.compact(nr));print(json.dumps({k:v for k,v in r.items()if k!='invariant'},indent=2))
