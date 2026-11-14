#!/usr/bin/env python3
from pathlib import Path
import sys,collections,json,time,random
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
BASE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(BASE/'sources/history209'))
import grammar_search as g
W=g.word(g.get_macro_tree()[2])
counts=collections.Counter(W[i:j] for i in range(len(W)) for j in range(i+2,len(W)+1))
patterns=sorted([s for s,c in counts.items() if c>1],key=lambda s:(len(s),s))
pset=set(patterns);strings=patterns+[W];yn={s:i for i,s in enumerate(patterns)}
edges=[];vs=len(patterns)
obj=[-1.0]*vs;integrality=[1]*vs
edge_by_string={};in_uses=collections.defaultdict(list)
for s in strings:
 es=[]
 for i in range(len(s)):
  for j in range(i+1,len(s)+1):
   t=s[i:j]
   if t==s:continue
   if len(t)>1 and t not in pset:continue
   eid=len(obj);obj.append(1.0);integrality.append(1)
   es.append((eid,i,j,t));edges.append((eid,s,i,j,t))
   if t in yn:in_uses[t].append(eid)
 edge_by_string[s]=es
ar=[];ac=[];av=[];lb=[];ub=[]
def con(coeff,lo,hi):
 n=len(lb);lb.append(lo);ub.append(hi)
 for j,v in coeff.items():ar.append(n);ac.append(j);av.append(v)
for s in strings:
 es=edge_by_string[s]
 for i in range(len(s)+1):
  terms={}
  for eid,a,b,t in es:
   if a==i:terms[eid]=1
   if b==i:terms[eid]=-1
  if s==W:
   val=1 if i==0 else -1 if i==len(s) else 0
  else:
   val=0
   if i==0:terms[yn[s]]=-1
   if i==len(s):terms[yn[s]]=1
  con(terms,val,val)
for eid,s,i,j,t in edges:
 if t in yn:con({eid:1,yn[t]:-1},-np.inf,0)
for s in patterns:
 terms={yn[s]:1}
 for eid in in_uses[s]:terms[eid]=-1
 con(terms,-np.inf,0)
# At least match the published DAG count; no lower-bound claim inferred.
con(dict(enumerate(obj)),-np.inf,69)
mat=coo_matrix((av,(ar,ac)),shape=(len(lb),len(obj))).tocsc()
print('MODEL',len(patterns),'patterns',len(obj),'variables',len(lb),'rows',flush=True)
start=time.time()
r=milp(np.array(obj),integrality=np.array(integrality),bounds=Bounds(0,1),
 constraints=LinearConstraint(mat,np.array(lb),np.array(ub)),
 options={'time_limit':180,'mip_rel_gap':0,'disp':True})
print('RESULT',r.message,'fun',r.fun,'bound',r.mip_dual_bound,'sec',time.time()-start,flush=True)
if r.x is None:sys.exit(0)
defs={}
for s in strings:
 if s!=W and r.x[yn[s]]<.5:continue
 parts=[(i,t) for eid,i,j,t in edge_by_string[s] if r.x[eid]>.5]
 parts.sort();assert ''.join(t for i,t in parts)==s
 defs[s]=[t for i,t in parts]
def cv(s,kind='right'):
 if len(s)==1:return s
 parts=[cv(t,kind) for t in defs[s]]
 def merge(parts):
  if len(parts)==1:return parts[0]
  if kind=='right':return parts[0],merge(parts[1:])
  if kind=='left':return merge(parts[:-1]),parts[-1]
  m=len(parts)//2;return merge(parts[:m]),merge(parts[m:])
 return merge(parts)
for kind in ('right','left','balanced'):
 tree=cv(W,kind);assert g.word(tree)==W
 (BASE/f'research/milp_{kind}.json').write_text(json.dumps(tree))
 print('TREE',kind,g.count(tree),flush=True)
(BASE/'research/milp_result.json').write_text(json.dumps({'objective':r.fun,'bound':r.mip_dual_bound,'definitions':defs,'time':time.time()-start},indent=2))
