from pathlib import Path
from collections import defaultdict
import json,sys
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_matrix
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'construction/vendor'
sys.path.insert(0,str(BASE));import compiler as c
inc=('leaf','inc',1)
def word(t):
 if t=='node60':return [inc]*2
 if t=='node61':return [inc]*4
 if c.isnode(t):return word(t[0])+word(t[1])
 return [t]
gram=c.read_grammar(Path(__file__).with_name('inputs')/'primary.grammar.json')
w=tuple(word(gram));print('length',len(w),flush=True)
occ=defaultdict(list)
for i in range(len(w)):
 for j in range(i+2,len(w)+1):occ[w[i:j]].append(i)
free={(inc,inc),(inc,inc,inc,inc)}
words=[t for t,ps in occ.items() if (len(ps)>1 and ps[-1]-ps[0]>=len(t)) and t not in free]+[w]
words=sorted(set(words),key=lambda t:(len(t),repr(t)))
W={t:k for k,t in enumerate(words)}; m=len(words)
print('repeated words',m,'max',max(map(len,words)),flush=True)
# One chosen RHS segmentation per active repeated-word rule; all coefficients integral.
obj=[-1.]*m; lb=[0.]*m; ub=[1.]*m;lb[W[w]]=1
cols=[];rows=[];vals=[];lo=[];hi=[]
def constraint(terms,l,h):
 idx=len(lo);lo.append(l);hi.append(h)
 for k,v in terms:rows.append(idx);cols.append(k);vals.append(v)
def var(cost):
 k=len(obj);obj.append(cost);lb.append(0.);ub.append(1.);return k
edges={};chain=[]
for k,t in enumerate(words):
 n=len(t);es=[]
 for i in range(n):
  for j in range(i+1,n+1):
   u=t[i:j]
   if j-i==1 or u in free or (u in W and len(u)<n):
    q=var(1.);es.append((i,j,q,u));edges[q]=(k,i,j)
    if len(u)>1 and u not in free:constraint([(q,1),(W[u],-1)],-np.inf,0)
 for i in range(n+1):
  ts=[(q,1 if a==i else -1)for a,b,q,u in es if a==i or b==i]
  if i==0:ts.append((k,-1))
  if i==n:ts.append((k,1))
  constraint(ts,0,0)
 chain.append(es)
A=coo_matrix((vals,(rows,cols)),shape=(len(lo),len(obj))).tocsc()
print('variables',len(obj),'constraints',len(lo),flush=True)
res=milp(np.array(obj),integrality=np.ones(len(obj)),bounds=Bounds(lb,ub),constraints=LinearConstraint(A,lo,hi),options={'time_limit':float(sys.argv[1])if len(sys.argv)>1 else 120,'mip_rel_gap':0.,'disp':True})
print(res.message, res.fun, getattr(res,'mip_gap',None),flush=True)
output={'status':res.message,'objective':res.fun,'gap':getattr(res,'mip_gap',None),'dual_bound':getattr(res,'mip_dual_bound',None),'word':w,'grammar':[]}
if res.x is not None:
 for k,t in enumerate(words):
  if res.x[k]>.5:
   used=[(a,b,u)for a,b,q,u in chain[k]if res.x[q]>.5]
   output['grammar'].append({'id':k,'word':t,'chunks':[list(u)for a,b,u in used]})
Path(__file__).with_name('milp_result.json').write_text(json.dumps(output,indent=2))
