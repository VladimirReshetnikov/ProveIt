"""Finite dictionary search of physically realizable binary sequence grammars.
The solver searches exact canonical closed-atom words and guards physical atom
orientations. Its output is only a candidate until independent audits pass.
"""
import json,sys,time
from pathlib import Path
from collections import Counter,defaultdict
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
P=Path(__file__).resolve().parent
base=json.loads((P/'inputs/canonical-baseline.json').read_text())
old={w:(a,b)for w,a,b in base['rules']}
lines=(P/'inputs/canonical-grammar.txt').read_text().splitlines();nn,nr,na=map(int,lines[0].split());mask={w:int(m)for w,m in map(str.split,lines[nn+1+nr:])};terms=set(mask)
roots=set(base['roots'])|{r['word']for r in base['routes']}
# Freeze sufficient blank bootstrap relations; routes remain at their existing
# semantic roots but their partitions may change subject to 22 projections.
locks={}
for w,b,t in map(str.split,(P/'inputs/canonical-lock54.txt').read_text().splitlines()[1:]):locks[w,int(b)]=t
routes={(r['source'],r['read']):r['word']for r in base['routes']}
ls=(P/'inputs/canonical-constraints.txt').read_text().splitlines();ng=int(ls[0]);i=1;projections=[]
for _ in range(ng):
 src,read,w,n=ls[i].split();i+=1
 for _ in range(int(n)):
  pre,t=ls[i].split();i+=1;projections.append((routes[int(src),int(read)],pre,t))
maxlen=int(sys.argv[1])if len(sys.argv)>1 else 24
seconds=int(sys.argv[2])if len(sys.argv)>2 else 300
prefix=sys.argv[3]if len(sys.argv)>3 else 'milp'
count=Counter(w[i:i+n]for w in roots for n in range(2,min(len(w),maxlen)+1)for i in range(len(w)-n+1))
words=set(old)|{w for w,c in count.items()if c>=2}
# No new rule may shadow a physical dictionary terminal in this search.

longest=max(roots,key=len)
words.update(longest[i:]for i in range(len(longest)-1))
words.update(longest[:i]for i in range(2,len(longest)))
words-=terms
words=sorted(words,key=lambda w:(len(w),w));possible=set();splits={}
for w in words:
 a=[]
 for k in range(1,len(w)):
  l,r=w[:k],w[k:]
  if not(l in possible or l in terms and mask[l]&1):continue
  if not(r in possible or r in terms and mask[r]&2):continue
  if (w,0)in locks and locks[w,0]!=l:continue
  if (w,1)in locks and locks[w,1]!=r:continue
  a.append((l,r))
 if a:possible.add(w);splits[w]=a
assert roots<=possible,roots-possible
words=[w for w in words if w in possible];idx={w:i for i,w in enumerate(words)}
y={};nv=len(words)
for w in words:
 for k in range(len(splits[w])):y[w,k]=nv;nv+=1
rows=[];cols=[];data=[];lo=[];hi=[]
def add(co,l,u):
 j=len(lo);lo.append(l);hi.append(u)
 for k,v in co.items():
  if v:rows.append(j);cols.append(k);data.append(v)
for w in words:
 add({idx[w]:-1,**{y[w,k]:1 for k in range(len(splits[w]))}},0,0)
 for k,(a,b)in enumerate(splits[w]):
  for x in set((a,b))-terms:add({y[w,k]:1,idx[x]:-1},-np.inf,0)
for w,pre,t in projections:
 if len(pre)==1:
  allowed=[k for k,ab in enumerate(splits[w])if ab[int(pre)]==t]
  add({y[w,k]:1 for k in allowed},1,1)
 elif len(pre)==2:
  b,c=map(int,pre)
  for k,ab in enumerate(splits[w]):
   child=ab[b];opts=[]if child in terms else [h for h,xy in enumerate(splits[child])if xy[c]==t]
   add({y[w,k]:1,**{y[child,h]:-1 for h in opts}},-np.inf,0)
 else:raise ValueError(pre)
# Total objective counts only actual sequence-state rules.
objective=np.zeros(nv);objective[:len(words)]=1
lower=np.zeros(nv);upper=np.ones(nv)
for w in roots:lower[idx[w]]=1
M=coo_matrix((data,(rows,cols)),shape=(len(lo),nv)).tocsc();M.indices=M.indices.astype(np.int32);M.indptr=M.indptr.astype(np.int32)
print('MODEL',len(words),'words',nv,'variables',len(lo),'constraints',flush=True)
import scipy.optimize._highspy._core as hc
from types import SimpleNamespace
model=hc.HighsLp();model.num_col_=nv;model.num_row_=len(lo)
model.col_cost_=objective;model.col_lower_=lower;model.col_upper_=upper
model.row_lower_=np.array(lo);model.row_upper_=np.array(hi)
model.integrality_=[hc.HighsVarType.kInteger]*nv
model.a_matrix_.format_=hc.MatrixFormat.kColwise
model.a_matrix_.num_col_=nv;model.a_matrix_.num_row_=len(lo)
model.a_matrix_.start_=M.indptr;model.a_matrix_.index_=M.indices;model.a_matrix_.value_=M.data
solver=hc._Highs();solver.setOptionValue('threads',1);solver.setOptionValue('time_limit',float(seconds));solver.setOptionValue('mip_rel_gap',0.0);solver.setOptionValue('objective_target',127.0)
assert solver.passModel(model)==hc.HighsStatus.kOk
warm=np.zeros(nv)
for w,ab in old.items():
 warm[idx[w]]=1;warm[y[w,splits[w].index(ab)]]=1
assert np.all(M@warm>=np.array(lo)-1e-7)and np.all(M@warm<=np.array(hi)+1e-7)
solution=hc.HighsSolution();solution.col_value=warm;solution.value_valid=True;assert solver.setSolution(solution)==hc.HighsStatus.kOk
start=time.monotonic();solver.run();info=solver.getInfo();solution=solver.getSolution()
res=SimpleNamespace(x=np.array(solution.col_value) if solution.value_valid else None,fun=info.objective_function_value,status=int(solver.getModelStatus()),message=solver.modelStatusToString(solver.getModelStatus()))

record=dict(maxlen=maxlen,seconds=time.monotonic()-start,status=res.status,message=res.message,objective=res.fun if res.x is not None else None,words=len(words),variables=nv,constraints=len(lo))
if res.x is not None:
 v=np.rint(res.x).astype(int);assert max(abs(res.x-v))<1e-4;assert np.all(M@v>=np.array(lo)-1e-7)and np.all(M@v<=np.array(hi)+1e-7)
 selected={w:splits[w][next(k for k in range(len(splits[w]))if v[y[w,k]])]for w in words if v[idx[w]]}
 d=dict(base,rules_count=len(selected),rules=[[w,*ab]for w,ab in selected.items()],status='ABSTRACT_CANONICAL_MILP_CANDIDATE',search=record)
 (P/(prefix+'.json')).write_text(json.dumps(d,indent=2)+'\n')
(P/(prefix+'-summary.json')).write_text(json.dumps(record,indent=2)+'\n');print('RESULT',record,flush=True)
