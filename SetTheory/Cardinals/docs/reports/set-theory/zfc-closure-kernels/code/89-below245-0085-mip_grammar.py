#!/usr/bin/env python3
"""Search a finite grammar universe by integer programming.

Constrained projections are preserved by freezing the rules they traverse.
An independent full grammar audit remains necessary for any candidate.
"""
import argparse
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_matrix

P=argparse.ArgumentParser()
P.add_argument('--package',type=Path,required=True)
P.add_argument('--seed',type=Path)
P.add_argument('--output',type=Path,required=True)
P.add_argument('--seconds',type=float,default=120)
P.add_argument('--length',type=int,default=40)
P.add_argument('--target',type=int,default=127)
P.add_argument('--zero',type=int,default=6)
P.add_argument('--complements',action='store_true')
P.add_argument('--lp',action='store_true')
A=P.parse_args();began=time.time(); p=A.package
d=json.loads((A.seed or p/'grammar.json').read_text())
g={w:(l,r)for w,l,r in d['rules']}
lines=(p/'inputs/state_reduction/route-grammar.txt').read_text().splitlines()
n,nr,na=map(int,lines[0].split())
old={w:(w[:int(k)],w[int(k):])for k,w,q in map(str.split,lines[1:n+1])}
allowed={c:int(m)for c,m in map(str.split,lines[n+1+nr:])}
constraints=[]
ls=(p/'inputs/state_reduction/bootstrap-lock54.txt').read_text().splitlines()
constraints += [row.split()for row in ls[1:]]
tok=(p/'inputs/state_reduction/route-constraints.txt').read_text().split();at=1
for i in range(int(tok[0])):
 s,b,w,n=tok[at:at+4];at+=4;w=d['routes'][i]['word']
 for j in range(int(n)):
  pre,t=tok[at:at+2];at+=2;constraints.append((w,pre,t))
ne,orig,na=map(int,tok[at:at+3]);at+=3;expr=[]
for i in range(ne):
 kind=tok[at];at+=1
 if kind=='L': expr.append(('L',))
 elif kind=='W': expr.append(('W',tok[at]));at+=1
 else:expr.append(('N',int(tok[at]),int(tok[at+1])));at+=2
atoms={tok[at+2*i]:int(tok[at+2*i+1])for i in range(na)}
def properties(gram):
 @lru_cache(None)
 def ep(i):
  e=expr[i]
  if e[0]=='L': return (0,0,0)
  if e[0]=='W': return wp(e[1])
  return join(ep(e[1]),ep(e[2]))
 @lru_cache(None)
 def wp(w):
  if len(w)==1:return ep(atoms[w])
  return join(*(wp(x)for x in gram.get(w,old.get(w))))
 def join(a,b):return (a[0]+1,max(a[0]+1,a[1],b[1]),max(a[2],b[2])+1)
 return ep(orig), {a:wp(a)for a in atoms}
frozen=set()
for w,pre,t in constraints:
 for b in pre:frozen.add(w);w=g[w][int(b)]
 assert w==t
main=max(d['roots'],key=len)
freq=Counter(main[i:i+n]for n in range(2,A.length+1)for i in range(len(main)-n+1))
vocab=set(g)|{w for w,c in freq.items()if c>=2}|set(atoms)
if A.complements:
 vocab.update(w[:i]for w in g for i in range(2,len(w)))
 vocab.update(w[i:]for w in g for i in range(1,len(w)-1))
def permitted(l,r):return (len(l)>1 or allowed[l]&1)and(len(r)>1 or allowed[r]&2)
splits={w:([(w,*g[w])] if w in frozen else [(w,w[:k],w[k:])for k in range(1,len(w)) if w[:k]in vocab and w[k:]in vocab and permitted(w[:k],w[k:])])for w in vocab if len(w)>1}
# Drop unsupported words to a fixed point before constructing the IP.
while True:
 bad={w for w,sp in splits.items()if not sp}
 if not bad:break
 for w in bad:del splits[w];vocab.remove(w)
 for w in splits:splits[w]=[(w,l,r)for w,l,r in splits[w]if l not in bad and r not in bad]
words=sorted(splits,key=lambda w:(len(w),w));wi={w:i for i,w in enumerate(words)}
rules=[r for w in words for r in splits[w]];ri={r:i+len(words)for i,r in enumerate(rules)}
nv=len(words)+len(rules);c=np.zeros(nv);c[:len(words)]=1
lower=np.zeros(nv);upper=np.ones(nv);integrality=np.ones(nv)
for w in set(d['roots'])|{r['word']for r in d['routes']}|frozen:lower[wi[w]]=1
R=[];C=[];V=[];lb=[];ub=[]
def row(terms,lo,hi):
 n=len(lb)
 for j,v in terms:R.append(n);C.append(j);V.append(v)
 lb.append(lo);ub.append(hi)
for w in words:
 row([(wi[w],-1)]+[(ri[r],1)for r in splits[w]],0,0)
for r in rules:
 w,l,h=r
 for v in set((l,h)):
  if len(v)>1:row([(ri[r],1),(wi[v],-1)],-np.inf,0)
row([(wi[w],1)for w in words],-np.inf,A.target)
# Leading-zero ranks provide a conservative scanner guard using exact atom
# ranks at the baseline. Their stability is checked after the solve.
bp,atomprops=properties(g)
if A.zero:
 off=nv;nv+=len(words)
 c=np.pad(c,(0,len(words)));lower=np.pad(lower,(0,len(words)));upper=np.concatenate((upper,np.full(len(words),A.zero,dtype=float)));integrality=np.pad(integrality,(0,len(words)))
 big=A.zero+1
 for r in rules:
  w,l,h=r
  terms=[(off+wi[w],1),(ri[r],-big)]
  val=1-big
  if len(l)>1:terms.append((off+wi[l],-1))
  else:val+=atomprops[l][0]
  row(terms,val,np.inf)
mat=coo_matrix((V,(R,C)),shape=(len(lb),nv)).tocsc()
print(json.dumps(dict(status='START',words=len(words),rules=len(rules),frozen=len(frozen),constraints=len(lb),variables=nv,baseline_props=bp,preparation_seconds=time.time()-began)),flush=True)
if A.lp:
 from scipy.optimize import linprog
 from scipy.sparse import vstack
 lo=np.array(lb);hi=np.array(ub)
 eq=np.where(lo==hi)[0];le=np.where((lo!=hi)&np.isfinite(hi))[0];ge=np.where((lo!=hi)&np.isfinite(lo))[0]
 req=mat[eq];rle=vstack((mat[le],-mat[ge])).tocsc()
 res=linprog(c,A_ub=rle,b_ub=np.concatenate((hi[le],-lo[ge])),A_eq=req,b_eq=lo[eq],bounds=np.column_stack((lower,upper)),method='highs',options={'time_limit':A.seconds})
 report=dict(status=res.status,message=res.message,objective=res.fun,seconds=time.time()-began)
 A.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2)+'\n');print(report)
 if res.success:
  import gzip
  sparse=lambda m:dict(shape=m.shape,entries=list(zip(m.tocoo().row.tolist(),m.tocoo().col.tolist(),m.tocoo().data.tolist())))
  cert=dict(c=c.tolist(),lower=lower.tolist(),upper=upper.tolist(),eq=sparse(req),eq_b=lo[eq].tolist(),le=sparse(rle),le_b=np.concatenate((hi[le],-lo[ge])).tolist(),eq_dual=res.eqlin.marginals.tolist(),le_dual=res.ineqlin.marginals.tolist(),report=report,words=words,rules=rules)
  with gzip.open(A.output.with_suffix('.lp.json.gz'),'wt')as f:json.dump(cert,f)
 raise SystemExit(0)
res=milp(c=c,integrality=integrality,bounds=Bounds(lower,upper),constraints=LinearConstraint(mat,np.array(lb),np.array(ub)),options={'time_limit':A.seconds,'mip_rel_gap':0,'presolve':True})
report=dict(status=res.status,message=res.message,seconds=time.time()-began,words=len(words),rules=len(rules),frozen=len(frozen),target=A.target)
for name in ('fun','mip_gap','mip_node_count','mip_dual_bound'):
 v=getattr(res,name,None)
 if v is not None:report[name]=float(v)
if res.x is not None:
 out={w:(l,r)for w,l,r in rules if res.x[ri[w,l,r]]>0.5}
 prop,newatoms=properties(out)
 seen=set()
 def visit(w):
  if len(w)==1 or w in seen:return
  seen.add(w)
  for child in out[w]:visit(child)
 for w in set(d['roots'])|{r['word']for r in d['routes']}:visit(w)
 out={w:r for w,r in out.items()if w in seen}
 report.update(candidate_rules=len(out),properties=prop,atomprops_stable=atomprops==newatoms)
 dd=dict(d);dd.update(rules_count=len(out),rules=[[w,*out[w]]for w in sorted(out)],properties=list(prop),search_method='finite-universe-milp',search_report=report)
 A.output.write_text(json.dumps(dd,indent=2)+'\n')
print(json.dumps(report,indent=2),flush=True)
A.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2)+'\n')
