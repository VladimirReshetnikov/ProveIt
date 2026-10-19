#!/usr/bin/env python3
"""Branch on grammar presence variables and emit exact rational LP bounds.

The finite dictionary universe is explicit. Bounds concern that universe and
the frozen projection rules only; no global TM lower bound is implied.
"""
import argparse,gzip,json,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix,vstack,hstack,csr_matrix
P=argparse.ArgumentParser();P.add_argument('model',type=Path);P.add_argument('output',type=Path);P.add_argument('--bound',type=int,default=127);P.add_argument('--nodes',type=int,default=250)
A=P.parse_args();D=json.load(gzip.open(A.model,'rt'));began=time.monotonic();nw=len(D['words']);nv=len(D['c'])
def matrix(spec):
 if not spec['entries']:return csr_matrix(spec['shape'])
 i,j,x=zip(*spec['entries']);return coo_matrix((x,(i,j)),shape=spec['shape']).tocsr()
eq=matrix(D['eq']);le=matrix(D['le']);c=np.array(D['c']);eb=np.array(D['eq_b']);lb=np.array(D['le_b']);lo=np.array(D['lower']);hi=np.array(D['upper'])
def rational(x):return F(float(x)).limit_denominator(1<<22)
def exact_bound(res,lows,highs):
 yd=[rational(x)for x in res.eqlin.marginals];zu=[min(F(0),rational(x))for x in res.ineqlin.marginals];r=[F(int(x))for x in c]
 for i,j,v in D['eq']['entries']:r[j]-=yd[i]*int(v)
 for i,j,v in D['le']['entries']:r[j]-=zu[i]*int(v)
 value=sum(y*int(b)for y,b in zip(yd,eb))+sum(z*int(b)for z,b in zip(zu,lb))+sum(v*int(lows[j]if v>=0 else highs[j])for j,v in enumerate(r))
 enc=lambda x:[x.numerator,x.denominator]
 return value,dict(eq_dual=[[i,*enc(v)]for i,v in enumerate(yd)if v],le_dual=[[i,*enc(v)]for i,v in enumerate(zu)if v],bound=enc(value))
count=0;leaves=0;maxdepth=0;history=[];done=False
def branch(lows,highs,depth):
 global count,leaves,maxdepth
 if count>=A.nodes:return dict(status='OPEN_NODE_BUDGET')
 count+=1;maxdepth=max(maxdepth,depth);res=linprog(c,A_ub=le,b_ub=lb,A_eq=eq,b_eq=eb,bounds=np.column_stack((lows,highs)),method='highs')
 node=dict(index=count,depth=depth,solver_status=res.status)
 if not res.success:
  node.update(status='OPEN_LP_INFEASIBILITY_REQUIRES_FARKAS');return node
 value,cert=exact_bound(res,lows,highs)
 node['floating_bound']=float(res.fun)
 if value>A.bound:
  leaves+=1;node.update(status='EXACT_BOUND',certificate=cert);return node
 frac=[j for j in range(nw)if abs(res.x[j]-round(res.x[j]))>1e-7]
 if not frac:
  node.update(status='INTEGER_GRAMMAR_FOUND',selected_words=[D['words'][j]for j in range(nw)if res.x[j]>.5]);return node
 # Fractional presence variables suffice: once all are binary, every selected
 # symbol admits at least one production supported on selected children.
 j=min(frac,key=lambda j:(abs(res.x[j]-.5),len(D['words'][j])))
 node.update(status='BRANCH',variable=j,word=D['words'][j],value=float(res.x[j]))
 hh=highs.copy();hh[j]=0;left=branch(lows,hh,depth+1)
 ll=lows.copy();ll[j]=1;right=branch(ll,highs,depth+1)
 node['children']=[left,right]
 if depth<3:print('progress',count,'depth',depth,'bounds',res.fun,'leaves',leaves,'seconds',time.monotonic()-began,flush=True)
 return node
tree=branch(lo,hi,0)
def closed(n):return n['status']=='EXACT_BOUND' or(n['status']=='BRANCH' and all(closed(ch)for ch in n['children']))
report=dict(status='EXACT_FINITE_UNIVERSE_LOWER_BOUND'if closed(tree)else'INCOMPLETE_CERTIFICATE_SEARCH',working_grammar_lower_bound=A.bound+1,nodes=count,leaves=leaves,maxdepth=maxdepth,seconds=time.monotonic()-began,scope='Specified finite dictionary universe with frozen rules only',tree=tree)
with gzip.open(A.output,'wt')as f:json.dump(report,f)
print(json.dumps({k:v for k,v in report.items()if k!='tree'},indent=2))
