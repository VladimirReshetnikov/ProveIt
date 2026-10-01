#!/usr/bin/env python3
from pathlib import Path
from math import comb
from random import Random
import json,time
import numpy as np
from scipy.optimize import minimize
from search import coefficient_profiles

def prep(profiles,N=10000):
 variables={};v=0
 for t in range(1,16):
  variables[t]=[v] if t.bit_count()==1 else [v,v+1];v+=len(variables[t])
 allterms=[{} for _ in range(4)]
 for j in range(1,4):
  for R,c in profiles[j]:
   cur={tuple([0]*v):float(c)}
   for t in set(R):
    m=R.count(t);vs=variables[t]
    if len(vs)==1:
     if m!=1:cur={};break
     factors=[({vs[0]:1},1.)]
    else:
     factors=[({vs[0]:1,vs[1]:m-1},comb(N,m-1)/N**(m-1)),({vs[1]:m},comb(N,m)/N**m)]
    nxt={}
    for e,c0 in cur.items():
     for ee,c1 in factors:
      ne=list(e)
      for i,d in ee.items():ne[i]+=d
      ne=tuple(ne);nxt[ne]=nxt.get(ne,0.)+c0*c1
    cur=nxt
   for e,c0 in cur.items():allterms[j][e]=allterms[j].get(e,0.)+c0
 ex=[];co=[];de=[]
 for j in range(1,4):
  for e,c in allterms[j].items():ex.append(e);co.append(c);de.append(j)
 return np.array(ex),np.array(co),np.array(de),variables

def main():
 rng=Random(561701);nrng=np.random.default_rng(44098);best=100;records=[];start=time.time()
 for case in range(120):
  core=[rng.randrange(8) for _ in range(4)]
  left=[1,2,4]+[rng.randrange(1,8) for _ in range(rng.randrange(4,14))]
  if case%2==0:left=[7]*rng.randrange(7,31)
  if case%3==0:core=[7]*4
  ex,co,de,variables=prep(coefficient_profiles(core,left,4,3))
  def fun(w):
   z=co*np.exp(ex@w);C=np.array([z[de==j].sum() for j in [1,2,3]])
   grads=np.array([ex[de==j].T@z[de==j]/C[j-1] for j in [1,2,3]])
   return 2*np.log(C[1])-np.log(C[0])-np.log(C[2])-np.log(1.8),2*grads[1]-grads[0]-grads[2]
  for seed in range(6):
   w=nrng.normal(0,2,ex.shape[1]);res=minimize(fun,w,jac=True,method='L-BFGS-B',bounds=[(-12,12)]*len(w),options={'maxiter':250,'ftol':1e-13,'gtol':1e-8})
   ratio=float(np.exp(res.fun))
   if ratio<best:
    best=ratio;item=dict(case=case,seed=seed,core=core,left=left,normalized_ratio=ratio,variables=variables,activities=np.exp(res.x).tolist(),diffuse_population=10000,optimizer_success=bool(res.success));records.append(item)
    Path(__file__).with_suffix('.json').write_text(json.dumps(dict(scope='Numerical diagnostic with one heavy and 10000 diffuse vertices per nonsingleton right class; not a theorem',best=item,records=records),indent=2)+'\n');print('BEST',json.dumps(item),flush=True)
   if ratio<1-1e-8:print('CANDIDATE',flush=True);return
  if case%10==0:print('PROGRESS',case,time.time()-start,flush=True)
 print('DONE',120,best,time.time()-start,flush=True)
if __name__=='__main__':main()
