#!/usr/bin/env python3
from pathlib import Path
from random import Random
from collections import Counter
import numpy as np,json,time
from scipy.optimize import minimize
from search import coefficient_profiles,prepare

def main():
 rng=Random(188882);nrng=np.random.default_rng(48821);best=100.;history=[];start=time.time()
 types=[1,2,4,9,10,12];pops=[1]*15
 for t,n in [(9,3),(10,2),(12,2)]:pops[t-1]=n
 for case in range(600):
  core=[1,1,1,3]
  if case%4==0:core=[1,1,1,7]
  if case%11==0:core=[1,1,3,7]
  left=[1,2,4]+[rng.randrange(1,8) for _ in range(rng.randrange(4,25))]
  if case%3==0:
   left=[1,2,4]
   for t in range(1,8):left.extend([t]*rng.choice([0,1,2,5,20,100]))
  prof=coefficient_profiles(core,left,4,3,types)
  ex,co,de=prepare(prof,15,pops);keep=(de>=1)&(de<=3);ex=ex[keep][:,[t-1 for t in types]];co=co[keep];de=de[keep]
  def fun(w):
   z=co*np.exp(ex@w);C=np.array([z[de==j].sum() for j in [1,2,3]])
   gr=np.array([ex[de==j].T@z[de==j]/C[j-1] for j in [1,2,3]])
   return 2*np.log(C[1])-np.log(C[0])-np.log(C[2])-np.log(1.8),2*gr[1]-gr[0]-gr[2]
  for seed in range(4):
   w=np.log([pops[t-1] for t in types]) if seed==0 else nrng.normal(0,3,len(types))
   result=minimize(fun,w,jac=True,method='L-BFGS-B',bounds=[(-12,12)]*len(w),options={'maxiter':200,'ftol':1e-14,'gtol':1e-9})
   ratio=float(np.exp(result.fun))
   if ratio<best:
    best=ratio;item=dict(case=case,core=core,left_counts=dict(Counter(left)),right_types=types,right_populations=[pops[t-1] for t in types],right_totals=np.exp(result.x).tolist(),normalized_ratio=ratio,optimizer_success=bool(result.success));history.append(item)
    Path(__file__).with_suffix('.json').write_text(json.dumps(dict(scope='Numerical discovery only, corrected Choe-Wagner Rayleigh seed',best=item,records=history),indent=2)+'\n');print('BEST',json.dumps(item),flush=True)
   if ratio<1-1e-8:print('CANDIDATE',flush=True);return
  if case%50==0:print('PROGRESS',case,time.time()-start,flush=True)
 print('DONE',600,best,time.time()-start,flush=True)
if __name__=='__main__':main()
