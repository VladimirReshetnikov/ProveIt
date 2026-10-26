#!/usr/bin/env python3
"""Finite arithmetic regressions; not a substitute for the unbounded proof."""
import json

def need(x,m):
 if not x:raise ValueError(m)
def pell(A,k):
 x,y=1,0
 for _ in range(k):x,y=A*x+(A*A-1)*y,x+A*y
 return x,y

def main():
 frame_cases=0;pool_cases=0;mixed_cases=0
 for W in range(2,41):
  for j in range(8*W+1):
   x,y=pell(W+1,j);need((y-j)%(2*W)==0,'2W index congruence');frame_cases+=1
  x,y=pell(W+1,2*W);need(y%(2*W)==0 and y//(2*W)>0,'positive frame quotient');need(x>4*W**(2*W),'strong frame lower bound')
 for A in range(2,21):
  for n in range(1,A):
   T=2*A*n-n*n-1;need(T>0,'T positive')
   req=[]
   for k in (1,2,5):
    X,Y=pell(A,k);Z=A*Y-X;m=n**k;f=n*Y-Z-m;need(f>=0 and f%T==0,'old natural quotient');h=f//T;req.append((X,Y,Z,m,h,k))
   U=sum(Y*Y for X,Y,Z,m,h,k in req);M=T*sum(h*h for X,Y,Z,m,h,k in req);K=2*sum(Y*(m+Z)for X,Y,Z,m,h,k in req)+(2*A-n)*M-n*U
   need(U>=0 and M>=0 and K>=0,'pooled natural signs');need(sum((m+Z)**2 for X,Y,Z,m,h,k in req)+M==n*K,'pool equality');pool_cases+=1
   for X,Y,Z,m,h,k in req:
    for eps in (-1,1):
     Zs=A*Y-eps*X;left=pow(n,k,T)*(n*Y-Zs)
     right=pow(n,2*k,T)if eps==1 else -1
     need((left-right)%T==0,'cleared mixed orientation');mixed_cases+=1
 # Demonstrates why the frame/sign proof cannot simply be omitted.
 A,n,Y,Z,m=2,1,1,4,3;T=2*A*n-n*n-1;U=Y*Y;M=(m+Z-n*Y)**2//T;K=2*Y*(m+Z)+(2*A-n)*M-n*U
 need(Y*Y+Z*Z-2*A*Y*Z==1 and (m+Z)**2+M==n*K,'unframed counterexample equations');need(m!=n and A*Y-Z<0,'unframed counterexample witness')
 print(json.dumps({'verified':True,'lower_frame_recurrence_cases':frame_cases,'positive_pool_instances':pool_cases,'mixed_orientation_congruences':mixed_cases,'unframed_reversed_pair_counterexample':{'A':A,'n':n,'Y':Y,'Z':Z,'m':m,'U':U,'M':M,'K':K},'scope':'Finite regressions only; the general statements are proved in PROOF.md.'},indent=2,sort_keys=True))
if __name__=='__main__':main()
