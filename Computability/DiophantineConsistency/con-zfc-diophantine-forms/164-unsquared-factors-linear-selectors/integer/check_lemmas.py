#!/usr/bin/env python3
"""Finite regressions only; unbounded proofs are in PROOF.md."""
import json,math

def need(t,s):
 if not t:raise ValueError(s)
L=[1]
for n in range(1,1001):
 L.append(math.lcm(L[-1],n));need(L[-1]<=4**n,'lcm bound')
 if n>=2:
  k=(n+1)//2;need(L[k]*math.comb(n,k)%L[n]==0,'lcm recurrence divisor')
for t in range(16,101):
 F=(2*(t+1))**t;need(F>L[t]**2,'linear radius threshold')
 # Valuations suffice to check binomial oddness without constructing B.
 def v2(n):
  a=0
  while n%2==0:a+=1;n//=2
  return a
 need(v2(F)>=t,'F valuation')
 need(all(v2(F+i)==v2(i)for i in range(1,t+1)),'B is odd')
for f in range(7,1001):need(f*f+1<=2**(f-1),'elementary coefficient bound')
for z in range(-10000,10001):
 q=4*z+1;need(q not in[0,-1],'nonzero and minus-one exclusion')
 if q!=1:need(abs(q)>=3 and abs(q+1)>=2,'remaining bases nonunit')
for z in range(-1000,1001):need((2*z+1)**2==4*z*(z+1)+1,'old root forward map')
# Without the mod-four condition the excluded zero-base branch is real:
need((-1)+1==0,'negative-one guard negative control')
print(json.dumps({'status':'pass','scope':'finite arithmetic regressions, not unbounded proofs','lcm_horizons':1000,'radius_horizons':[16,100],'radix_parameters':20001,'root_map_parameters':2001,'minus_one_negative_control':'q=-1 makes q+1=0; oddness alone does not avoid that branch'},indent=2,sort_keys=True))
