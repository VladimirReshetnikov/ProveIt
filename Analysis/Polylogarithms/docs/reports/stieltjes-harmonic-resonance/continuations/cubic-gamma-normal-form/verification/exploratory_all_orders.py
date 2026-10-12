"""UNPROVED all-order extension. Exact exploration is not a proof.
Run this module for an independent finite comparison through weight 24.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial,comb
import json

def mul(p,q):
 out=[F(0)]*(len(p)+len(q)-1)
 for i,a in enumerate(p):
  for j,b in enumerate(q):out[i+j]+=a*b
 return tuple(out)
@lru_cache(None)
def pol(m):
 if not any(m):return (F(1),)
 m=list(m);j=next(j for j,k in enumerate(m) if k);m[j]-=1
 q=tuple(F(2*comb(j+1,i),2**(j+1)*factorial(j+1)) if (j+1-i)%2 else F(0) for i in range(j+1))
 return mul(pol(tuple(m)),q)

def formula(m):
 r=len(m)-1;W=sum((j+1)*k for j,k in enumerate(m))
 if r<=0:return F(1)
 if sum(j*k for j,k in enumerate(m))%2:return F(0)
 mm=list(m);mm[0]=0;mm[r]-=2
 p=pol(tuple(mm));P=tuple(F((-1)**(i//2)*comb(r,i//2)) if i%2==0 else F(0) for i in range(2*r+1));q=mul(p,P)
 integral=sum((c/F(j+1) for j,c in enumerate(q) if j%2==0),F(0))
 return F((-1)**r*factorial(W),4**r*factorial(r)*factorial(r+1))*integral/F(__import__('math').prod(factorial(k) for k in m))
if __name__ == '__main__':
 from normal_form import reduce, bell_next
 P={():F(1)}; count=0
 for weight in range(25):
  N,H=reduce(P)
  for m,c in N.items():
   if len(m)>4:
    assert formula(m)==c,(weight,m,c,formula(m))
    count+=1
  P=bell_next(P)
 print(json.dumps({"status":"PASS","highest_derivative_at_least":4,
                   "weight_at_most":24,"nonzero_coefficients_checked":count,
                   "conjecture_status":"UNPROVED"},indent=2))
