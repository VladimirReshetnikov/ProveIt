"""Exact canonical integration-by-parts normal forms over Q.

A polynomial is a dict mapping the finite exponent tuple (m0,m1,...)
to fractions.Fraction coefficients; trailing zero exponents are omitted.
reduce(P) returns N,H with P=N+D(H), and N has functional support.
This is the independent terminating algorithm proved in article.pdf.
"""
from fractions import Fraction as F
from functools import lru_cache

def trim(t):
 t=tuple(t)
 while t and t[-1]==0:t=t[:-1]
 return t

def add(P,Q,c=F(1)):
 for m,v in Q.items():
  P[m]=P.get(m,F(0))+c*v
  if not P[m]:del P[m]
 return P

def deriv(P):
 out={}
 for m,c in P.items():
  for i,n in enumerate(m):
   if not n:continue
   t=list(m)+[0];t[i]-=1;t[i+1]+=1;t=trim(t)
   out[t]=out.get(t,F(0))+c*n
 return {m:c for m,c in out.items() if c}

def functional(m):return len(m)<=1 or m[-1]>=2

@lru_cache(None)
def reduce_m(m):
 if functional(m):return {m:F(1)},{}
 r=len(m)-1;T=list(m);T[r]-=1;T[r-1]+=1;a=T[r-1];T=trim(T)
 rest=deriv({T:F(1,a)});rest.pop(m)
 N={};H={T:F(1,a)}
 for q,c in rest.items():
  nq,hq=reduce_m(q);add(N,nq,-c);add(H,hq,-c)
 return N,H

def reduce(P):
 N={};H={}
 for m,c in P.items():
  nn,hh=reduce_m(m);add(N,nn,c);add(H,hh,c)
 return N,H

def bell_next(P):
 Q={}
 for m,c in P.items():
  t=list(m) if m else [0];t[0]+=1;Q[trim(t)]=c
 add(Q,deriv(P),F(-1))
 return Q

def coeff(P,*m):return P.get(trim(m),F(0))

if __name__=='__main__':
 import json,time,math
 P={():F(1)};start=time.time()
 data={}
 for n in range(25):
  N,H=reduce(P)
  assert add(dict(N),deriv(H))==P
  for m,c in N.items():
   if len(m)==4 and m[0]==0 and m[3]>=2:print(n,m,c,flush=True)
  data[n]={'N':{','.join(map(str,m)):str(c) for m,c in N.items()},'H':{','.join(map(str,m)):str(c) for m,c in H.items()}}
  P=bell_next(P)
 json.dump(data,open('normal_data.json','w'),indent=2)
 print('seconds',time.time()-start,'cache',reduce_m.cache_info(),flush=True)
