"""Independent sparse rational integration-by-parts reducer.
This reference implementation does not use the beta coefficient theorem.
Tuple exponent keys and Fraction coefficients are used throughout.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial,comb

def trim(e):
 e=list(e)
 while e and e[-1]==0:e.pop()
 return tuple(e)
def add(p,q,c=F(1)):
 z=p.copy()
 for e,a in q.items():
  z[e]=z.get(e,F(0))+c*a
  if not z[e]:del z[e]
 return z
def dm(e):
 p={}
 for j,c in enumerate(e):
  if c:
   f=list(e)+[0];f[j]-=1;f[j+1]+=1;p[trim(f)]=F(c)
 return p
def dp(p):
 z={}
 for e,c in p.items():z=add(z,dm(e),c)
 return z
@lru_cache(None)
def nm(e):
 if len(e)<=1 or e[-1]>=2:return {e:F(1)}
 r=len(e)-1;f=list(e);f[r]-=1;f[r-1]+=1;c=f[r-1];f=trim(f)
 rest=dm(f);del rest[e]
 z={}
 for g,a in rest.items():z=add(z,nm(g),-a/c)
 return z
@lru_cache(None)
def hm(e):
 if len(e)<=1 or e[-1]>=2:return {}
 r=len(e)-1;f=list(e);f[r]-=1;f[r-1]+=1;c=f[r-1];f=trim(f)
 rest=dm(f);del rest[e]
 z={f:F(1,c)}
 for g,a in rest.items():z=add(z,hm(g),-a/c)
 return z

def norm(p):
 z={}
 for e,c in p.items():z=add(z,nm(e),c)
 return z

def prim(p):
 z={}
 for e,c in p.items():z=add(z,hm(e),c)
 return z

def hierarchy(M):
 a={():F(1)}
 yield a
 for m in range(M):
  au={}
  for e,c in a.items():
   f=list(e) or [0];f[0]+=1;au[trim(f)]=c
  a=add(au,dp(a),-1)
  yield a
