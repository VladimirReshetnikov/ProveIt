#!/usr/bin/env python3
"""Exact integer coefficient check of the centered two-root identity."""
from collections import defaultdict
from pathlib import Path
import json
N=6
class P:
 def __init__(self,d):self.d={m:c for m,c in d.items() if c}
 @staticmethod
 def const(c):return P({(0,)*N:c})
 def cast(self,b):return b if isinstance(b,P) else P.const(b)
 def __add__(self,b):
  b=self.cast(b);d=defaultdict(int,self.d)
  for m,c in b.d.items():d[m]+=c
  return P(d)
 __radd__=__add__
 def __neg__(self):return P({m:-c for m,c in self.d.items()})
 def __sub__(self,b):return self+-self.cast(b)
 def __rsub__(self,b):return -self+b
 def __mul__(self,b):
  b=self.cast(b);d=defaultdict(int)
  for m,c in self.d.items():
   for n,e in b.d.items():d[tuple(x+y for x,y in zip(m,n))]+=c*e
  return P(d)
 __rmul__=__mul__
 def __pow__(self,n):
  a=P.const(1)
  for i in range(n):a=a*self
  return a
vs=[]
for i in range(N):
 m=[0]*N;m[i]=1;vs.append(P({tuple(m):1}))
x,M,t,V,ell,delta=vs
j=delta*(x*x+M*(6*t+4*V)*x+9*M*M*ell)-4*M*M*(V*V-1)
center=j*j+24*delta*t*V*M*M*j+144*delta*M**4*((t*t-ell)*(1-V*V)+delta*ell*V*V)
Z=x+M*(3*t+2*V);Cy=(delta+1)*V*V-1
original=(delta*(Z*Z-9*M*M*(t*t-ell))-4*M*M*Cy)**2-144*delta*M**4*(t*t-ell)*Cy
if (center-original).d:raise RuntimeError('Center identity failed')
receipt={'status':'PASS','variables':['x','M','t0','V','ell','delta'],'coefficient_domain':'integers','nonzero_monomials':len(center.d),'difference_nonzero_monomials':0,'specializations':'No nonzero, sign, integrality or irreducibility condition used'}
(Path(__file__).resolve().parent/'CENTER_IDENTITY.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
