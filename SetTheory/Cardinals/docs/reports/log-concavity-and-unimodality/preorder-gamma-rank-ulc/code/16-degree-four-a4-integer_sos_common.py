"""Global integer-domain SOS: binomial multipliers and core-symmetry orbit averages."""
import json,itertools,math,time,sys
from pathlib import Path
from functools import lru_cache
from fractions import Fraction as F
import numpy as np
import sympy as sp
from sympy.polys.matrices import DomainMatrix
from scipy.optimize import linprog
from scipy.sparse import csc_matrix
D=Path(__file__).parent
T={r['id']:r for r in map(json.loads,(D/'a4_gaps.jsonl').read_text().splitlines())}
O={r['id']:r for r in json.loads((D/'face_orbits.json').read_text())}
def exps(d,n):
 if not d:return [0]
 return [a+(e<<3) for a in range(n+1) for e in exps(d-1,n-a)]
def degree(c):
 n=0
 while c:n+=c&7;c>>=3
 return n
@lru_cache(maxsize=200000)
def bp(a,b):
 overlap=[];aa=a;bb=b;j=0
 while aa or bb:
  x=aa&7;y=bb&7
  if x and y:overlap.append((j,x,y))
  aa>>=3;bb>>=3;j+=1
 out=[(a+b,1)]
 for j,x,y in overlap:out=[(e-(z<<(3*j)),c*math.factorial(x+y-z)//(math.factorial(z)*math.factorial(x-z)*math.factorial(y-z))) for e,c in out for z in range(min(x,y)+1)]
 return out

def ray(a,b,m,u,v):
 p={}
 for x,y,w in((a,a,u*u),(a,b,-2*u*v),(b,b,v*v)):
  for e,c in bp(x,y):
   for f,k in bp(e,m):p[f]=p.get(f,0)+w*c*k
 return {e:c for e,c in p.items() if c}
