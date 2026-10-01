#!/usr/bin/env python3
"""Complete mask profile proof check and exact four-variable polynomial identities."""
from itertools import combinations_with_replacement,permutations
from fractions import Fraction
from pathlib import Path
import json,hashlib

def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def basis(ms):return any(all(mask>>i&1 for mask,i in zip(ms,p)) for p in permutations(range(3)))
def cross(a,b):
 v=0
 for i in range(3):
  for j in range(3):
   if i!=j and a>>i&1 and b>>j&1:v|=1<<(3-i-j)
 return v
parts=[(0,1,2,3),(0,2,1,3),(0,3,1,2)]
rows=[];sha=hashlib.sha256();profiles=0
for H in (1,3,7):
 neg=[];nonzero=0
 for ms in combinations_with_replacement(range(1,8),3):
  c=sum(bool(t&H) for t in ms)-1 if basis(ms) else 0
  require(c>=0,('triple',H,ms,c));nonzero+=bool(c);profiles+=1
  sha.update(f'{H}:{ms}:{c}\n'.encode())
 for ms in combinations_with_replacement(range(1,8),4):
  Q=sum(bool(ms[i]&H) and basis(ms[:i]+ms[i+1:]) for i in range(4))
  D=sum(basis((cross(ms[a],ms[b]),cross(ms[c],ms[d]),H)) for a,b,c,d in parts)
  c=4*D-3*Q;nonzero+=bool(c);profiles+=1
  sha.update(f'{H}:{ms}:{c}\n'.encode())
  if c<0:neg.append((ms,c))
 expected=[] if H!=3 else [((1,2,5,6),-4),((1,5,6,6),-4),((2,5,5,6),-4),((5,5,6,6),-4)]
 require(neg==expected,('negative profile list',H,neg))
 require(nonzero=={1:138,3:153,7:144}[H],('nonzero count',H,nonzero))
 rows.append(dict(normal_support=H,nonzero_coefficients=nonzero,negative_profiles=neg))
class Poly:
 def __init__(self,x=0):
  self.d=x.d.copy() if isinstance(x,Poly) else (x.copy() if isinstance(x,dict) else ({(0,0,0,0):Fraction(x)} if x else {}))
 def __add__(self,x):
  d=self.d.copy()
  for k,v in Poly(x).d.items():
   d[k]=d.get(k,0)+v
   if not d[k]:del d[k]
  return Poly(d)
 __radd__=__add__
 def __neg__(self):return Poly({k:-v for k,v in self.d.items()})
 def __sub__(self,x):return self+-Poly(x)
 def __rsub__(self,x):return Poly(x)+-self
 def __mul__(self,x):
  d={}
  for k,v in self.d.items():
   for l,w in Poly(x).d.items():
    m=tuple(a+b for a,b in zip(k,l));d[m]=d.get(m,0)+v*w
  return Poly({k:v for k,v in d.items() if v})
 __rmul__=__mul__
 def __truediv__(self,n):return self*Fraction(1,n)
 def __pow__(self,n):
  out=Poly(1)
  for _ in range(n):out=out*self
  return out

def var(i):return Poly({tuple(int(j==i) for j in range(4)):Fraction(1)})
A,B,x,y=[var(i) for i in range(4)]
f=A*x+x*(x-1)/2;g=B*y+y*(y-1)/2
M=A+x;N=B+y;a=A*(A-1);b=B*(B-1)
q=f*N+M*g
D=(f+g)*M*N+((M*N)**2-x*y-x*B**2-y*A**2-A**2*B**2)/2
T=2*(4*D-q*(3*(M+N)+1))
def formula(M,N,a,b):return M*N*((M-N)**2+M+N-2)+a*N*(3*N-M-3)+b*M*(3*M-N-3)-4*a*b
require(not (T-formula(M,N,a,b)).d,'four-variable identity')
M,N=var(0),var(1)
corner_args=[(0,0),(M*(M-1),0),(0,N*(N-1)),(M*(M-1),N*(N-1))]
expected=[M*N*((M-N)**2+M+N-2),M*N*(N-1)*(M+N-1),M*N*(M-1)*(M+N-1),Poly(0)]
for args,want in zip(corner_args,expected):require(not (formula(M,N,*args)-want).d,'corner formula')
out=dict(all_pass=True,mask_profiles=profiles,profile_sha256=sha.hexdigest(),normal_supports=rows,polynomial_identities=5)
print(json.dumps(out,indent=2))
