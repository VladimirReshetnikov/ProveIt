#!/usr/bin/env python3
"""Independent exact A301746 coefficients and logarithmic reversion checks."""
import sys
if not __debug__:raise SystemExit('Assertions must be enabled; do not use -O.')
from fractions import Fraction as F
from pathlib import Path
from math import comb,factorial
import argparse,json,hashlib
pa=argparse.ArgumentParser();pa.add_argument('--output-dir',type=Path,default=Path(__file__).parent);ar=pa.parse_args();ar.output_dir.mkdir(parents=True,exist_ok=True)
N=150;div=[0]*(N+1)
for k in range(1,N+1):
 for j in range(k,N+1,k):div[j]+=1
b=[v*v for v in div];w=[b[k]-(b[k//2] if k%2==0 else 0) for k in range(N+1)];assert all(v>=1 for v in w[1:])
a=[0]*(N+1);a[0]=1;ea=a[:]
for k in range(1,N+1):
 cap=min(b[k],N//k);a=[sum(comb(b[k],j)*a[n-k*j] for j in range(min(cap,n//k)+1)) for n in range(N+1)]
 ea=[sum(comb(w[k]+j-1,j)*ea[n-k*j] for j in range(n//k+1)) for n in range(N+1)]
assert a==ea
ld=[0]*(N+1)
for k in range(1,N+1):
 for j in range(k,N+1,k):ld[j]+=k*b[k]*(-1)**(j//k+1)
a2=[0]*(N+1);a2[0]=1
for n in range(1,N+1):
 value=sum(ld[j]*a2[n-j] for j in range(1,n+1));assert value%n==0;a2[n]=value//n
assert a2==a and a[:16]==[1,1,4,8,19,35,82,142,291,524,989,1724,3174,5393,9517,16064]
assert all(a[n+1]>a[n] for n in range(1,N))
for j in range(30): assert (j+1)**2==comb(j+3,3)-(comb(j+1,3) if j>=2 else 0)
# Polynomial ring Q[r,c,d][x]/x^5, independent of the symbolic producer code.
CUT=4
def mon(x=0,r=0,c=0,d=0,v=1):return {(x,r,c,d):F(v)} if v else {}
one=mon();x=mon(1);r=mon(r=1);c=mon(c=1);d=mon(d=1)
def add(*aa):
 o={}
 for a0 in aa:
  for k,v in a0.items():o[k]=o.get(k,F(0))+v
 return {k:v for k,v in o.items() if v}
def sc(a0,s):return {k:v*s for k,v in a0.items() if v*s}
def mul(*aa):
 o=one
 for a0 in aa:
  q={}
  for k,v in o.items():
   for ell,w0 in a0.items():
    key=tuple(t+u for t,u in zip(k,ell))
    if key[0]<=CUT:q[key]=q.get(key,F(0))+v*w0
  o={k:v for k,v in q.items() if v}
 return o
def pw(a0,n):
 o=one
 for _ in range(n):o=mul(o,a0)
 return o
def inv(a0):
 assert a0.get((0,0,0,0))==1 and all(k[0] or k==(0,0,0,0) for k in a0)
 u=add(one,sc(a0,-1));return add(*(pw(u,j) for j in range(CUT+1)))
def log(a0):
 u=add(a0,sc(one,-1));assert all(k[0]>=1 for k in u)
 return add(*(sc(pw(u,j),F((-1)**(j+1),j)) for j in range(1,CUT+1)))
def exp(a0):
 assert all(k[0]>=1 for k in a0)
 return add(*(sc(pw(a0,j),F(1,factorial(j))) for j in range(CUT+1)))
def qrat(v):return add(one,sc(v,3),sc(mul(c,pw(v,2)),3),mul(add(sc(c,3),d),pw(v,3)))
def rrat(v):return add(one,sc(v,F(3,2)),sc(mul(c,pw(v,2)),3),mul(add(sc(c,F(3,2)),d),pw(v,3)))
def coeff(a0,j):return {k:v for k,v in a0.items() if k[0]==j}
def lift(a0,j):return {(j,k[1],k[2],k[3]):v for k,v in a0.items()}
results={}
for typ in ['forward','inverse']:
 y=one
 for j in range(1,5):
  v=mul(x,inv(y));v=sc(v,2) if typ=='forward' else v
  extra=qrat(v) if typ=='forward' else rrat(v)
  residual=add(y,sc(one,-1),sc(mul(r,x),-1),sc(mul(x,log(y)),3),mul(x,log(extra)))
  y=add(y,sc(coeff(residual,j),-1))
 v=mul(x,inv(y));v=sc(v,2) if typ=='forward' else v
 lr=add(sc(log(y),F(3,2)),log(rrat(v)),sc(log(qrat(v)),F(-1,2))) if typ=='forward' else add(sc(log(y),-3),log(qrat(v)),sc(log(rrat(v)),-2))
 ans=exp(lr)
 if typ=='forward':
  targets=[one,sc(r,F(3,2)),add(sc(pw(r,2),F(3,8)),sc(r,F(-9,2)),sc(c,6),sc(one,F(-9,2))),add(sc(pw(r,3),F(-1,16)),sc(mul(c,r),-3),sc(c,-18),sc(d,4),sc(r,F(63,4)),sc(one,27))]
 else:
  targets=[one,sc(r,-3),add(sc(pw(r,2),6),sc(r,9),sc(one,F(9,4)),sc(c,-3)),add(sc(pw(r,3),-10),sc(pw(r,2),F(-81,2)),sc(r,F(-153,4)),sc(one,F(-81,8)),sc(mul(c,r),15),sc(c,9),sc(d,-1))]
 for j,t in enumerate(targets):assert coeff(ans,j)==lift(t,j),(typ,j,coeff(ans,j),lift(t,j))
 results[typ]={str(j):{','.join(map(str,k[1:])):str(v) for k,v in sorted(coeff(ans,j).items())} for j in range(4)}
# Leading cumulants kappa_r~(r!/12)*t^(-r-1)*L^3.
V=F(1,6);k3=F(1,2);k4=F(2)
assert k4/(8*V**2)-5*k3**2/(24*V**3)==F(-9,4)
receipt={'status':'PASS','scope':'Finite exact algebra and coefficients; analytic estimates are separately proved.','three_way_coefficient_identities':N+1,'strict_monotonicity_checks':N-1,'Euler_factor_identities':30,'formal_coefficients':results,'leading_E1_coefficient':'-9/4','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ar.output_dir/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
