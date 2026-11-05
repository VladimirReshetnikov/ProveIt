#!/usr/bin/env python3
"""Independent arithmetic controls for the stated cube-free scale deduction."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('requires python3 -I -S -B')
def fac(n):
 out={}; d=2
 while d*d<=n:
  while n%d==0: out[d]=out.get(d,0)+1;n//=d
  d+=1
 if n>1: out[n]=out.get(n,0)+1
 return out
checks=0
for beta in range(2,70):
 for J in range(1,beta+2):
  q=beta*J+1
  for s in range(1,18):
   fs=fac(s)
   if any(e>=3 for e in fs.values()): continue
   Y=q**3*s
   for Jp in range(1,J+1):
    qp=beta*Jp+1
    if Y%(qp**3): continue
    for prime,exp in fac(qp).items():
     if 3*exp>3*fac(q).get(prime,0)+fs.get(prime,0): raise ValueError('valuation')
     if exp>fac(q).get(prime,0): raise ValueError('cube-free divisibility')
    if q%qp or qp!=q: raise ValueError(('rigidity',beta,J,s,Jp))
    checks+=1
# The J-bound is sharp as an arithmetic inequality, even for s=1.
for beta in range(2,100):
 q=beta*(beta+2)+1; qp=beta+1
 if q!=qp*qp or q**3!=qp**3*(qp**3) or q==qp: raise ValueError('J-bound example')
# The first positive exponent is odd, beta ≡1 mod 3.
if (pow(2,590069,3)-1)%3!=1: raise ValueError('fixed beta mod 3')
r=Path(__file__).resolve().parents[2]; p=r/'research/p64-qcube72-preserve-Y-normalization-obstruction'
pins={'README.md':'656b2d4103ea05a1811e611f857ff6029cb2cf94bac7a450d627ac8591450739','check.py':'f028a28b63bcbca614d730fe46b30a44dc29f5cf7bfafa6fb5af6da5ee059e09','result.json':'e41d17b44f86a6549a248f71b0dbab8e3c118650db26f0b54253801fce18df25'}
for name,want in pins.items():
 if hashlib.sha256((p/name).read_bytes()).hexdigest()!=want: raise ValueError(('pin',name))
print(json.dumps({'status':'PASS_INDEPENDENT_CONTROLS','positive_factorization_cases':checks,'sharp_J_bound_examples':98,'fixed_beta_mod_3':1,'pins':pins,'scope':'Finite arithmetic controls; universal statement established separately; no Lean replay or graph-zero assertion.'},sort_keys=True,indent=2))
