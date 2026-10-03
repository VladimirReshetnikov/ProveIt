#!/usr/bin/env python3
"""Independent integer falling-product replay; no logarithmic series recurrence."""
from fractions import Fraction as Q
from math import factorial,comb
from pathlib import Path
import json

def ensure(test,info):
 if not test:raise RuntimeError(info)
def bcoef(M,Y):
 f=[1]+[0]*Y
 for h in range(M):
  a=Y-h
  for j in range(Y,0,-1):f[j]=a*f[j]+f[j-1]
  f[0]*=a
 return f[Y]
def T(r,Y):return Q(bcoef(r+Y,Y)*factorial(Y),factorial(r+Y))
def modq(x,p,mod=None):
 mod=mod or p
 ensure(x.denominator%p!=0,('nonintegral',p))
 return x.numerator*pow(x.denominator,-1,mod)%mod

def stirling_row(m):
 f=[1]
 for k in range(m):
  g=[0]*(len(f)+1)
  for i,c in enumerate(f):g[i]+=k*c;g[i+1]+=c
  f=g
 return f
primes=[3,5,7,11,13,17,19,23];residue=triangle=derivative=shift=0
for p in primes:
 for m in range(2,min(8,p-1)+1):
  c=stirling_row(m);r=m*(p-1)
  for j in range(1,m):
   M=r+j;b=bcoef(M,j);val=Q(b*factorial(j),factorial(M))
   expected=-Q(factorial(j)**2*factorial(m-j-1)*c[j],factorial(m)*factorial(m-1))
   ensure(modq(p**(j-1)*val-expected,p)==0,('Stirling residue',p,m,j));residue+=1
   ensure(b%p**(m-j)==0,('integer division',p,m,j))
   ensure(modq(Q(b,p**(m-j))-Q((-1)**j*factorial(j)*c[j],factorial(m)),p)==0,('triangle',p,m,j));triangle+=1
   # A finite p-step differentiates any p-integral polynomial modulo p.
   gj=p**m*val;der=Q(p**m*T(r,j+p)-gj,p)
   expected_d=Q(factorial(j)*(-1)**(m-j-1)*factorial(m-j-1),factorial(m))
   ensure(modq(der-expected_d,p)==0,('derivative',p,m,j));derivative+=1
   e=m-j+1;actual_shift=-modq(gj/Q(p**e),p)*pow(modq(der,p),-1,p)%p
   expected_shift=modq(Q((-1)**(m-j-1)*factorial(j)*c[j],factorial(m-1)),p)
   ensure(actual_shift==expected_shift,('shift',p,m,j));shift+=1
# The distinct prime-square family, checked from positive representative values.
square=[]
for p in [3,5,7,11,13,17,19]:
 r=p*p-1;small=0
 for a in range(1,p):
  J=Q(p**(p+2)*T(r,a),a)
  ensure(modq(J,p,p**3)==0,('nonzero residue representative',p,a));small+=1
  d=Q(Q(p**(p+2)*T(r,a+p),a+p)-J,p)
  ensure(modq(d,p)==1,('prime-square derivative',p,a))
 Jp=Q(p**(p+2)*T(r,p),p)
 ensure(modq(Jp,p,p**3)==p*p,('zero residue branch',p))
 d=Q(Q(p**(p+2)*T(r,2*p),2*p)-Jp,p)
 ensure(modq(d,p)==1,('zero residue derivative',p))
 square.append(dict(p=p,nonzero_classes=small,zero_class_residue=(p-p*p)%(p**3)))
# Exact check of the sole candidate on offset (p-1)^2, not p^2-1.
candidates=[]
for p in [3,5,7,11,13,17,19]:
 r=(p-1)**2;Y=p*p+p-2;v=bcoef(r+Y,Y)
 ensure(v!=0,('square-offset candidate unexpectedly zero',p))
 candidates.append(dict(p=p,offset=r,Y=Y,integer_coefficient_nonzero=True))
out=dict(method='Truncated products of consecutive integer-root factors; polynomial residues use a finite p-step derivative',primes=primes,maximum_multiplier=8,Stirling_residue_checks=residue,scaled_triangle_checks=triangle,finite_difference_derivative_checks=derivative,first_displacement_checks=shift,prime_square_branch_checks=square,distinct_square_offset_candidates=candidates,all_pass=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
