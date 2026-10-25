#!/usr/bin/env python3
"""Finite exact diagnostics for the reviewed unbounded lemmas, not proofs of them."""
from fractions import Fraction
from math import isqrt, gcd
from pathlib import Path
import json
OUT=Path(__file__).resolve().parent

def need(ok,m):
 if not ok:raise ValueError(m)
def val(n,p):
 n=abs(n);need(n!=0,'valuation zero')
 e=0
 while n%p==0:n//=p;e+=1
 return e

def pell(a,n):
 # Independent binary powering in Z[sqrt(a^2-1)].
 d=a*a-1;x,y=1,0;u,v=a,1
 while n:
  if n&1:x,y=x*u+d*y*v,x*v+y*u
  u,v=u*u+d*v*v,2*u*v;n//=2
 return x,y

counts={'adjacent_candidates':0,'rational_adjacent_roots':0,'descent_steps':0,'lifting_cases':0,'isometry_cases':0,'coprimality_signed_cases':0}
for q in range(2,181):
 for V in range(1,121):
  rat=Fraction(q*V*V-1,q-1);a,b=isqrt(rat.numerator),isqrt(rat.denominator);counts['adjacent_candidates']+=1
  if a*a!=rat.numerator or b*b!=rat.denominator:continue
  y=Fraction(a,b);counts['rational_adjacent_roots']+=1
  vv,yy=V,y
  while vv>1:
   vp=(2*q-1)*vv-2*(q-1)*yy;yp=(2*q-1)*yy-2*q*vv
   need(vp.denominator==1 and abs(vp)<vv and vp!=0,'strict descent')
   need(q*vp*vp-(q-1)*yp*yp==1 and yp.denominator==y.denominator,'norm/denominator')
   vv,yy=abs(vp),abs(yp);counts['descent_steps']+=1
  need(vv==1 and yy==1 and b==1,'terminal denominator')
for rho in range(2,41):
 primes=[p for p in range(2,rho+1) if rho%p==0 and all(p%d for d in range(2,isqrt(p)+1))]
 for inc in range(4,65,4):
  chi,psi=pell(rho,inc)
  for p in primes:
   need(psi%rho==0 and val(psi//rho,p)==val(inc,p),'second-coordinate lifting')
   target=2*(val(rho,p)+val(inc,p))-(1 if p==2 else 0)
   need(val(chi-1,p)==target,'first-coordinate lifting');counts['lifting_cases']+=1
   for nu in [1,3,5,7]:
    c0,_=pell(rho,nu);c1,_=pell(rho,nu+inc)
    need(c0%rho==c1%rho==0,'odd quotient')
    need(val((c1-c0)//rho,p)==val(inc,p),'quotient isometry');counts['isometry_cases']+=1
for A in list(range(-9,-1))+list(range(2,10)):
 for c in range(-3,4):
  for r in range(-3,4):
   for P in list(range(-9,0,2))+list(range(1,10,2)):
    for b in [-2,-1,0,1,2]:
     Delta=A*A-1;Dm=1+Delta*c*c;BP=Dm*P;U=A*r*c*c;F=1+Delta*U*U*BP;Q=Delta*Delta*U*U*BP;V=F*b-c;Da=(Q-1)*(Q*V*V-1)
     need(BP and F and Da,'unconditional nonzero')
     need(gcd(BP,F)==gcd(BP,Da)==gcd(F,Da)==1,'coprime product')
     need(F%4==1,'strong sign residue');counts['coprimality_signed_cases']+=1
result={'status':'PASS','optimized':not __debug__,'scope':'Exact finite diagnostic grids; unbounded proofs reviewed in REVIEW.md','counts':counts}
(OUT/('LEMMAS_OPTIMIZED.json' if not __debug__ else 'LEMMAS_NORMAL.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
