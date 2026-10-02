#!/usr/bin/env python3
"""Assertion-based exact ballot checks. The infinite asymptotic proof is separate."""
import sys
if not __debug__: raise SystemExit('Assertions must be enabled; do not use -O.')
from pathlib import Path
import argparse, contextlib, io, json, hashlib, runpy
from fractions import Fraction
from itertools import product
from math import factorial
import sympy as S
pa=argparse.ArgumentParser();pa.add_argument('--source-dir',type=Path,default=Path('/workspace/shared/oeis-asymptotic-screening-20261001'));pa.add_argument('--output-dir',type=Path,default=Path(__file__).parent);ar=pa.parse_args();ar.output_dir.mkdir(parents=True,exist_ok=True)
records=[];pins={}
for name,q in [('ballot_four_correction.py',4),('ballot_first_correction.py',5)]:
 p=ar.source_dir/name;pins[name]=hashlib.sha256(p.read_bytes()).hexdigest()
 buf=io.StringIO()
 with contextlib.redirect_stdout(buf):g=runpy.run_path(str(p))
 if q==4:
  r=g['t'];uni=-6*r**3/S.Integer(25)+3*r**2/S.Integer(10)+3*r/S.Integer(5)-S.Rational(47,50)
  sad=-r**3/2+4*r*r/S.Integer(5)+7*r/S.Integer(10)-S.Rational(2,5)
  full=-37*r**3/S.Integer(200)+11*r*r/S.Integer(40)+13*r/S.Integer(40)-S.Rational(259,400)
  assert g['red'](g['univ']-uni)==0 and g['red'](g['amp']-sad)==0 and g['red'](g['full']-full)==0
 else:
  uni=-S.Rational(7,4)+3*S.sqrt(5)/10;sad=-S.Rational(11,4)+S.sqrt(5);full=13*(S.sqrt(5)-5)/50
  assert S.simplify(g['univ']-uni)==0 and S.simplify(g['amp']-sad)==0 and S.simplify(g['full']-full)==0
 records.append({'q':q,'D_uni':str(uni),'D_sad':str(sad),'c1':str(full)})
# Derive the generic degree-six equation from the two quadratic factors.
A,B,C,D,Z,F=S.symbols('A B C D Z F')
v=-A*F;w=-1/(Z*F)
small=S.cancel((-B/Z+(D/Z)*v)/(w-v));large=-D/Z-small
relation=S.factor((v+w+small*large)-(C-1)/Z)
Q=1+(C-1)*F+(B*D-A*Z)*F**2+(A*D**2+B**2*Z+2*A*Z*(1-C))*F**3+(A*B*D*Z-A**2*Z**2)*F**4+A**2*Z**2*(C-1)*F**5+A**3*Z**3*F**6
assert S.factor(relation+Q/(F*Z*(A*Z*F**2-1)**2))==0
# Exact saddle covariance determinants and lattice constants for many fixed q.
dets={}
for q in range(2,17):
 steps=[i-(q+1)//2 for i in range(1,q+1)] if q%2 else [2*i-q-1 for i in range(1,q+1)]
 h=q-2;sig=S.Rational(sum(s*s for s in steps),q);delta=1 if q%2 else 2
 H=S.Matrix(h,h,lambda i,j:S.Rational(int(i==j),q)-S.Rational(1,q*q)-S.Rational(steps[i]*steps[j],q*q)/sig)
 det=H.det() if h else S.Integer(1)
 assert det==S.Rational(delta**2,q**q)/sig
 assert all(H[:k,:k].det()>0 for k in range(1,h+1))
 dets[str(q)]=str(det)
# Independently compare word DP with the formal bridge-exponential recurrence.
reports=[]
for steps in [(-3,-1,1,3),(-2,-1,0,1,2)]:
 q=len(steps);M=3;zero=(0,)*q;states=sorted(product(range(M+1),repeat=q),key=sum);walk={zero:1}
 for v0 in states[1:]:
  if sum(x*s for x,s in zip(v0,steps))<0:walk[v0]=0;continue
  value=0
  for i,x in enumerate(v0):
   if x:
    prev=list(v0);prev[i]-=1;value+=walk[tuple(prev)]
  walk[v0]=value
 balanced=[v0 for v0 in states if sum(x*s for x,s in zip(v0,steps))==0]
 bridge={v0:factorial(sum(v0))//__import__('functools').reduce(lambda a,b:a*factorial(b),v0,1) for v0 in balanced if v0!=zero}
 exp={zero:Fraction(1)}
 for v0 in balanced[1:]:
  value=0
  for u,b in bridge.items():
   if all(x<=y for x,y in zip(u,v0)):
    diff=tuple(y-x for x,y in zip(u,v0));value+=b*exp[diff]
  exp[v0]=value/sum(v0)
  assert exp[v0].denominator==1 and exp[v0]==walk[v0]
 diag=[walk[(n,)*q] for n in range(M+1)]
 assert diag==([1,7,403,40350] if q==4 else [1,35,18720,19369350])
 reports.append({'q':q,'word_states':len(states),'balanced_coefficient_identities':len(balanced),'diagonal':diag})
# Formal verification of the sign in D_uni using generic Puiseux coefficients.
a,b,c=S.symbols('a b c');e1=S.Rational(3,8)-3*c/(2*a)
b1=-S.Rational(1,8)+(a/2-3*(c-a*b+a**3/3)/2)/a
assert S.expand(e1-b1+3*b/2-a*a/2)==0
receipt={'status':'PASS','scope':'Exact corroboration; ordinary asymptotic proof and source audit are separate.','correction_formula_identities':records,'generic_degree_six_identity':True,'covariance_determinants':dets,'bridge_exponential_identity':reports,'generic_univariate_correction_identity':True,'source_sha256':pins,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ar.output_dir/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
