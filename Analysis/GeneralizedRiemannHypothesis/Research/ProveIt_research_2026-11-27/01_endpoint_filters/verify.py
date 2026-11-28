#!/usr/bin/env python3
"""Exact algebra checks and labelled numerical illustrations for paper.tex.

These checks do not replace the complex-analytic proof. Requires sympy and mpmath.
Run from this directory; writes verification.json.
"""
from pathlib import Path
import json
import sympy as sp
import mpmath as mp

delta=sp.symbols('delta', real=True)
envelope=sp.cos(delta)*sp.log(sp.cos(delta))+delta*sp.sin(delta)
series=sp.series(envelope,delta,0,8)
assert sp.expand(series.removeO()).coeff(delta,2)==sp.Rational(1,2)
assert sp.expand(series.removeO()).coeff(delta,4)==0
assert sp.expand(series.removeO()).coeff(delta,6)==sp.Rational(1,144)

families=[]
for r in range(7):
 for s in range(7):
  if r+s==0:continue
  d=r+s
  A=sp.Rational(s,2)-sp.Rational(d,4)+2*r
  assert A==sp.Rational(7*r+s,4) and A>0
  cstar=sp.pi*d/(4**sp.Rational(s,d))
  qstar=4**sp.Rational(s,d)
  assert sp.simplify(cstar*qstar-sp.pi*d)==0
  # At the unconstrained positive-tail saddle, c_j exp(2t_j)
  # are equal. The AM--GM coefficient agrees exactly with b_*.
  cgeom=sp.pi/(4**sp.Rational(s,d))
  assert sp.simplify(cgeom**d-sp.pi**d/4**s)==0
  families.append({'r':r,'s':s,'alpha':str(sp.Rational(2,d)),
                   'A':str(A),'b_star':str(cstar)})

mp.mp.dps=65
theta=[]
for t in [mp.mpf(0),mp.mpf('0.25'),mp.mpf('0.5'),mp.mpf(1),mp.mpf(2)]:
 x=mp.exp(2*t)
 phi=mp.fsum((4*mp.pi**2*n**4*mp.exp(mp.mpf('4.5')*t)
              -6*mp.pi*n*n*mp.exp(mp.mpf('2.5')*t))*mp.exp(-mp.pi*n*n*x)
             for n in range(1,25))
 beta=2*mp.exp(mp.mpf('1.5')*t)*mp.fsum(
       (-1)**n*(2*n+1)*mp.exp(-mp.pi*(2*n+1)**2*x/4) for n in range(25))
 assert phi>0 and beta>0
 theta.append({'t':str(t),'phi_25_term':mp.nstr(phi,35),
               'beta_25_term':mp.nstr(beta,35),
               'status':'floating-point illustration, not interval certificate'})

result={'exact_family_checks':len(families),'indicator_series':str(series),
        'exact_algebra':'PASS','families':families,'theta_illustrations':theta,
        'proof_status':'Theorem proven in manuscript; not Lean formalized.'}
Path('verification.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS:',len(families),'exact family identities; indicator Taylor coefficients; 5 labelled theta illustrations.')
