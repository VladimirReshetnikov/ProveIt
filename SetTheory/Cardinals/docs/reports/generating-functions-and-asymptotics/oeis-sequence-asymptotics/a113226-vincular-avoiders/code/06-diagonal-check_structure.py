#!/usr/bin/env python3
"""Exact elimination checks for the differential algebraic equation."""
import json,pathlib
import sympy as s
u,v,w=s.symbols('u v w')
N=4*v-2*u+1;D=v+u+1
E=s.expand((4*w-2*v)*D-N*(w+v)-N*D)
claimed=3*(2*u+1)*w-10*v*v-(2*u+8)*v+2*u*u+u-1
if s.expand(E-claimed)!=0: raise RuntimeError('elimination failed')
A,A1,A2,A3=s.symbols('A A1 A2 A3')
poly=s.factor(claimed.subs({u:A1/A,v:A2/A-A1**2/A**2,
                           w:A3/A-3*A1*A2/A**2+2*A1**3/A**3})*A**4)
if s.denom(poly)!=1: raise RuntimeError('uncleared denominator')
out={'status':'pass','logarithmic_equation':str(claimed),
     'polynomial_equation':str(poly)}
pathlib.Path(__file__).with_name('structure_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
