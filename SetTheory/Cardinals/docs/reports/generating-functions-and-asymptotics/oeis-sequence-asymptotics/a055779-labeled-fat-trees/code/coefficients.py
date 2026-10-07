#!/usr/bin/env python3
"""Report203 coefficient data, adapted from the report producer's generator.

This program writes JSON to stdout; it never overwrites the expected fixture.
The separate symbolic_checks.py derives these identities by fixed-M
differentiation and exponential recurrence, rather than importing this code.
"""
import sys
sys.dont_write_bytecode = True
import json
import sympy as s

if s.__version__ != '1.14.0':
    raise RuntimeError('Use pinned SymPy 1.14.0 for this reproducibility fixture')

r = s.symbols('r')
P = s.Integer(1)
kappa = []
for j in range(9):
    kappa.append(P/(1+r))
    P = s.expand((1+r)*P+r*s.diff(P,r))
b = kappa[2]
k3,k4,k5,k6 = kappa[3:7]
s1 = k4/(8*b**2)-5*k3**2/(24*b**3)
s2 = (-k6/(48*b**3)+7*k3*k5/(48*b**4)+35*k4**2/(384*b**4)
      -35*k3**2*k4/(64*b**5)+385*k3**4/(1152*b**6))
c1 = s.factor(s.Rational(1,12)+s1)
c2 = s.factor(s.Rational(1,288)+s1/12+s2)
result = {'r':str(r), 'kappas':[str(s.factor(x)) for x in kappa],
          'c1':str(c1),'c2':str(c2),'d2':str(s.factor(c2-c1*c1/2))}
print(json.dumps(result,sort_keys=True,indent=2))
