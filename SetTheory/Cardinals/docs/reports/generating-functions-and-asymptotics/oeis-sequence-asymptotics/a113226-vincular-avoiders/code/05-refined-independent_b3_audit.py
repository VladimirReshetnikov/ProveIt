#!/usr/bin/env python3
"""Independent hand expansion of the third marking-saddle correction.

This does not import refined_coefficients or its exponential recursion.
With h=n^(-1/6), the exponent through h^6 has the four nonzero
coefficients P1, P3, P4, P6 below. Enumerating partitions of 6 gives
E6; the coefficient amplitude supplies A3, A2*E2, A1*E4 and A1'*iX*P1.
"""
import json
from pathlib import Path
import sympy as s

X,V=s.symbols('X V',positive=True)
C1,C2,D1,D2,F3,F4,A1,A2,A3,A1p=s.symbols('C1 C2 D1 D2 F3 F4 A1_0 A2_0 A3_0 A1_1')
P1=3*s.I*C1*X
P3=s.I*D1*X-s.I*F3*X**3/6
P4=-3*C2*X**2/2
P6=F4*X**4/24-D2*X**2/2
E2=P1**2/2
E4=P4+P1*P3+P1**4/24
E6=P6+P3**2/2+P1**2*P4/2+P1**3*P3/6+P1**6/720
poly=s.Poly(s.expand(E6+A1*E4+A2*E2+s.I*A1p*X*P1+A3),X)
b3=s.factor(sum(coef*(s.factorial2(k-1) if k else 1)/V**(k//2)
                for (k,),coef in poly.terms() if not k%2))
local={str(x):x for x in [V,C1,C2,D1,D2,F3,F4,A1,A2,A3,A1p]}
record=json.loads(Path(__file__).with_name('refined_coefficients.json').read_text())
recorded=s.sympify(record['second_saddle'][3],locals=local)
assert s.simplify(b3-recorded)==0
print(json.dumps({'b3':str(b3),'third_correction_verified':True,
                  'method':'Manual degree-six exponential partitions; no coefficient-generator import'},indent=2))
