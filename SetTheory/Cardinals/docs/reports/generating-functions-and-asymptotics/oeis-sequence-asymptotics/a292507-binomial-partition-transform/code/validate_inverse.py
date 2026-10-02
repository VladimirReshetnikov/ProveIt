#!/usr/bin/env python3
"""Independently verify the first two displayed inverse polynomials."""
import json
from pathlib import Path
import sympy as s
from reproduce import inverse_polynomials
L,a,b,g,l,c1,c2=s.symbols('L alpha beta gamma logC c1 c2')
u=inverse_polynomials(2,2)
v1=-g*b/(2*a*a)*L-b**3/(8*a**3)+b*(l-2*g)/(2*a*a)-c1/a
v2=g*g/(a*a)*L+(c1*c1/2-c2)/a-g*l/(a*a)+b*b*g/(2*a**3)
assert s.simplify(u[0]-v1)==0
assert s.simplify(u[1]-v2)==0
result={'U1':str(u[0]),'U2':str(u[1]),'verified_against_displayed_formulas':True}
Path('inverse_verification.json').write_text(json.dumps(result,indent=2)+'\n')
print('Both displayed inverse polynomials agree symbolically with the general recursion.')
