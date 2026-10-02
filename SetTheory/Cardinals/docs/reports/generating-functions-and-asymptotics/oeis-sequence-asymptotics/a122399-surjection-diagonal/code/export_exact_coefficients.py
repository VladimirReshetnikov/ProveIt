#!/usr/bin/env python3
"""Export rational expressions in exact phase coefficients; no floating point."""
from pathlib import Path
import sympy as s
P=Path(__file__).parent
x,y,B=s.symbols('x y B')
phase={}
for line in (P/'phase_coefficients.txt').read_text().splitlines():
    name,value=line.split(' = '); phase[int(name[2:])]=s.sympify(value)
assert all(not v.atoms(s.Float) for v in phase.values())
J=4
f={j:s.Symbol('f'+str(j)) for j in range(3,2*J+3)}
poly={(0,0):s.Integer(1)}
for k in range(3,2*J+3):
    weight=k-2; q={}
    for a in range(2*J//weight+1):
        e=f[k]**a/s.factorial(a)
        for (r,d),v in poly.items():
            if r+a*weight<=2*J:
                key=r+a*weight,d+a*k; q[key]=q.get(key,s.Integer(0))+v*e
    poly=q
raw=[]
for j in range(J+1):
    v=s.Integer(0)
    for a in range(2*j+1):
        for (r,d),q in poly.items():
            if r+a==2*j:
                k=d+a
                moment=(-1)**(k//2)*s.factorial(k)/(s.factorial(k//2)*2**(k//2)*B**(k//2))
                v+=(-1)**a*(a+1)*q*moment
    raw.append(s.expand(v))
c=[raw[0]]+[s.expand(raw[j]+raw[j-1]) for j in range(1,J+1)]
lines=['Exact coefficients; substitute B=2-y+x and the phase formulas below.','No floating-point constants occur.','']
for j,v in enumerate(c):
    assert not v.atoms(s.Float)
    lines.append(f'c_{j} = {v}')
lines+=['','Phase polynomials:']
lines += [f'f_{j} = {phase[j]}' for j in range(3,2*J+3)]
# Fully combine c1,c2 as rational functions in x,y for easy external audit.
lines+=['','Combined saddle-variable expressions:']
for j in [1,2]:
    v=s.factor(c[j].subs({f[k]:phase[k] for k in f}).subs(B,2-y+x))
    lines.append(f'c_{j}(x,y) = {v}')
(P/'exact_coefficients.txt').write_text('\n'.join(lines)+'\n')
print('PASS: all exact coefficient expressions are rational, with no Float atoms')
