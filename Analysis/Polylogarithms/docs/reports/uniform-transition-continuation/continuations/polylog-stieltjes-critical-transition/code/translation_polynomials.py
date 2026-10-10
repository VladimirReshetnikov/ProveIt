#!/usr/bin/env python3
"""Exact cusp polynomials from the proved two-variable gamma kernel."""
import json
from pathlib import Path
import sympy as S

x,y,L=S.symbols('x y L')
degree=6
u=x+y
v=x-y
def trunc(p):
    return S.Add(*(c*x**a*y**b for (a,b),c in S.Poly(S.expand(p),x,y).terms()
                   if a+b<=degree))
logR=sum(u**k/S.Integer(k) for k in range(1,degree+1))
logR+=sum(S.zeta(k)*(x**k+y**k-u**k)/k for k in range(2,degree+1))
logR+=sum((1-S.Rational(1,2)**(2*m))*S.zeta(2*m)
          *(u**(2*m)-v**(2*m))/m for m in range(1,degree//2+1))
logR=trunc(logR)
exponent=logR+u*L
term=S.Integer(1)
result=term
for k in range(1,degree+1):
    term=trunc(term*exponent/k)
    result=trunc(result+term)
poly=S.Poly(result,x,y)
records=[]
for r,s in [(0,0),(0,1),(1,1),(1,2),(2,2),(1,3),(2,3),(3,3)]:
    p=S.expand(S.factorial(r)*S.factorial(s)*poly.coeff_monomial(x**r*y**s))
    assert S.Poly(p,L).LC()==1
    assert S.degree(p,L)==r+s
    if r+s:
        assert S.Poly(p,L).coeff_monomial(L**(r+s-1))==r+s
    records.append(dict(r=r,s=s,expression=str(p),latex=S.latex(p)))
assert S.simplify(poly.coeff_monomial(x*y)
                 -(L**2+2*L+2+S.pi**2/3))==0
dest=Path(__file__).resolve().parents[1]/'verification'
dest.mkdir(exist_ok=True)
(dest/'translation_polynomials.json').write_text(json.dumps(records,indent=2)+'\n')
(dest/'translation_polynomials.tex').write_text('\n'.join(
    r'\[P_{%d,%d}(L)=%s.\]'%(a['r'],a['s'],a['latex']) for a in records)+'\n')
for item in records:
    if item['r']+item['s']<=4:
        print('P_%d%d ='%(item['r'],item['s']),item['expression'])
print('Exact polynomial checks passed for all listed pairs.')
