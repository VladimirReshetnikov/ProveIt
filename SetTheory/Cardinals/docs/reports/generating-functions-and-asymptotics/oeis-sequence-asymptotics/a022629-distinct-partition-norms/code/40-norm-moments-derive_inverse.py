#!/usr/bin/env python3
"""Exact formal inversion of the entropy block through R_0^(-6)."""
from pathlib import Path
import sympy as S
z,c=S.symbols('z c')
N=8
P=[0,c,c,c-c*c/2,c+S.Rational(9,10)*c*c,c+S.Rational(41,5)*c*c+c**3/2,c+27*c*c+S.Rational(1973,210)*c**3,c+S.Rational(129,2)*c*c+S.Rational(8109,70)*c**3-S.Rational(5,8)*c**4]
def tr(e,n=N):return S.series(e,z,0,n).removeO().expand()
E=S.Integer(1)
for k in range(2,7):
    a=S.symbols('a')
    test=E+a*z**k
    logE=tr(S.log(test))
    ir=tr(z/(1+z*logE))
    residual=tr(test*(1/z+logE-1+sum(P[j]*tr(ir**j) for j in range(1,len(P))))-(1/z-1))
    sol=S.solve(residual.coeff(z,k-1),a)[0]
    E+=S.factor(sol)*z**k
    print('E',k,S.factor(sol),flush=True)
print('E=',S.collect(E,z))
print('E2=',S.collect(tr(E**2,7),z))

expected2 = (1-2*c*z**2-2*c*z**3+(4*c**2-2*c)*z**4
 +(S.Rational(6,5)*c**2-2*c)*z**5
 +(-8*c**3-S.Rational(77,5)*c**2-2*c)*z**6)
assert S.expand(tr(E**2,7)-expected2)==0
out=Path(__file__).resolve().parent/'data'
out.mkdir(exist_ok=True)
(out/'inverse_coefficients.txt').write_text('E = '+str(S.collect(E,z))+'\nE^2 = '+str(S.collect(tr(E**2,7),z))+'\n')
print('Printed inverse coefficients verified exactly.')
