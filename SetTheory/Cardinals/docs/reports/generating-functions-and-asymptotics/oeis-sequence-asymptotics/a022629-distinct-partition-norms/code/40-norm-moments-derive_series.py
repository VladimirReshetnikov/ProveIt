#!/usr/bin/env python3
"""Generate the logarithmic expansion through order eight, using exact SymPy algebra.
The truncation order is deliberately fixed; increase all derivative and series
orders together when extending the computation. The analytic justification is
in Sections 7 and 8 of article.pdf, not in this finite symbolic check.
"""
from pathlib import Path
import sympy as S
z,u,s,c=S.symbols('z u s c')
N=8

def tr(e,n=N+2):
    return S.series(e,z,0,n).removeO().expand()
# U derivatives at zero of inverse s(u-1)-log u
expr=u
U={}
for k in range(1,8):
    expr=S.factor(S.diff(expr,u)/(s-1/u))
    if k%2:
        U[k]=S.factor(expr.subs(u,1))
        print('U',k, U[k],flush=True)
d=0
for j in range(1,5):
    const=S.simplify(2*(1-S.Rational(2)**(1-2*j))*S.zeta(2*j)/(S.pi**2/6)**j)
    d += const*c**j*U[2*j-1]
dz=tr(d.subs(s,1/z))
print('d=',S.collect(dz,z),flush=True)
qz=tr(1+2*z/(1-z)*(dz-z*z*S.diff(dz,z)))
print('q=',S.collect(qz,z),flush=True)
delta=0
for i in range(4):
    w=tr(z/(1+z*delta))
    qs=tr(qz.subs(z,w))
    delta=tr(-S.log(qs)/2)
    print('iter',i,flush=True)
w=tr(z/(1+z*delta))
qs=tr(qz.subs(z,w))
ds=tr(dz.subs(z,w))
h=tr(((1/z+delta)*(qs+1)/2 -1+ds)*tr(qs**(-S.Rational(1,2))),N+1)
print('delta=',S.collect(delta,z))
print('H=',S.collect(h,z))
for k in range(1,8):
 print(k,S.factor(h.coeff(z,k)),flush=True)
expected = [c,c,c-c**2/2,c+S.Rational(9,10)*c**2,
 c+S.Rational(41,5)*c**2+c**3/2,
 c+27*c**2+S.Rational(1973,210)*c**3,
 c+S.Rational(129,2)*c**2+S.Rational(8109,70)*c**3-S.Rational(5,8)*c**4]
for j, value in enumerate(expected, 1):
    assert S.expand(h.coeff(z,j)-value)==0
out=Path(__file__).resolve().parent/'data'
out.mkdir(exist_ok=True)
(out/'formal_coefficients.txt').write_text(str(S.collect(h,z))+'\n')
print('All seven printed polynomials verified exactly.')
