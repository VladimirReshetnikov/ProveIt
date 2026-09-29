#!/usr/bin/env python3
"""Optional symbolic identities; requires SymPy, not a formal verification."""
from __future__ import annotations
import sympy as s

checks=0

def zero(expression: s.Expr, label: str) -> None:
    global checks
    result=s.simplify(s.expand(expression))
    if result!=0:
        raise AssertionError(f"{label}: {result}")
    checks+=1

a,t,u,y,q,L,C,E=s.symbols('a t u y q L C E', real=True)
F=a*a*(s.cosh(2*t)+1)-(2-a*a)*(s.cosh(2*a*t)-1)
series=s.series(F,t,0,6).removeO()
zero(series-(2*a*a-2*a*a*(1-a*a)*t*t+s.Rational(2,3)*a*a*(1-a*a)**2*t**4),
     'hyperbolic power-series coefficients')
zero(1-u+u*u/3-((u-s.Rational(3,2))**2/3+s.Rational(1,4)),
     'positive quadratic decomposition')
# Special-order maxima after exact substitutions.
zero(s.Rational(1,8)-(y-1)/(2*y*y)-(y-2)**2/(8*y*y), 'half-order upper bound')
zero(s.Rational(1,2)-2*u/(1+4*u*u)-(2*u-1)**2/(2*(1+4*u*u)),
     'third-order upper bound')
# Full determinant identity, small symbolic dimensions.
for n in range(1,5):
    b=s.symbols('b0:'+str(n))
    d=s.symbols('d0:'+str(n))
    vector=s.Matrix(b)
    matrix=s.diag(*d)-vector*vector.T
    expected=s.prod(d)-sum(b[i]**2*s.prod(d[j] for j in range(n) if j!=i)
                           for i in range(n))
    zero(matrix.det(method='domain-ge')-expected,f'rank-one determinant n={n}')
# Exact quartic bending; only a short local series is required.
z=s.symbols('z')
g=2*((1+s.sqrt(1+8*s.sqrt(3)*z-16*z*z)/2)**5-1)
expansion=s.series(g,z,0,5).removeO()
zero(expansion-(s.Rational(211,16)+s.Rational(405,4)*s.sqrt(3)*z-6480*z**4),
     'half-order Taylor coefficients through order four')
# Envelope derivative with beta and its derivative specified exactly.
beta=s.symbols('beta')
rho=q*beta/(1-q+beta)
derivative=s.diff(rho,q)+s.diff(rho,beta)*(-s.sqrt(3)*t/4)
zero(derivative.subs({q:s.Rational(1,2),beta:s.Rational(1,8)})-(9-4*s.sqrt(3)*t)/25,
     'half-order envelope derivative')
# The first terms of both endpoint expansions.
rsmall=q*(1-q*(L+1)+E*q*q)/(1-q+1-q*(L+1)+E*q*q)
zero(s.series(rsmall,q,0,3).removeO()-(q/2-q*q*L/4),'small-q expansion')
rnear=(1-a)*(C*a*a+E*a**4)/(a+C*a*a+E*a**4)
zero(s.series(rnear,a,0,3).removeO()-(C*a-C*(1+C)*a*a),'near-one expansion')
# The equality branch is essential at the two exact orders.
for m,k,n in [(1,2,10),(1,3,11)]:
    P=s.Poly(m*(1+y**(2*k-m))-(2*k-m)*(y**k+y**(k-m)),y)
    K=s.Poly((n*m-k)*y**m*(1-y**(k-m))**2-(k-m)*(1+y**k)**2,y)
    gcd=s.gcd(P,K)
    count=gcd.count_roots(0,1)
    if count!=1:
        raise AssertionError('exceptional equality root count')
    checks+=1
    print(f'q={m}/{k}: gcd(P,K)={gcd.as_expr()}, exactly one root in (0,1).')
print(f'PASS: {checks} symbolic identity/root-count checks; SymPy {s.__version__}.')
print('These checks do not constitute a proof-assistant verification.')
