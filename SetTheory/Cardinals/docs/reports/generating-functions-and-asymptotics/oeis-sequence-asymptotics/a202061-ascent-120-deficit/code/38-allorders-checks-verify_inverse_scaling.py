#!/usr/bin/env python3
import sympy as s
x,B,q=s.symbols('x B q')
P=lambda b:-b*b/4+s.Rational(7,2)*b-10
shift=B+s.Rational(7,3)*s.log(1-q*x)
expr=(1-q*x)**s.Rational(2,3)*(1+x*shift/(1-q*x)
                  +x*x*P(shift)/(1-q*x)**2)
got=s.series(expr,x,0,3).removeO().expand()
want=1+(B-2*q/3)*x+P(B-2*q/3)*x*x
assert s.simplify(got-want)==0
print('PASS: inverse fourth-scale shift, including the F prefactor')
polys=[s.Integer(1),B,P(B),
 (4*B**3-105*B**2+774*B-2050-27*s.pi**2)/24,
 -(7*B**4-273*B**3+3444*B**2-19768*B-189*s.pi**2*B
    +1944*s.zeta(3)+999*s.pi**2+46290)/48]
for j in range(len(polys)-1):
 assert s.simplify(s.diff(polys[j+1],B)
        -(1-s.Rational(3,2)*j)*polys[j]
        -s.Rational(7,2)*s.diff(polys[j],B))==0
 print(f'PASS: derivative covariance recurrence from P{j} to P{j+1}')
print('This check does not independently verify the integration constants in P3/P4.')
