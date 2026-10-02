#!/usr/bin/env python3
"""Regression tests for the portable exact residual generator."""
import sympy as s
from derive_residual import *

_,R=residual_coefficients(2,[])
assert R[1]==0
assert cancel(solve_rational_ode(R[2],1,3,4,2)-p1)==0
print('Reconstruct p1: PASS')
_,R=residual_coefficients(3,[p1])
assert R[1:3]==[0,0]
assert cancel(solve_rational_ode(R[3],2,6,8,2)-p2)==0
print('Reconstruct p2: PASS')
q=s.Function('q')(w)
_,Q=residual_coefficients(3,[p1,q])
assert cancel(Q[3]-R[3]+w*s.diff(q,w)-2*(w+1)*q)==0
print('Generic smooth coefficient and triangular ODE identity: PASS')
for r in range(1,7):
    for kval in range(0,8):
        direct=-s.Rational(kval**r,r)+s.Rational((-1)**(r+1),r)*sum(s.Integer(i)**r for i in range(kval))
        assert s.expand(log_product_coefficient(r).subs(k,kval)-direct)==0
print('Faulhaber logarithmic coefficients through order 6: PASS')
_,R=residual_coefficients(4,[p1,p2])
p3=solve_rational_ode(R[4],3,9,13,2)
_,R=residual_coefficients(5,[p1,p2,p3])
assert R[1:5]==[0,0,0,0] and R[5] != 0
print('Third coefficient cancels exactly through order 4; order 5 is computed: PASS')
