#!/usr/bin/env python3
"""Exact symbolic checks of the closed first-order formulas and phase transform."""
from sympy import symbols, simplify, expand, series, Rational

v, r, t, delta, z, eta, d0, B0 = symbols('v r t delta z eta d0 B0', nonzero=True)
B = (2-r)/v
h1 = (1/v-r)/2
h2 = (-1/v**2+r*(1+r))/2
F3 = (3*r-6)/v**2+r*(1+r)/v
F4 = (24-12*r)/v**3-4*r*(1+r)/v**2-r*(1+r)*(1+2*r)/v
c1 = -v*(2*r+1)/24
eta_expr = -h1/B+F3/(2*B**2)
d0_expr = c1-(h2+h1**2)/(2*B)+h1*F3/(2*B**2)+F4/(8*B**2)-5*F3**2/(24*B**3)
assert simplify(eta_expr-(3*r*v+4*r-8)/(2*(r-2)**2)) == 0
num = 13*r**2*v**2+36*r**2*v+12*r**2+17*r*v**2-72*r*v-48*r+4*v**2+48
assert simplify(d0_expr-num/(12*v*(r-2)**3)) == 0
P1 = d0+eta*t-t**2/(2*B0)
Q1 = 2*delta+v*delta**2+P1.subs(t,2*delta)
assert expand(Q1-(d0+(2+2*eta)*delta+(v-2/B0)*delta**2)) == 0
# First two orders of the exact phase-coefficient transform, generic P2.
p20,p21,p22,p23,p24 = symbols('p20:25')
P2 = p20+p21*t+p22*t**2+p23*t**3+p24*t**4
T = 2*delta+delta**2*z/(1-delta*z)
a = v*delta**2*z/(1-delta*z)
prefactor = (1+2*delta*z+3*delta**2*z**2)*(1+a+a**2/2)
expr = prefactor*(1+P1.subs(t,T)*z/(1-delta*z)+P2.subs(t,T)*z**2/(1-delta*z)**2)
q2 = expand(series(expr,z,0,3).removeO()).coeff(z,2)
q2_expected = (P2.subs(t,2*delta)+delta**2*P1.diff(t).subs(t,2*delta)
    +(3*delta+v*delta**2)*P1.subs(t,2*delta)
    +3*delta**2+3*v*delta**3+v**2*delta**4/2)
assert simplify(q2-q2_expected)==0
print('PASS: exact rational d0 and eta identities; exact Q1 and Q2 transforms.')
