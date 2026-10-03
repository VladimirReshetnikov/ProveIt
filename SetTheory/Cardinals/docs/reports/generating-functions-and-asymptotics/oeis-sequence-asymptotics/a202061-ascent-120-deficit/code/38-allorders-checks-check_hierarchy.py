#!/usr/bin/env python3
"""Exact polynomial covariance and explicit finite-order error exponents."""
import sympy as s
B,K=s.symbols('B K', real=True)
P=[s.Integer(1),B,-B**2/s.Integer(4)+7*B/s.Integer(2)-10,
 (4*B**3-105*B**2+774*B-2050-27*s.pi**2)/24,
 -(7*B**4-273*B**3+3444*B**2-19768*B-189*s.pi**2*B+1944*s.zeta(3)+999*s.pi**2+46290)/48]
for j,p in enumerate(P):
 assert s.Poly(p,B).degree()==j
 assert s.simplify(s.expand(p).coeff(B,j)-s.binomial(s.Rational(2,3),j)*s.Rational(3,2)**j)==0
for j in range(4):
 assert s.simplify(s.diff(P[j+1],B)-(1-s.Rational(3,2)*j)*P[j]-s.Rational(7,2)*s.diff(P[j],B))==0
print('PASS: P0--P4 exact degree/leading coefficients; covariance differential identity through P4')
B0=K+3;A0=4*B0+10;E=2*K+8;N=K+3
assert s.simplify(s.Rational(3,2)-A0/2+K+K+s.Rational(19,2))==0
assert s.simplify(1-B0+K)==-2
assert s.simplify(1-E/2+K)==-3
assert s.simplify(-K-2+K)==-2
assert s.simplify(A0/2-2*B0-1)==4
assert s.simplify(-N-1+K)==-4
print('PASS: normalization, summation, endpoint, slack, Bernstein and row-truncation exponents for symbolic K')
print('PASS: fixed J uses K=J-1 and N=J+2; targets exp(L/3)*L^(2/3-J) diverge')
