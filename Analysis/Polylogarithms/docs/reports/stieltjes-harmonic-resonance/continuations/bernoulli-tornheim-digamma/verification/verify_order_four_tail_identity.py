#!/usr/bin/env python3
"""Exact finite algebra for the convergent (4,6) tail identity.

Absolute convergence and the finite-part passage are proved in
sections/03c_moment_rank_four.tex; this program verifies the coefficients.
"""
import sympy as sp

x=sp.symbols("x")
M=sp.Matrix([[0,sp.Rational(3,4),sp.Rational(1,4)],
             [sp.Rational(5,12),sp.Rational(2,3),-sp.Rational(1,12)],
             [1,-sp.Rational(3,8),sp.Rational(1,12)]])
row=sp.Matrix([[-7,45,66]])
assert row*M==sp.Matrix([[sp.Rational(339,4),0,0]])
S=512*(-7*x**7+45*x**9+66*x**11)
W=sp.expand(S.subs(x,x+sp.Rational(1,2))-S.subs(x,x-sp.Rational(1,2)))
assert W==67+15516*x**2+324320*x**4+1434496*x**6+1601280*x**8+371712*x**10
asymptotic=sp.expand(W*(x**-8/15-sp.Rational(7,60)*x**-10))
R=sum(term for term in sp.Add.make_args(asymptotic)
      if term.as_powers_dict().get(x,0)>=0)
assert R==(123904*x**2+316928)/5
assert -sp.Rational(339,8)*512==-21696
print("Exact extraction row, centered weight polynomial, subtraction, and right side: PASS")
