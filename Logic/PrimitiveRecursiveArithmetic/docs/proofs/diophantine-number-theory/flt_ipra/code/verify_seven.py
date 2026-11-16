#!/usr/bin/env python3
"""Exact polynomial checks for the exponent-seven argument.

Run: python verify_seven.py
Requires SymPy. These checks validate the displayed algebraic identities;
they are not a formal proof of FLT or of its interpretation in iPRA.
The variable d represents 2**a, so no symbolic exponent simplification is
needed. Rational coefficients are exact SymPy rationals.
"""

import sympy as S


def check(name, expression):
    residual = S.expand(expression)
    if residual != 0:
        raise AssertionError(f"{name}: nonzero residual {residual}")
    print(f"PASS {name}")


x, y, z = S.symbols("x y z")
s = x + y + z
u = x*x + y*y + z*z + x*y + x*z + y*z
v = (x+y)*(y+z)*(z+x)
t = u*u + x*y*z*s
check("seventh-power symmetric identity",
      s**7 - (x**7+y**7+z**7) - 7*v*t)

Q, R, d = S.symbols("Q R d")
quartic = Q**4 - 3*7**4*d**2*Q**2*R**2 + 16*7**7*d**4*R**4
C = Q**2 - S.Rational(3, 2)*7**4*d**2*R**2
check("first quartic square completion",
      quartic - C*C - S.Rational(1, 4)*7**7*d**4*R**4)

s, t = S.symbols("s t")
Qsq = (s**4 + S.Rational(3, 2)*7**4*d**2*s**2*t**2
       - S.Rational(1, 16)*7**7*d**4*t**4)
B = s**2 + S.Rational(3, 4)*7**4*d**2*t**2
check("row I second square completion",
      B**2 - Qsq - 4*7**7*d**4*t**4)

Qsq = (S.Rational(1, 16)*d**4*s**4
       + S.Rational(3, 2)*7**4*d**2*s**2*t**2 - 7**7*t**4)
E = S.Rational(1, 4)*d**2*s**2 + 3*7**4*t**2
check("row III correction square completion",
      E**2 - Qsq - 64*7**7*t**4)

u, v = S.symbols("u v")
T = 7**7*v**4 - 3*7**4*u**2*v**2 + 16*u**4
G = 32*u*u - 3*7**4*v*v
check("row III final correction square completion",
      64*T - G*G - 7**7*v**4)

h, q, r = S.symbols("h q r")
s = 7*h*q*q
v = 7**6*h**7
u = q*r
expression = S.cancel((u*u+s*(s*(s*s-u)-v))/q**2)
check("substitution of the seventh-power parameters",
      expression - (r*r + 49*h*h*q**3*(49*h*h*q**3-r) - 7**7*h**8))
H = 49*h*h*q**3
check("final FLT-to-quartic square completion",
      (r-H/2)**2 - (expression-S.Rational(3, 4)*H**2+7**7*h**8))

print("All seven polynomial identities passed exact symbolic expansion.")
