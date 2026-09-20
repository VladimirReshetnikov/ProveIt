#!/usr/bin/env python3
"""Reproduce the resultant certificate for double chains. Requires sympy."""
from pathlib import Path
import sympy as sp

s, t, a, H, z = sp.symbols('s t a H z')
f = t*s**2*a**2 + ((1+t)*s-1)*a + 1
# Substitute b=H/a into the quadratic for F_1(-s,t), then multiply by a^2.
g = t*s**2*H**2 + (-(1+t)*s-1)*H*a + a**2
resultant = sp.Poly(sp.resultant(f, g, a), s)
assert all(exponents[0] % 2 == 0 for exponents, _ in resultant.terms())
P = sp.expand(sum(coefficient*z**(exponents[0]//2)
                  for exponents, coefficient in resultant.terms()))
expected = (t**4*z**4*H**4
            + t**2*z**2*((1+t)**2*z-1)*H**3
            + 2*t*z*(1+(t**2+t+1)*z)*H**2
            + ((1+t)**2*z-1)*H + 1)
assert sp.expand(P-expected) == 0
assert P.subs(z, 0) == 1-H
assert sp.diff(P, H).subs({z: 0, H: 1}) == -1
out = Path(__file__).resolve().parents[1]/'results'/'quartic_certificate.txt'
out.write_text('Resultant in a of:\n'+str(f)+'\nand\n'+str(g)
               +'\nwith s^2=z equals:\n'+str(sp.factor(P))
               +'\n\nLaTeX:\n'+sp.latex(expected)
               +'\n\nAt z=0: 1-H; derivative in H at (z,H)=(0,1): -1.\n')
print('PASS: resultant identity and unique formal branch verified.')
print(expected)
