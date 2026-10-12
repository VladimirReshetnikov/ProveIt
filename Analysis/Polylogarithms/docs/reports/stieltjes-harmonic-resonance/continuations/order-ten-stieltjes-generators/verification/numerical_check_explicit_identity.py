#!/usr/bin/env python3
"""High-precision diagnostic; not used as a proof gate."""
from __future__ import annotations
import json
from fractions import Fraction
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
obj = json.loads((HERE / "explicit_10_16_zeta2.json").read_text())
D = int(obj["polynomial_denominator"])
P = [Fraction(int(n), D) for n in obj["polynomial_numerators"]]
Q = {int(e): Fraction(v["numerator"], v["denominator"]) for e, v in obj["subtraction"].items()}

mp.mp.dps = 90

def mpf(q: Fraction) -> mp.mpf:
    return mp.mpf(q.numerator) / q.denominator

def peval(x: mp.mpf) -> mp.mpf:
    y = x*x
    value = mp.mpf('0')
    for c in reversed(P):
        value = value*y + mpf(c)
    return value

def qeval(x: mp.mpf) -> mp.mpf:
    return mp.fsum(mpf(c)*x**e for e,c in Q.items())

def term(n: int) -> mp.mpf:
    x = mp.mpf(n) + mp.mpf('0.5')
    return peval(x)*mp.zeta(10,n+1)*mp.zeta(16,n+1)-qeval(x)

# mpmath's Richardson/Shanks machinery handles the O(n^-2) tail here.
value = mp.nsum(lambda n: term(int(n)), [0, mp.inf])
error = value-mp.zeta(2)
print("diagnostic value:", mp.nstr(value, 60))
print("zeta(2):         ", mp.nstr(mp.zeta(2), 60))
print("absolute error:  ", mp.nstr(abs(error), 8))
if abs(error) > mp.mpf('1e-45'):
    raise SystemExit("numerical diagnostic did not reach the requested precision")
