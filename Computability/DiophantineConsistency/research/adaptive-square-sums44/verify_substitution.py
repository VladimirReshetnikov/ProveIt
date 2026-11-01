#!/usr/bin/env python3
"""Check the two positive-coordinate embeddings as exact polynomials."""
import runpy
from pathlib import Path

D = Path(__file__).resolve().parent
old = runpy.run_path(str(D.parent / 'adaptive-square-sums46/verify_degree.py'))
new = runpy.run_path(str(D / 'verify_degree.py'))
P = new['P']
g = new['g']
replacement = {name: g[name] for name in new['names']}
replacement['wPositive'] = g['wValueVariable'] + P.lift(1)
replacement['wNegative'] = P.lift(1)
replacement['rootSkewPositive'] = g['rootSkewVariable'] + P.lift(1)
replacement['rootSkewNegative'] = P.lift(1)

def substitute(polynomial):
    total = P.lift(0)
    for monomial, coefficient in polynomial.d.items():
        term = P.lift(coefficient)
        for name, exponent in zip(old['names'], monomial):
            for _ in range(exponent):
                term = term * replacement[name]
        total = total + term
    return total

for name in old['factors_names']:
    if substitute(old['g'][name]) != g[name]:
        raise ValueError(('residual differs after substitution', name))
if old['factors_names'] != new['factors_names']:
    raise ValueError('residual order differs')
print('PASS: all 33 parent residuals agree under the positive W/root-skew embedding')
