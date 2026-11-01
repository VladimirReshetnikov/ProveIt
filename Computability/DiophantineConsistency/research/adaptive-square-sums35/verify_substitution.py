#!/usr/bin/env python3
"""Check the 36-to-35 residual substitution as exact integer polynomials."""
import runpy
from pathlib import Path

D = Path(__file__).resolve().parent
old = runpy.run_path(str(D.parent / 'adaptive-square-sums36/verify_degree.py'))
new = runpy.run_path(str(D / 'verify_degree.py'))
P = new['P']
g = new['g']
replacement = {name: g[name] for name in new['names']}
replacement['squareVariable'] = g['g80']

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
    value = substitute(old['g'][name])
    if name == 'squareDifference':
        if value != P.lift(0):
            raise ValueError(('eliminated residual is nonzero', name))
    elif value != g[name]:
        raise ValueError(('residual differs after substitution', name))
if [n for n in old['factors_names'] if n != 'squareDifference'] != new['factors_names']:
    raise ValueError('residual order differs')
print('PASS: all 23 parent residuals agree under substitution; the removed residual vanishes')
