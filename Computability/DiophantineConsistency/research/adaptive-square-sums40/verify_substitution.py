#!/usr/bin/env python3
"""Check the 42-to-40 residual substitution as exact integer polynomials."""
import runpy
from pathlib import Path

D = Path(__file__).resolve().parent
old = runpy.run_path(str(D.parent / 'adaptive-square-sums42/verify_degree.py'))
new = runpy.run_path(str(D / 'verify_degree.py'))
P = new['P']
g = new['g']
replacement = {name: g[name] for name in new['names']}
replacement['aVariable'] = g['productVariable2'] + g['Y']
replacement['qPositive'] = g['qValueVariable'] + P.lift(1)
replacement['qNegative'] = P.lift(1)

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
    if name == 'aDifference':
        if value != P.lift(0):
            raise ValueError(('eliminated residual is nonzero', name))
    elif value != g[name]:
        raise ValueError(('residual differs after substitution', name))
if [n for n in old['factors_names'] if n != 'aDifference'] != new['factors_names']:
    raise ValueError('residual order differs')
print('PASS: all 28 parent residuals agree under substitution; the removed residual vanishes')
