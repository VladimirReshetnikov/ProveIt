#!/usr/bin/env python3
"""Check the 49-to-47 residual substitution as exact integer polynomials."""
import runpy
from pathlib import Path

D = Path(__file__).resolve().parent
old = runpy.run_path(str(D.parent / 'adaptive-square-sums49/verify_degree.py'))
new = runpy.run_path(str(D / 'verify_degree.py'))
P = new['P']
old_names = old['names']
new_names = new['names']
g = new['g']
replacement = {name: g[name] for name in new_names}
replacement['cVariable'] = g['eta'] + g['ySumVariable']
replacement['aVariable'] = g['productVariable2'] + g['Y']

def substitute(polynomial):
    total = P.lift(0)
    for monomial, coefficient in polynomial.d.items():
        term = P.lift(coefficient)
        for name, exponent in zip(old_names, monomial):
            for _ in range(exponent):
                term = term * replacement[name]
        total = total + term
    return total

removed = {'cDifference', 'aDifference'}
for name in old['factors_names']:
    value = substitute(old['g'][name])
    if name in removed:
        if value != P.lift(0):
            raise ValueError(('eliminated residual is nonzero', name))
    elif value != g[name]:
        raise ValueError(('residual differs after substitution', name))
if [n for n in old['factors_names'] if n not in removed] != new['factors_names']:
    raise ValueError('residual order differs')
print('PASS: all 35 parent residuals agree under substitution; both removed residuals vanish')
