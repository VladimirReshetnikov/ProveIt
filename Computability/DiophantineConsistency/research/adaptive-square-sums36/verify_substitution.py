#!/usr/bin/env python3
"""Check the simultaneous 40-to-36 substitution as exact polynomials."""
import runpy
from pathlib import Path

D = Path(__file__).resolve().parent
old = runpy.run_path(str(D.parent / 'adaptive-square-sums40/verify_degree.py'))
new = runpy.run_path(str(D / 'verify_degree.py'))
P = new['P']
g = new['g']
replacement = {name: g[name] for name in new['names']}
for variable, value in [('cubeVariable', 'q3'), ('productVariable', 'g55'),
                        ('psiSquareVariable', 'g39'), ('ySquareVariable', 'y2')]:
    replacement[variable] = g[value]

def substitute(polynomial):
    total = P.lift(0)
    for monomial, coefficient in polynomial.d.items():
        term = P.lift(coefficient)
        for name, exponent in zip(old['names'], monomial):
            for _ in range(exponent):
                term = term * replacement[name]
        total = total + term
    return total

removed = {'cubeDifference', 'productDifference', 'psiSquareDifference', 'ySquareDifference'}
for name in old['factors_names']:
    value = substitute(old['g'][name])
    if name in removed:
        if value != P.lift(0):
            raise ValueError(('eliminated residual is nonzero', name))
    elif value != g[name]:
        raise ValueError(('residual differs after substitution', name))
if [n for n in old['factors_names'] if n not in removed] != new['factors_names']:
    raise ValueError('residual order differs')
print('PASS: all 27 parent residuals agree under the simultaneous substitution; four vanish')
