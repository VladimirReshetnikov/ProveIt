#!/usr/bin/env python3
"""Check all AQ26 residuals under the four simultaneous substitutions."""
from pathlib import Path
import runpy

if not __debug__:
    raise RuntimeError('optimized Python is not supported')

D = Path(__file__).resolve().parent
old = runpy.run_path(str(D.parent / 'adaptive-square-sums26-degree8/verify_degree.py'))
new = runpy.run_path(str(D / 'verify_degree.py'))
P, graph = new['P'], new['g']
replacements = {name: graph[name] for name in new['names']}
replacements.update({'cVariable': graph['c'], 'productVariable2': graph['E'],
                     'qSquareVariable': graph['q2'], 'qValueVariable': graph['QComputed']})
removed = {'cDifference', 'product2Difference', 'qSquareDifference', 'qSignedDifference'}
if set(old['factors_names']) - removed != set(new['factors_names']) or len(removed) != 4:
    raise ValueError('residual coverage')

def substitute(poly):
    total = P.lift(0)
    for monomial, coefficient in poly.d.items():
        term = P.lift(coefficient)
        for name, exponent in zip(old['names'], monomial):
            for _ in range(exponent):
                term = term * replacements[name]
        total = total + term
    return total

for name in old['factors_names']:
    expected = P.lift(0) if name in removed else graph[name]
    if substitute(old['g'][name]) != expected:
        raise ValueError(('residual mismatch', name))
print('PASS: 13 retained residuals agree and all four deleted residuals vanish')
