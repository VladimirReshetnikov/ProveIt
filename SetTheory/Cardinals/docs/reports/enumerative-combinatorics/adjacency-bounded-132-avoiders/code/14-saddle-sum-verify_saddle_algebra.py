#!/usr/bin/env python3
"""Exact algebra checks for the unified scalar saddle sum. Standard library."""
from fractions import Fraction as F
from pathlib import Path
import json, math

def add(dst, key, value):
    dst[key] = dst.get(key, F(0)) + value
    if not dst[key]:
        del dst[key]

def deriv(poly):
    out = {}
    for (a, b, c, d, e), coef in poly.items():
        if b:
            add(out, (a, b - 1, c, d, e), coef * b)
        if c:
            add(out, (a + 1, b - 2, c - 2, d + 1, e), -coef * c)
        if d:
            add(out, (a + 1, b - 2, c - 1, d - 1, e + 1), -coef * d)
        if not e == 0:
            raise AssertionError('No derivative of fourth cumulant is needed.')
    return out
f2 = {(2, -3, -1, 0, 0): F(1)}
f3 = deriv(f2)
if not f3 == {(2, -4, -1, 0, 0): F(-3), (3, -5, -3, 1, 0): F(1)}:
    raise AssertionError('Exact algebra check failed')
f4 = deriv(f3)
if not f4 == {(2, -5, -1, 0, 0): F(12), (3, -6, -3, 1, 0): F(-8), (4, -7, -4, 0, 1): F(-1), (4, -7, -5, 2, 0): F(3)}:
    raise AssertionError('Exact algebra check failed')
limit_third = F(-2) * F(1, 2) ** 3
if not limit_third == F(-1, 4):
    raise AssertionError('Exact algebra check failed')
if not limit_third / F(math.factorial(3)) == F(-1, 24):
    raise AssertionError('Exact algebra check failed')
if not F(1, 24) * F(1, 2) ** 3 == F(1, 192):
    raise AssertionError('Exact algebra check failed')
rows = 0
for mu in [F(3, 2), F(7), F(91, 3)]:
    for variance in [F(2, 3), F(5), F(13, 2)]:
        for L in [F(4), F(25, 2), F(101, 3)]:
            for b in [F(1, 3), F(2, 5)]:
                ratio_sq = L / (b ** 4 * variance) / (L / (b * b * mu)) ** 2
                H_sq = variance * L / (mu * mu)
                if not ratio_sq == 1 / H_sq:
                    raise AssertionError('Exact algebra check failed')
                rows += 1
data = {'third_derivative_terms': [[list(k), str(v)] for k, v in sorted(f3.items())], 'fourth_derivative_terms': [[list(k), str(v)] for k, v in sorted(f4.items())], 'cubic_action_constant': str(limit_third / F(6)), 'half_integer_multiplier_constant': str(F(1, 192)), 'exact_prefactor_checks': rows, 'passed': True}
Path(__file__).with_name('saddle_algebra_results.json').write_text(json.dumps(data, indent=2) + '\n')
print(json.dumps({'passed': True, 'exact_prefactor_checks': rows, 'derivative_identities': 2}))
