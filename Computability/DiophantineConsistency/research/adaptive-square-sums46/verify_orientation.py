#!/usr/bin/env python3
"""Verify the proposed negative-Z orientation as exact polynomials."""
import runpy
from pathlib import Path

D = Path(__file__).resolve().parent
old = runpy.run_path(str(D.parent / 'adaptive-square-sums47/verify_degree.py'))
new = runpy.run_path(str(D / 'verify_degree.py'))
names = new['names'] + ['orientationQuotient']
zero = (0,) * len(names)

class P:
    def __init__(self, terms):
        self.terms = {k: v for k, v in terms.items() if v}

    @staticmethod
    def lift(value):
        return value if isinstance(value, P) else P({zero: value})

    def __add__(self, value):
        result = self.terms.copy()
        for key, coefficient in P.lift(value).terms.items():
            result[key] = result.get(key, 0) + coefficient
        return P(result)

    def __neg__(self):
        return P({key: -coefficient for key, coefficient in self.terms.items()})

    def __sub__(self, value):
        return self + -P.lift(value)

    def __mul__(self, value):
        result = {}
        for left, a in self.terms.items():
            for right, b in P.lift(value).terms.items():
                key = tuple(x + y for x, y in zip(left, right))
                result[key] = result.get(key, 0) + a * b
        return P(result)

    def __eq__(self, value):
        return self.terms == P.lift(value).terms

v = {}
for i, name in enumerate(names):
    exponent = [0] * len(names)
    exponent[i] = 1
    v[name] = P({tuple(exponent): 1})
old_map = {name: v[name] for name in new['names']}
old_map['zPositive'] = P.lift(1)
old_map['zNegative'] = v['zValueVariable'] + P.lift(1)
new_map = {name: v[name] for name in new['names']}
new_map['r'] = v['r'] + P.lift(2) * v['orientationQuotient']

def substitute(polynomial, source_names, mapping):
    total = P.lift(0)
    for monomial, coefficient in polynomial.d.items():
        term = P.lift(coefficient)
        for name, exponent in zip(source_names, monomial):
            for _ in range(exponent):
                term = term * mapping[name]
        total = total + term
    return total

for name in old['factors_names']:
    before = substitute(old['g'][name], old['names'], old_map)
    after = substitute(new['g'][name], new['names'], new_map)
    if name == 'zDifference':
        expected = P.lift(2) * (v['zValueVariable'] - v['scaleVariable'] * v['orientationQuotient'])
        if after - before != expected:
            raise ValueError(('incorrect orientation displacement', name))
    elif after != before:
        raise ValueError(('unexpected changed residual', name))
print('PASS: negative Z becomes positive after the r-shift whenever Z magnitude = scale * quotient')
print('This polynomial identity does not establish the quotient or positive-witness map in Lean.')
