#!/usr/bin/env python3
"""Exact finite arithmetic cross-check for a restricted negative-root template.

This does not establish the template's hypotheses for any 85 zero and does
not replace the Lean proof. The preceding inequality gives Y < 54; for
positive q >= 2 with q^3 | Y and Y >= 8, q is 2 or 3. With H | 27(8X+1),
X >= 1, the positive quotient m is at most 6. We solve the resulting linear
equation for *all* integer X rather than searching up to a chosen X bound.
"""
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


cases = []
zero_coefficient = []
for q in (2, 3):
    for y in range(8, 54):
        if y % q**3:
            continue
        for m in range(1, 7):
            # 27(8X+1) = m(4Y(X+1)+3).
            coefficient = 216 - 4*y*m
            right = 4*y*m + 3*m - 27
            if coefficient == 0:
                zero_coefficient.append([q, y, m, right])
                require(right != 0, 'unbounded X family requires separate analysis')
                continue
            if right % coefficient:
                continue
            x = right // coefficient
            if x < 1:
                continue
            require(27*(8*x+1) == m*(4*y*(x+1)+3), 'linear reconstruction')
            eta = 4*((y*(x+1))**2+4*y*(x+1)+3)+3 - y*(8*x*y*y+4)
            cases.append({'q':q, 'Y':y, 'm':m, 'X':x, 'eta':eta})

require(cases == [{'q':2, 'Y':48, 'm':1, 'X':7, 'eta':-5597361}],
        'unexpected surviving arithmetic case')
require(all(case['eta'] <= 0 for case in cases), 'positive eta remains possible')
print(json.dumps({'result':'PASS', 'integer_cases':cases,
                  'zero_coefficient_cases':zero_coefficient,
                  'scope':'Necessary arithmetic for this restricted template; not full 85 zero equivalence or arbitrary-model proof.'},
                 indent=2, sort_keys=True))
