#!/usr/bin/env python3
"""High-precision, non-certified diagnostics of the Fourier contact powers.

Requires mpmath. No transport optimization is performed. The finite product
uses 121 factors; its agreement with the analytic coefficient is numerical
corroboration and is not an interval certificate for an infinite product.
Run from the package root: python code/fourier_diagnostics.py
"""
from pathlib import Path
from itertools import combinations
import csv
import json
import math
import mpmath as mp

mp.mp.dps = 90
ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
DATA.mkdir(exist_ok=True)


def truncated_fourier_derivative(q, T, r, max_level=120):
    # Taylor coefficients in h for sinc(pi*a*(T+h)), then exact finite
    # polynomial multiplication truncated to degree r. sinpi is stable
    # at the integer zero of the fixed level-0 factor.
    product = [mp.mpf(1)] + [mp.mpf(0)] * r
    for k in range(max_level+1):
        a = q**k
        sine = [(mp.pi*a)**j / mp.factorial(j) *
                mp.sinpi(a*T + mp.mpf(j)/2) for j in range(r+1)]
        coeff = [sum(sine[j] * (-1)**(u-j) /
                     (mp.pi*a*T**(u-j+1)) for j in range(u+1))
                 for u in range(r+1)]
        product = [sum(product[j]*coeff[u-j] for j in range(u+1))
                   for u in range(r+1)]
    return mp.factorial(r)*product[r]


def tail_constant(B, terms=150):
    return mp.fprod(mp.sinpi(mp.mpf(B)**(-j)) /
                    (mp.pi*mp.mpf(B)**(-j)) for j in range(1, terms+1))


def critical(D):
    e, i = min((d+1-i, i) for i, d in enumerate(D) if i >= 1)
    return e, D[i], i


cases = [(2, (1, 1)), (2, (1, 3)), (2, (3, 3, 3)),
         (2, (4, 4, 4)), (2, (0, 3, 3)), (3, (2, 4, 4))]
rows = []
for B, D in cases:
    e, n, r = critical(D)
    T = B**n
    PB = tail_constant(B)
    symmetric = sum(math.prod(c) for c in combinations(range(1, n+1), e))
    coefficient = mp.factorial(r)*PB*B**e*mp.mpf(T)**(-r)*symmetric
    sign = (-1)**sum(B**j for j in range(n+1))
    for magnitude in ['0.001', '0.0003', '0.0001', '0.00003', '0.00001']:
        for direction in [-1, 1]:
            delta = direction*mp.mpf(magnitude)
            value = truncated_fourier_derivative(mp.mpf(1)/B+delta, T, r)
            ratio = value/(sign*coefficient*delta**e)
            rows.append({'B':B, 'D':','.join(map(str,D)), 'n':n, 'r':r, 'e':e,
                         'delta':mp.nstr(delta, 12),
                         'coefficient_abs':mp.nstr(coefficient, 35),
                         'normalized_ratio':mp.nstr(ratio, 35),
                         'absolute_ratio_error':mp.nstr(abs(ratio-1), 15)})
with (DATA/'fourier_diagnostics.csv').open('w', newline='', encoding='utf-8') as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0]))
    w.writeheader()
    w.writerows(rows)
PB = tail_constant(2)
summary = {
    'status':'completed; numerical corroboration only',
    'mpmath_digits':mp.mp.dps, 'product_levels_included':[0,120],
    'tail_constant_terms':150, 'number_of_rows':len(rows),
    'P2':mp.nstr(PB,50),
    'triple_width_one_eighth_lower_coefficient':
        mp.nstr(PB/(8*mp.pi**2*mp.sqrt(1+121*mp.pi**2)),40),
    'near_resonance_samples': [r for r in rows if abs(mp.mpf(r['delta'])) == mp.mpf('0.00001')],
    'limitations':['Finite product diagnostics are not interval bounds.',
                   'The optimal Wasserstein distance is not computed.',
                   'The proof, not these samples, establishes the exponents.']
}
(DATA/'fourier_summary.json').write_text(json.dumps(summary, indent=2)+'\n', encoding='utf-8')
print(json.dumps(summary, indent=2))
