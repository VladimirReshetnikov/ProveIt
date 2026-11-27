#!/usr/bin/env python3
"""Reproduce exact constant certificates, finite bounds, and the paper figure."""

from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction
from math import isqrt
from pathlib import Path
import csv
import json
import sys

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)  # Exact rational certificates can exceed 4,300 digits.

from compression_law import (balanced_likelihood, boundary_normalizer,
    delta_interval, even_product, first_correction, gram_tv_square_bound,
    likelihood, odd_product, rank_tv_bound)
from verify_exhaustive import Field, all_matrices, predicted_joint

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'results'
FIGURES = ROOT / 'figures'
RESULTS.mkdir(exist_ok=True)
FIGURES.mkdir(exist_ok=True)


def decimal_out(x, places=30, up=False):
    """Directed decimal rounding of an exact rational number."""
    with localcontext() as ctx:
        ctx.prec = places + 60
        ctx.rounding = ROUND_CEILING if up else ROUND_FLOOR
        value = Decimal(x.numerator) / Decimal(x.denominator)
        return str(value.quantize(Decimal(1).scaleb(-places)))


def sqrt_upper(x, places=40):
    scale = 10**places
    floor_square = x.numerator * scale * scale // x.denominator
    upper = Fraction(isqrt(floor_square) + 1, scale)
    assert upper * upper > x
    return upper


def rational_record(x):
    return {'numerator': str(x.numerator), 'denominator': str(x.denominator)}


constants = []
for q in (2, 3, 4, 5, 8, 9):
    lo, hi = delta_interval(q, 48)
    assert 0 < lo < hi < 1
    assert hi - lo < Fraction(1, 10**27)
    constants.append({'q': q, 'factors': 48,
                      'lower_decimal': decimal_out(lo),
                      'upper_decimal': decimal_out(hi, up=True),
                      'lower_rational': rational_record(lo),
                      'upper_rational': rational_record(hi)})
(RESULTS / 'certified_constants.json').write_text(json.dumps({
    'formula': 'Delta_q = product_odd(1-q^-j)*(1-product_even(1-q^-j))',
    'method': 'Exact rational product bounds; omitted-tail product >= 1-tail sum.',
    'constants': constants}, indent=2) + '\n')

bounds = []
for m in range(1, 13):
    q, a, b = 2, 4*m, 2*m
    epsilon = sqrt_upper(gram_tv_square_bound(q, a, b, 48))
    factor = 1 - even_product(q, b//2) / boundary_normalizer(q, a, b)
    O = odd_product(q, b//2)
    lower = factor * max(Fraction(0), O-epsilon)
    upper = factor * min(Fraction(1), O+epsilon)
    rank_upper = min(Fraction(1), rank_tv_bound(q, a, b))
    bounds.append({'m': m, 'q': q, 'a': a, 'b': b, 'ambient_dimension': a+b,
                   'full_tv_lower': decimal_out(lower, 25),
                   'full_tv_upper': decimal_out(upper, 25, up=True),
                   'rank_tv_upper': decimal_out(rank_upper, 25, up=True),
                   'gram_tv_upper': decimal_out(epsilon, 25, up=True)})
with (RESULTS / 'boundary_bounds.csv').open('w', newline='') as stream:
    writer = csv.DictWriter(stream, fieldnames=list(bounds[0]))
    writer.writeheader()
    writer.writerows(bounds)

# Inspect fixed-size expansions on all 2x2 observations and all alternating
# 2x2 forms over F_2 and F_3. Counts are evaluated by a separate module from
# the frame-enumeration verifier; normalization of A is checked exactly.
first_order = []
for q in (2, 3):
    field = Field(q)
    for fv in range(q):
        F = ((0, fv), (field.neg[fv], 0))
        f = int(fv != 0)
        for hv in range(q):
            H = ((0, hv), (field.neg[hv], 0))
            h = int(hv != 0)
            coefficients = []
            scaled_errors = {N: Fraction(0) for N in (4, 6, 8)}
            mass = {N: Fraction(0) for N in (4, 6, 8)}
            for M in all_matrices(q, 2, 2):
                _, (s, u, v, _) = predicted_joint(field, 4, F, H, M)
                A = first_correction(q, 2, 2, f, h, s, u, v)
                coefficients.append(A)
                for N in scaled_errors:
                    L = likelihood(q, N, 2, 2, f, h, s, u, v)
                    t = Fraction(1, q**(2*N))
                    scaled_errors[N] = max(scaled_errors[N], abs(L-1-A*t)/(t*t))
                    mass[N] += L / q**4
            assert sum(coefficients) == 0
            assert all(value == 1 for value in mass.values())
            C = Fraction(sum(abs(x) for x in coefficients), 2*q**4)
            assert C >= Fraction(q-1, q)
            first_order.append({'q': q, 'F_upper': fv, 'H_upper': hv,
                                'sum_A': 0, 'C': rational_record(C),
                                'max_scaled_remainder_at_N': {
                                    str(N): decimal_out(value, 12, up=True)
                                    for N, value in scaled_errors.items()}})

# Every residual-corank likelihood has the predicted strict sign on a grid
# of dimensions, independently of whether particular matrices are sampled.
sign_cases = 0
for q in (2, 3, 4, 5, 8, 9):
    for a in (2, 4, 6, 10):
        for b in (2, 4, 6, 10):
            for ell in range(b//2 + 1):
                L = balanced_likelihood(q, a, b, ell)
                assert (L < 1) if ell == 0 else (L > 1)
                sign_cases += 1
(RESULTS / 'formula_checks.json').write_text(json.dumps({
    'status': 'passed', 'first_order_checks': first_order,
    'boundary_likelihood_sign_cases': sign_cases,
    'scope': 'Finite checks supplement the proofs; they do not prove asymptotics.'
}, indent=2) + '\n')

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                     'axes.spines.top': False, 'axes.spines.right': False,
                     'pdf.fonttype': 42})
x = [row['m'] for row in bounds]
lo = [float(row['full_tv_lower']) for row in bounds]
hi = [float(row['full_tv_upper']) for row in bounds]
rank = [float(row['rank_tv_upper']) for row in bounds]
delta = float(sum(delta_interval(2, 48), Fraction(0))/2)
fig, ax = plt.subplots(figsize=(7.5, 4.35), layout='constrained')
ax.fill_between(x, lo, hi, color='#177e89', alpha=.3,
                label='Certified full-matrix interval', zorder=4)
ax.plot(x, [(a+b)/2 for a,b in zip(lo,hi)], color='#177e89', linewidth=2, zorder=4)
ax.plot(x, rank, color='#b85c38', marker='o', markersize=4, linewidth=1.7,
        label='Upper bound for rank-only distance')
ax.axhline(delta, color='#28334a', linestyle='--', linewidth=1.2,
           label=r'Positive limit $\Delta_2 = 0.130634\ldots$')
ax.set_yscale('log')
ax.set_ylim(5e-8, .55)
ax.set_xlim(.8,12.2)
ax.set_xticks(range(1,13))
ax.set_xlabel(r'$m$: block size $4m\times2m$, ambient dimension $6m$')
ax.set_ylabel('Total-variation distance (log scale)')
ax.set_title('Full matrix dependence persists as rank information vanishes',
             loc='left', fontsize=12, pad=12, fontweight='bold')
ax.grid(axis='y', color='#dde2e8', linewidth=.6)
ax.legend(loc='lower left', frameon=False, fontsize=9)
fig.savefig(FIGURES / 'boundary_bounds.pdf')
fig.savefig(FIGURES / 'boundary_bounds.png', dpi=180)
plt.close(fig)
print(json.dumps({'status': 'passed', 'constant_certificates': len(constants),
                  'first_order_form_pairs': len(first_order),
                  'likelihood_sign_cases': sign_cases,
                  'boundary_rows': len(bounds), 'figure': 'figures/boundary_bounds.pdf'},
                 indent=2))
