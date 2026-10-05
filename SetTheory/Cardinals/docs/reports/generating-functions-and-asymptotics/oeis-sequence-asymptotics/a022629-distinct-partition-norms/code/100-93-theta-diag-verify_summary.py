#!/usr/bin/env python3
"""Sanity checks for saved results, not a proof/certification of coefficients.

Checks deliberately use explicit exceptions so python -O cannot disable them.
"""
import json
import os


def require(condition, message):
    if not condition:
        raise ValueError(message)


p = os.path.dirname(__file__)
with open(os.path.join(p, 'diagnostics_complete.json')) as f:
    rows = json.load(f)['rows']
require(len(rows) == 18, 'Expected exactly 18 diagnostic rows')
for index, r in enumerate(rows):
    label = f"Row {index}: lambda={r['lam_target']}, a={r['a']}, phase={r['phase_target']}"
    require(isinstance(r['n'], int), f'{label}: n is not an integer')
    require(abs(float(r['n_round_delta'])) <= .500001,
            f'{label}: n-rounding error exceeds a half unit')
    require(abs(float(r['mu_minus_target'])) < .51 / float(r['K']),
            f'{label}: phase error exceeds the tested rounding bound')
    require(abs(float(r['actual_lambda']) - r['lam_target']) < .002,
            f'{label}: actual lambda is too far from its target')
    require(r['omitted_arcs']['omitted_normalized_envelope_integral'] < 4e-14,
            f'{label}: omitted-arc envelope diagnostic exceeds tolerance')
    require(float(r['discarded_variables_TV_multiplier_bound']) < 6.4e-22,
            f'{label}: discarded-variable coupling bound exceeds tolerance')
    require(r['quadrature']['max_exact_product_point_error'] < 5e-20,
            f'{label}: direct characteristic-product check exceeds tolerance')
    require(float(r['multiplier']) > 0, f'{label}: multiplier is not positive')
for lam in [4, 5]:
    for ph in [0, .5]:
        rr = [r for r in rows if r['lam_target'] == lam
              and r['phase_target'] == ph and r['a'] >= 20]
        errs = [abs(float(r['relative_theta_error'])) for r in rr]
        require(all(x > y for x, y in zip(errs, errs[1:])),
                f'lambda={lam}, phase={ph}: relative errors do not decrease')
print('18 rows verified; all tests are numerical diagnostics, not rigorous coefficient certificates.')
