#!/usr/bin/env python3
"""Exact rational checks supporting the all-n low-k error constants.

This checks the explicit inequalities in the analytic proof. It does not replace
Rouche's theorem/Cauchy's estimate, and does not implement a numerical inverse.
"""
from fractions import Fraction as F
from math import factorial, comb
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def interval(data, key):
    value = data[key]['outward_decimal_25']
    require(isinstance(value, list) and len(value) == 2, 'invalid interval shape')
    a, b = map(F, value)
    require(a <= b, 'reversed interval')
    return a, b


def generate(certificate, exact):
    rho = interval(certificate, 'rho')
    require(F(148, 100) < rho[0] <= rho[1] < F(3, 2), 'root range')
    eta = F(13, 100)-F(11, 1000)
    require(eta == F(119, 1000), 'circle lower bound')
    require(F(5, 468) < F(11, 1000), 'Taylor circle tail')
    require(sum(F(4)**m/F(2)**comb(m, 2) for m in range(6)) == 26, 'majorant partial sum')
    require(26+F(2, 15) < 27, 'majorant geometric tail')
    require(2*(F(91, 6)+F(1, 32)) == F(1459, 48) < 32, 'H4 coefficient majorant')
    bounds = {2: {1: 5, 2: 2}, 3: {1: 11, 2: 3}, 4: {1: 3, 2: 4, 3: 2}}
    coeff = {k: {j: interval(certificate, 'P%d_binomial%d' % (k, j)) for j in p}
             for k, p in bounds.items()}
    for k, p in bounds.items():
        for j, v in p.items():
            require(max(map(abs, coeff[k][j])) < v, 'Laurent absolute bound')
    principal = {k: sum(v*3**j for j, v in p.items()) for k, p in bounds.items()}
    require(principal == {2: 33, 3: 60, 4: 99}, 'principal part bounds')
    boundary = {2: F(27, 2)/eta**2+33, 3: F(54)/eta**2+60,
                4: F(864)/eta**2+F(27, 2)**2/eta**3+99}
    M = {2: 1000, 3: 3900, 4: 170000}
    for k in M:
        require(boundary[k] < M[k], 'effective remainder constant')
    error_at_50 = F(170000)*F(3, 4)**50
    require(error_at_50 < F(1, 10), 'envelope error at 50')
    # Coefficientwise monomial lower bounds valid for every real x >= 0.
    monomial = {
        2: [coeff[2][1][0]+coeff[2][2][0], coeff[2][2][0]],
        3: [coeff[3][1][0]+coeff[3][2][0], coeff[3][2][0]],
        4: [coeff[4][1][0]+coeff[4][2][0]+coeff[4][3][0],
            coeff[4][2][0]+F(3, 2)*coeff[4][3][0], coeff[4][3][0]/2]}
    lower = {2: [F(-7, 2), F(3, 2)], 3: [F(-43, 5), F(12, 5)],
             4: [F(-9, 2), F(-29, 20), F(13, 20)]}
    for k in lower:
        require(all(a > b for a, b in zip(monomial[k], lower[k])), 'polynomial lower bound')
        require(sum(v*50**j for j, v in enumerate(lower[k])) > F(1, 10), 'positive envelope at 50')
        require(sum(j*v*50**(j-1) for j, v in enumerate(lower[k]) if j) > F(1, 10),
                'positive envelope derivative at 50')
    # A finite supplemental check, distinct from the all-n analytic proof.
    comparisons = 0
    for k in M:
        for n, count in enumerate(exact['counts'][str(k)]):
            normalized = F(k*count, factorial(n)**2*2**comb(n, 2))
            p = tuple(sum(v[side]*comb(n+j-1, j-1) for j, v in coeff[k].items())
                      for side in (0, 1))
            rp = (rho[1]**(-n), rho[0]**(-n))
            products = [x*y for x in p for y in rp]
            require(max(abs(normalized-min(products)), abs(normalized-max(products))) <= F(M[k], 2**n),
                    'finite all-n bound check')
            comparisons += 1
    return {'status': 'PASS', 'arithmetic': 'exact Fraction only',
            'error_radius': '2', 'constants': M,
            'circle_E_lower_bound': str(eta),
            'boundary_remainder_upper_bounds': {k: str(v) for k, v in boundary.items()},
            'envelope_start': 50, 'envelope_error_upper_bound_at_50': str(error_at_50),
            'polynomial_monomial_lower_bounds': {k: [str(v) for v in p] for k, p in lower.items()},
            'supplemental_finite_count_checks': comparisons,
            'all_n_justification': 'analytic proof plus the exact inequalities checked here',
            'certified_inverse_solver_implemented': False}


if __name__ == '__main__':
    certificate = json.loads(Path('constant_certificate.json').read_text())
    exact = json.loads(Path('exact_checks.json').read_text())
    result = generate(certificate, exact)
    with open('effective_error_checks.json', 'x', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print('PASS: exact effective-error and envelope inequalities')
