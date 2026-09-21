#!/usr/bin/env python3
"""Optional numerical cross-checks (not proofs); requires mpmath.

All interval bounds originate in exact rational arithmetic and the article's
proof. Here they are compared with independently evaluated zeta constants.
The asymptotic ratios should tend to 1 for fixed offset as N increases.
"""
from __future__ import annotations
import csv
import json
from fractions import Fraction
from pathlib import Path
import mpmath as mp

ROOT = Path(__file__).resolve().parent

def number(value: Fraction) -> mp.mpf:
    return mp.mpf(value.numerator) / value.denominator

def predict(family: str, k: int, n: int) -> mp.mpf:
    if family == 'zeta3':
        lam = 17 + 12*mp.sqrt(2)
        return 96*mp.sqrt(2)*mp.pi**3/(lam**k*(lam**2-1))*lam**(-2*n)
    phi = (1+mp.sqrt(5))/2
    lam = phi**5
    offset_power = 4*k if family == 'zeta2_upper' else 6*k
    sign = (-1)**(n if family == 'zeta2_upper' else n+k)
    return sign*20*mp.pi**2*mp.sqrt(5)/(phi**offset_power*(lam**2+1))*lam**(-2*n)

def main() -> None:
    with (ROOT/'data/certified_intervals.csv').open(newline='') as stream:
        records = list(csv.DictReader(stream))
    rows = []
    max_relative_precision_change = mp.mpf(0)
    for row in records:
        value = Fraction(int(row['partial_numerator']), int(row['partial_denominator']))
        bound = Fraction(int(row['bound_numerator']), int(row['bound_denominator']))
        family = row['family']
        k, n = int(row['offset']), int(row['terms'])
        s = 3 if family == 'zeta3' else 2
        with mp.workdps(200):
            error200 = mp.zeta(s) - number(value)
        with mp.workdps(250):
            error = mp.zeta(s) - number(value)
            if mp.sign(error) != int(row['error_sign']):
                raise ArithmeticError(f'Numerical sign mismatch: {family}, k={k}, N={n}')
            if not abs(error) <= number(bound):
                raise ArithmeticError(f'Numerical interval mismatch: {family}, k={k}, N={n}')
            precision_change = abs(error-error200)/abs(error)
            if precision_change > mp.mpf('1e-40'):
                raise ArithmeticError('Insufficient numerical precision.')
            max_relative_precision_change = max(max_relative_precision_change, precision_change)
            rows.append([family, k, n, mp.nstr(error, 35),
                         mp.nstr(error/predict(family,k,n), 25)])
    with (ROOT/'data/numerical_checks.csv').open('w', newline='') as stream:
        writer = csv.writer(stream)
        writer.writerow(['family','offset','terms','signed_error_250_dps',
                         'error_divided_by_leading_asymptotic'])
        writer.writerows(rows)
    report = {'status':'PASS', 'mpmath_version':mp.__version__,
              'intervals_cross_checked':len(rows), 'decimal_precisions':[200,250],
              'max_relative_error_change_between_precisions':
                  mp.nstr(max_relative_precision_change, 8),
              'warning':'Numerical checks are not rigorous interval certificates.'}
    (ROOT/'data/numerical_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
