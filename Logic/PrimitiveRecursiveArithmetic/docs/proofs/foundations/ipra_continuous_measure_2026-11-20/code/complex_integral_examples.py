#!/usr/bin/env python3
"""Rational coefficient, quadrature, and derivative-tail checks."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json


def falling(m, j):
    return F(factorial(m + j), factorial(m))


def partial(z, j, n):
    return sum((falling(m, j) * z ** m / (m + j + 1) for m in range(n)), F(0))


def derivative_tail(r, j, n):
    if r == 0:
        return F(0) if n >= 1 else F(factorial(j))
    theta = (1 + r) / 2
    alpha = r / theta
    return factorial(j) * alpha ** n / ((1 - theta) ** (j + 1) * (1 - alpha))


def main():
    checks = 0
    examples = []
    # The polynomial integral is independently enclosed by left/right sums.
    for power in range(10):
        integral = F(1, power + 1)
        for m in (4, 16, 64):
            lower = sum((F(i, m) ** power for i in range(m)), F(0)) / m
            upper = sum((F(i + 1, m) ** power for i in range(m)), F(0)) / m
            assert lower <= integral <= upper
            assert upper - lower <= F(max(1, power), m)
            checks += 2

    for r in (F(0), F(1, 4), F(1, 2)):
        for j in range(5):
            for n in (1, 2, 4, 8, 16):
                bound = derivative_tail(r, j, n)
                observed_tail = partial(r, j, n + 40) - partial(r, j, n)
                assert 0 <= observed_tail <= bound
                examples.append({'r': r, 'order': j, 'terms': n,
                                 'value': partial(r, j, n), 'tail_bound': bound,
                                 'next_40_terms': observed_tail})
                checks += 1
    for n in (1, 3, 8, 16):
        for k in range(17):
            t, z = F(k, 16), F(1, 2)
            direct = 1 / (1 - z * t)
            geometric = sum(((z * t) ** m for m in range(n)), F(0))
            exact_remainder = (z * t) ** n / (1 - z * t)
            assert direct - geometric == exact_remainder
            assert exact_remainder <= 2 * F(1, 2) ** n
            checks += 2

    # Independent monotone quadrature interval for integral 1/(1-t/2).
    m = 256
    lower = sum((1 / (1 - F(i, 2 * m)) for i in range(m)), F(0)) / m
    upper = sum((1 / (1 - F(i + 1, 2 * m)) for i in range(m)), F(0)) / m
    n = 12
    series_lower = partial(F(1, 2), 0, n)
    series_upper = series_lower + 2 * F(1, 2) ** n
    assert max(lower, series_lower) <= min(upper, series_upper)
    checks += 1
    result = {'status': 'passed', 'exact_assertions': checks,
              'scope': 'Exact finite inequalities and independent quadrature consistency, not a proof of an infinite identity.',
              'example_at_half': {'series_terms': n, 'series_lower': series_lower,
                                  'series_upper': series_upper,
                                  'quadrature_lower': lower, 'quadrature_upper': upper},
              'derivative_examples': examples}
    out = Path(__file__).resolve().parents[1] / 'validation' / 'complex_integral_examples.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, default=str, indent=2) + '\n')
    print(json.dumps({'status': 'passed', 'exact_assertions': checks, 'output': str(out)}))


if __name__ == '__main__':
    main()
