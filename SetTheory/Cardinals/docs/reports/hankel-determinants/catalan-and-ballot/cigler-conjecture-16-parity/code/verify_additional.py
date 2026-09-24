#!/usr/bin/env python3
"""Supplementary exact checks for the recurrence and t=1 product formulas.

This checks consequences separately from the main Conjecture 16 regression
suite. No floating-point arithmetic or guessed recurrence is used.
"""
from __future__ import annotations

import json
import platform
import time
from fractions import Fraction
from pathlib import Path

from hankel import auxiliary_closed, auxiliary_corner, parity_formula


def product_at_one(a: int, m: int, epsilon: int) -> int:
    value = Fraction(1)
    for r in range(1, a + 1):
        value *= Fraction(2 * m + 2 * r - 1, 2 * r - 1) if epsilon else Fraction(m + r, r)
        for s in range(r + 1, a + 1):
            value *= Fraction(2 * m + r + s - epsilon, r + s - epsilon)
    if value.denominator != 1:
        raise ArithmeticError('nonintegral product at t=1')
    return value.numerator


def recurrence_polynomial(k: int, t: int) -> list[int]:
    """Ascending coefficients of the claimed polynomial in E^2."""
    a = k // 2
    d = a * (a - 1) if k % 2 else (a - 1) ** 2
    coefficients = [1]
    for q in range(k):
        eigenvalue = t ** (2 * q)
        for _ in range(d + 1):
            expanded = [0] * (len(coefficients) + 1)
            for j, coefficient in enumerate(coefficients):
                expanded[j] -= eigenvalue * coefficient
                expanded[j + 1] += coefficient
            coefficients = expanded
    return coefficients


def main() -> None:
    if not __debug__:
        raise RuntimeError('Run without -O: the verification suite uses assertions.')
    start = time.monotonic()
    count_one = 0
    for a in range(9):
        for m in range(13):
            for epsilon in (0, 1):
                assert product_at_one(a, m, epsilon) == auxiliary_corner(a, m, 1, epsilon)
                count_one += 1
    print(f'PASS: {count_one} removable-specialization product formulas at t=1', flush=True)

    count_recurrence = 0
    for k in range(2, 9):
        for tv in (-2, 2, 3):
            polynomial = recurrence_polynomial(k, tv)
            order = 2 * (len(polynomial) - 1)
            terms = [parity_formula(k, n, tv, auxiliary_closed) for n in range(order + 6)]
            for start_index in range(6):
                residual = sum(c * terms[start_index + 2 * j]
                               for j, c in enumerate(polynomial))
                assert residual == 0, (k, tv, start_index, residual)
                count_recurrence += 1
    print(f'PASS: {count_recurrence} exact recurrence residuals (both parities)', flush=True)
    result = {
        'status': 'all supplementary checks passed',
        'python': platform.python_version(),
        'arithmetic': 'exact integers and rational numbers; no floating point',
        'ranges': {
            'specialization': '0<=a<=8, 0<=m<=12, epsilon=0,1; t=1',
            'recurrence': '2<=k<=8, t=-2,2,3, starting index n=0,...,5'},
        'counts': {'product_at_one': count_one, 'recurrence_residuals': count_recurrence},
        'elapsed_seconds': round(time.monotonic() - start, 3),
        'scope': 'Finite checks of Appendix A and Proposition 9.1; not proofs.'}
    destination = Path(__file__).resolve().parents[1] / 'data' / 'additional_verification.json'
    destination.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
