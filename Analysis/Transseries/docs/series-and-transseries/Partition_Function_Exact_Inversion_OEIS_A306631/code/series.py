#!/usr/bin/env python3
"""Exact rational coefficients for the two inverse partition constructions.

The mathematical recurrences and convergence proofs are in article.tex.
This script also substitutes the computed coefficients into both defining
logarithmic equations and checks that every retained coefficient vanishes.
No third-party package is required.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

Polynomial = list[F]


def mul(a: Polynomial, b: Polynomial, order: int) -> Polynomial:
    """Multiply power series, retaining degrees 0 through order."""
    result = [F(0)] * (order + 1)
    for i, x in enumerate(a):
        if not x or i > order:
            continue
        for j, y in enumerate(b[:order - i + 1]):
            if y:
                result[i + j] += x * y
    return result


def power(a: Polynomial, exponent: int, order: int) -> Polynomial:
    if exponent < 0 or order < 0:
        raise ValueError('Exponent and truncation order must be nonnegative.')
    result = [F(1)] + [F(0)] * order
    for _ in range(exponent):
        result = mul(result, a, order)
    return result


def log_one_plus(a: Polynomial, order: int) -> Polynomial:
    """Return log(1+a) modulo z**(order+1), for a[0] == 0."""
    if not a or a[0] != 0:
        raise ValueError('The logarithm argument must have zero constant term.')
    result = [F(0)] * (order + 1)
    a_power = [F(1)] + [F(0)] * order
    for k in range(1, order + 1):
        a_power = mul(a_power, a, order)
        multiplier = F((-1) ** (k + 1), k)
        for j in range(order + 1):
            result[j] += multiplier * a_power[j]
    return result


def coefficients(order: int) -> tuple[Polynomial, Polynomial]:
    """Return v_j and bias coefficients w_j; the stored w_0 is zero."""
    if order < 0:
        raise ValueError('Order must be nonnegative.')
    v = [F(1)] + [F(0)] * order
    for j in range(1, order + 1):
        v[j] = F(1, j + 1) + sum(
            (F(2, k) * power(v, k, j)[j - 2 * k + 1]
             for k in range(1, (j + 1) // 2 + 1)), F(0))
    square = mul(v, v, order)
    bias = [F(0)] + [2 * v[j] - (square[j - 2] if j >= 2 else 0)
                     for j in range(1, order + 1)]
    return v, bias


def inverse_coefficients(order: int) -> tuple[Polynomial, Polynomial]:
    """Return q_j and target-side inverse corrections r_j; r_0 is zero."""
    if order < 0:
        raise ValueError('Order must be nonnegative.')
    q = [F(1)] + [F(0)] * order
    for j in range(1, order + 1):
        a = [F(0), F(0)] + q[:j]
        b = a.copy()
        b[1] -= 1
        log_a = log_one_plus(a, j + 1)
        log_b = log_one_plus(b, j + 1)
        q[j] = 3 * log_a[j + 1] - log_b[j + 1]
    square = mul(q, q, order)
    inverse = [F(0)] + [2 * q[j] + (square[j - 2] if j >= 2 else 0)
                        for j in range(1, order + 1)]
    return q, inverse


def verify_equations(v: Polynomial, q: Polynomial) -> int:
    """Check both implicit equations through degree len(v), exactly."""
    if len(v) != len(q):
        raise ValueError('Both coefficient lists must have the same length.')
    degree = len(v)
    minus_z = [F(0), F(-1)] + [F(0)] * (degree - 1)
    minus_z2v = [F(0), F(0)] + [-x for x in v[:-1]]
    log_first = log_one_plus(minus_z, degree)
    log_second = log_one_plus(minus_z2v, degree)
    z_v = [F(0)] + v
    if any(z_v[j] + log_first[j] + 2 * log_second[j]
           for j in range(degree + 1)):
        raise ArithmeticError('The v equation has a nonzero retained residual.')

    z2q = [F(0), F(0)] + q[:-1]
    minus_z_plus_z2q = z2q.copy()
    minus_z_plus_z2q[1] -= 1
    log_first = log_one_plus(z2q, degree)
    log_second = log_one_plus(minus_z_plus_z2q, degree)
    z_q = [F(0)] + q
    if any(z_q[j] - 3 * log_first[j] + log_second[j]
           for j in range(degree + 1)):
        raise ArithmeticError('The q equation has a nonzero retained residual.')
    return degree


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=12)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if not 1 <= args.order <= 40:
        parser.error('The command-line order must be between 1 and 40.')
    v, w = coefficients(args.order)
    q, r = inverse_coefficients(args.order)
    verified_degree = verify_equations(v, q)
    result = {
        'order': args.order,
        'exact_equations_verified_through_degree': verified_degree,
        'v': [str(x) for x in v],
        'bias_w': [str(x) for x in w],
        'inverse_q': [str(x) for x in q],
        'inverse_r': [str(x) for x in r],
    }
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
