#!/usr/bin/env python3
"""Exact derivation of the (p,q)=(10,16) zeta(2) reconstruction identity."""
from __future__ import annotations

from fractions import Fraction
from math import comb, factorial, gcd
from typing import Dict, List, Sequence


def bernoulli_numbers(nmax: int) -> list[Fraction]:
    b = [Fraction(0) for _ in range(nmax + 1)]
    b[0] = Fraction(1)
    for n in range(1, nmax + 1):
        b[n] = -sum(Fraction(comb(n + 1, k)) * b[k] for k in range(n)) / Fraction(n + 1)
    return b


def invert_matrix(a: Sequence[Sequence[Fraction]]) -> list[list[Fraction]]:
    n = len(a)
    aug = [list(row) + [Fraction(int(i == j)) for j in range(n)] for i, row in enumerate(a)]
    for k in range(n):
        pivot = next((r for r in range(k, n) if aug[r][k]), None)
        if pivot is None:
            raise ZeroDivisionError("singular matrix")
        if pivot != k:
            aug[k], aug[pivot] = aug[pivot], aug[k]
        pv = aug[k][k]
        aug[k] = [x / pv for x in aug[k]]
        for i in range(n):
            if i == k:
                continue
            c = aug[i][k]
            if c:
                aug[i] = [x - c * y for x, y in zip(aug[i], aug[k])]
    return [row[n:] for row in aug]


def source_matrix(a: int, b: int, bernoulli: Sequence[Fraction]) -> list[list[Fraction]]:
    out: list[list[Fraction]] = []
    for t in range(b):
        row: list[Fraction] = []
        for k in range(b):
            idx = t + k - a + 1
            if idx < 0:
                mu = Fraction(0)
            else:
                mu = bernoulli[2 * idx] / factorial(2 * idx)
            first = Fraction(factorial(2 * b + 2 * t - 2 * a + 1), factorial(2 * b - 2 * k))
            second = Fraction(0)
            if k < a:
                second = Fraction(factorial(2 * t + 1), factorial(2 * a - 2 * k))
            row.append(mu * (first + second))
        out.append(row)
    return out


def reconstruction_weights(a: int, b: int, zeta_index: int) -> list[Fraction]:
    bernoulli = bernoulli_numbers(4 * b + 4)
    matrix = source_matrix(a, b, bernoulli)
    inv = invert_matrix(matrix)
    max_r = 2 * b - 1
    weights = [Fraction(0) for _ in range(max_r + 1)]
    for t in range(b):
        j = b + t
        for r in range(j + 1):
            weights[r] += inv[zeta_index][t] * Fraction(comb(2 * j + 1, 2 * r), 2 ** (2 * (j - r)))
    return weights


def primitive_integer_row(weights: Sequence[Fraction]) -> tuple[int, list[int]]:
    from math import lcm
    den = 1
    for x in weights:
        den = lcm(den, x.denominator)
    nums = [x.numerator * (den // x.denominator) for x in weights]
    common = 0
    for n in nums:
        common = gcd(common, abs(n))
    if common > 1:
        nums = [n // common for n in nums]
        den //= common
    return den, nums


def rising(x: int, n: int) -> int:
    out = 1
    for j in range(n):
        out *= x + j
    return out


def bernoulli_half_even(m: int, bernoulli: Sequence[Fraction]) -> Fraction:
    if m == 0:
        return Fraction(1)
    return (Fraction(1, 2 ** (2 * m - 1)) - 1) * bernoulli[2 * m]


def tail_asymptotic_coefficient(s: int, m: int, bernoulli: Sequence[Fraction]) -> Fraction:
    if m == 0:
        return Fraction(1, s - 1)
    return bernoulli_half_even(m, bernoulli) * Fraction(rising(s, 2 * m - 1), factorial(2 * m))


def subtraction_polynomial(
    p: int,
    q: int,
    polynomial_coefficients: Sequence[Fraction],
) -> Dict[int, Fraction]:
    bernoulli = bernoulli_numbers(64)
    base = p + q - 2
    out: Dict[int, Fraction] = {}
    for r, coeff in enumerate(polynomial_coefficients):
        if not coeff:
            continue
        max_ell = (2 * r - base) // 2
        if max_ell < 0:
            continue
        for ell in range(max_ell + 1):
            product_coeff = sum(
                tail_asymptotic_coefficient(p, u, bernoulli)
                * tail_asymptotic_coefficient(q, ell - u, bernoulli)
                for u in range(ell + 1)
            )
            exponent = 2 * r - base - 2 * ell
            out[exponent] = out.get(exponent, Fraction(0)) + coeff * product_coeff
    return dict(sorted(out.items()))


def derive_identity() -> dict:
    a, b, k = 5, 8, 1
    weights = reconstruction_weights(a, b, k)
    denominator, numerators = primitive_integer_row(weights)
    normalized = [Fraction(n, denominator) for n in numerators]
    subtraction = subtraction_polynomial(10, 16, normalized)
    return {
        "a": a,
        "b": b,
        "p": 10,
        "q": 16,
        "zeta_index": k,
        "zeta_value": "zeta(2)",
        "polynomial_denominator": denominator,
        "polynomial_numerators": numerators,
        "subtraction": {
            str(e): {"numerator": c.numerator, "denominator": c.denominator}
            for e, c in subtraction.items()
        },
    }
