#!/usr/bin/env python3
"""Exact computations for Cigler's Conjecture 16.

Integers use Python's standard library. Symbolic polynomials, in verify.py,
use SymPy's exact ZZ[t] polynomial ring. No floating-point arithmetic is used.
"""
from __future__ import annotations

from math import comb
from typing import Any, Callable, Sequence

Scalar = Any


def validate_nonnegative(**values: int) -> None:
    for name, value in values.items():
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise ValueError(f"{name} must be a nonnegative integer")


def exact_div(a: Scalar, b: Scalar) -> Scalar:
    """Exact division in Z or a SymPy polynomial ring; reject a remainder."""
    if not b:
        raise ZeroDivisionError("zero divisor in exact division")
    if isinstance(a, int) and isinstance(b, int):
        q, r = divmod(a, b)
        if r:
            raise ArithmeticError("inexact integer division")
        return q
    return a.exquo(b)


def determinant(matrix: Sequence[Sequence[Scalar]], one: Scalar = 1) -> Scalar:
    """Bareiss determinant, with row pivoting and checked exact divisions."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("determinant requires a square matrix")
    if not n:
        return one
    a = [list(row) for row in matrix]
    previous = one
    sign = 1
    for k in range(n - 1):
        if not a[k][k]:
            pivot = next((r for r in range(k + 1, n) if a[r][k]), None)
            if pivot is None:
                return 0 * one
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        p = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = exact_div(a[i][j] * p - a[i][k] * a[k][j], previous)
        for i in range(k + 1, n):
            a[i][k] = 0 * one
        previous = p
    return sign * a[-1][-1]


def binomial(n: int, k: int) -> int:
    return comb(n, k) if 0 <= k <= n else 0


def cigler_moment(index: int, t: Scalar) -> Scalar:
    """Source equation (6), not a consequence of the conjectured formula."""
    validate_nonnegative(index=index)
    one = t ** 0
    if index == 0:
        return one
    return sum((binomial((index - 1) // 2, (j - 1) // 2)
                * binomial(index // 2, j // 2) * t ** (j - 1)
                for j in range(1, index + 1)), 0 * one)


def source_hankel(k: int, n: int, t: Scalar) -> Scalar:
    validate_nonnegative(k=k, n=n)
    c = [cigler_moment(r, t) for r in range(k + max(0, 2 * n - 1))]
    return determinant([[c[k + i + j] for j in range(n)] for i in range(n)], t ** 0)


def normalized_source(k: int, n: int, t: Scalar) -> Scalar:
    if k < 1:
        raise ValueError("the normalized theorem is for k >= 1")
    h = source_hankel(k, n, t)
    power = n * (n - 1) // 2
    return (-1) ** (k * power) * exact_div(h, t ** power)


def auxiliary_corner(a: int, m: int, t: Scalar, epsilon: int) -> Scalar:
    """det((M_epsilon**a)[0:m,0:m]), using banded multiplication.

    M_epsilon has diagonal 1+t^2, an extra epsilon*t at (0,0),
    and t on both adjacent diagonals. The finite truncation is exact:
    a steps starting below m cannot reach an index >= m+a.
    """
    validate_nonnegative(a=a, m=m)
    if epsilon not in (0, 1):
        raise ValueError("epsilon must be 0 or 1")
    one = t ** 0
    if not m or not a:
        return one
    size = m + a + 1  # one extra harmless boundary index
    columns = []
    for j in range(m):
        v = [0 * one for _ in range(size)]
        v[j] = one
        for _ in range(a):
            w = [0 * one for _ in range(size)]
            for h in range(size):
                w[h] += (1 + t * t + (epsilon * t if h == 0 else 0)) * v[h]
                if h:
                    w[h - 1] += t * v[h]
                if h + 1 < size:
                    w[h + 1] += t * v[h]
            v = w
        columns.append(v[:m])
    return determinant([[columns[j][i] for j in range(m)] for i in range(m)], one)


def alternant_numerator(a: int, m: int, t: Scalar, delta: int) -> Scalar:
    validate_nonnegative(a=a, m=m)
    if delta not in (0, 1):
        raise ValueError("delta must be 0 or 1")
    one = t ** 0

    def derivative_monomial(degree: int, order: int) -> Scalar:
        if degree < order:
            return 0 * one
        return comb(degree, order) * t ** (degree - order)

    return determinant([
        [derivative_monomial(j - 1, i - 1)
         - derivative_monomial(2 * m + 2 * a - j + delta, i - 1)
         for j in range(1, a + 1)]
        for i in range(1, a + 1)], one)


def auxiliary_closed(a: int, m: int, t: Scalar, epsilon: int) -> Scalar:
    """Small alternant formula. At t=+/-1 use auxiliary_corner instead."""
    if isinstance(t, int) and t in (-1, 1):
        return auxiliary_corner(a, m, t, epsilon)
    numerator = alternant_numerator(a, m, t, 1 - epsilon)
    denominator = ((1 - t) ** a * (1 - t * t) ** (a * (a - 1) // 2)
                   if epsilon else (1 - t * t) ** (a * (a + 1) // 2))
    return exact_div(numerator, denominator)


def parity_formula(k: int, n: int, t: Scalar,
                   auxiliary: Callable[..., Scalar] = auxiliary_corner) -> Scalar:
    validate_nonnegative(k=k, n=n)
    if k == 0:
        raise ValueError("the parity factorization requires k >= 1")
    a, m = k // 2, n // 2
    if k % 2:
        return auxiliary(a, m + n % 2, t, 1) * auxiliary(a, m, t, 0)
    if n % 2:
        return (1 + t) * auxiliary(a - 1, m + 1, t, 1) * auxiliary(a, m, t, 0)
    return auxiliary(a, m, t, 1) * auxiliary(a - 1, m, t, 0)


def stable_coefficient(k: int, degree: int) -> int:
    """[t^degree] 1/((1-t)^a (1-t^2)^b), for the parity of k."""
    validate_nonnegative(k=k, degree=degree)
    if k == 0:
        raise ValueError("k must be positive")
    a = k // 2
    b = a * a if k % 2 else a * (a - 1)
    if not a:
        return int(degree == 0)

    def weak_compositions(total: int, boxes: int) -> int:
        return comb(total + boxes - 1, boxes - 1) if boxes else int(total == 0)

    return sum(weak_compositions(j, b) * weak_compositions(degree - 2 * j, a)
               for j in range(degree // 2 + 1))


def schur_candidate(k: int, n: int, t: Scalar) -> Scalar:
    """EXPERIMENTAL stronger identity, not used in the article's proof."""
    validate_nonnegative(k=k, n=n)
    if not k:
        raise ValueError("k must be positive")
    a, b = k // 2, (k - 1) // 2
    one = t ** 0
    if not a:
        return one
    h = [one] + [0 * one] * (n + a)
    for x in [one] * a + [t] + [t * t] * b:
        for j in range(1, len(h)):
            h[j] += x * h[j - 1]
    return determinant([[h[n - i + j] if n - i + j >= 0 else 0 * one
                         for j in range(a)] for i in range(a)], one)
