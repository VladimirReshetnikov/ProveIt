#!/usr/bin/env python3
"""Exact coefficients and independent enumeration for the A189281 report.

Standard-library routines are exact. Functions prefixed by numerical_ require
mpmath and provide high-precision diagnostics, not interval certificates.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from functools import lru_cache
from math import factorial
from typing import Iterator


def auxiliary_coefficients(order: int) -> list[int]:
    if order < 0:
        raise ValueError("order must be nonnegative")
    a = [1, 3, 2, -1, 1, 2][:order + 1]
    for i in range(6, order + 1):
        numerator = -3*a[i-1]-(i+1)*a[i-2]-(i-5)*a[i-3]
        q, r = divmod(numerator, 2)
        if r:
            raise ArithmeticError("Auxiliary recurrence lost integrality")
        a.append(q)
    return a


def correction_coefficients(order: int) -> tuple[list[int], list[int]]:
    """Return (psi_0..psi_order, c_0..c_order) by shifted Stirling transform."""
    psi = auxiliary_coefficients(order)
    c = [1]
    row = [1]  # S(0, 0)
    for j in range(1, order+1):
        c.append(sum(psi[i]*row[i-1] for i in range(1, j+1)))
        nxt = [0]*(len(row)+1)
        for k in range(1, len(nxt)):
            nxt[k] = (row[k-1] if k-1 < len(row) else 0)
            if k < len(row):
                nxt[k] += k*row[k]
        row = nxt
    return psi, c


def partitions(n: int, lower: int = 1) -> Iterator[tuple[int, ...]]:
    if n == 0:
        yield ()
    else:
        for first in range(lower, n+1):
            for rest in partitions(n-first, first):
                yield (first,)+rest


@lru_cache(maxsize=None)
def path_profiles(n: int) -> tuple[tuple[tuple[int, ...], int], ...]:
    """Profile and number of ordered compositions for one n-vertex path."""
    result = []
    for parts in partitions(n):
        counts = Counter(parts)
        mult = factorial(len(parts))
        for v in counts.values():
            mult //= factorial(v)
        result.append((parts, mult))
    return tuple(result)


def forest_profiles(lengths: tuple[int, ...]) -> dict[tuple[int, ...], int]:
    acc: dict[tuple[int, ...], int] = {(): 1}
    for length in lengths:
        if length < 0:
            raise ValueError("negative path length")
        nxt: dict[tuple[int, ...], int] = defaultdict(int)
        for p, count in acc.items():
            for q, other in path_profiles(length):
                nxt[tuple(sorted(p+q))] += count*other
        acc = dict(nxt)
    return acc


def exact_a(n: int) -> int:
    """Independent signed matching-of-path-tilings formula, no guessed recurrence."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    counts = forest_profiles((n//2, n-n//2))
    answer = 0
    for profile, tilings in counts.items():
        weight = tilings*tilings
        for multiplicity in Counter(profile).values():
            weight *= factorial(multiplicity)
        answer += (-1)**(n-len(profile))*weight
    return answer


def numerical_dawson(z):
    import mpmath as mp
    z = mp.mpmathify(z)
    return z*mp.hyp1f1(1, mp.mpf('1.5'), -z*z)


def numerical_K(x):
    import mpmath as mp
    x = mp.mpmathify(x)
    return numerical_dawson((x+1)/2)+mp.exp(-x)*numerical_dawson((x-1)/2)


def numerical_H(x):
    """Dawson--Volterra formula; straight-segment primitives, diagnostic only."""
    import mpmath as mp
    x = mp.mpmathify(x)
    ik = x*mp.quad(lambda u: numerical_K(x*u), [0, 1])
    iik = x*x*mp.quad(lambda u: (1-u)*numerical_K(x*u), [0, 1])
    return (mp.diff(numerical_K, x, 2)+4*mp.diff(numerical_K, x)
            +6*numerical_K(x)+4*ik+iik)


def numerical_canonical(n):
    """One real quadrature for C_*(n), valid for real n>1.

    Integration by parts eliminates the Volterra primitives. A change of
    variables maps the integral to [0,1]. This is not interval arithmetic.
    """
    import mpmath as mp
    n = mp.mpf(n)
    if n <= 1:
        raise ValueError("The real integral requires n>1")
    def integrand(y):
        if y == 0:
            return mp.mpf(0)
        x = 1/y-1
        polynomial = ((n+1)*(n+2)*y**4+4*(n+1)*y**3+6*y*y
                      +4*y/n+1/(n*(n-1)))
        return numerical_K(x)*y**(n-3)*polynomial
    return mp.quad(integrand, [0, mp.mpf('.25'), mp.mpf('.5'), mp.mpf('.75'), 1])


def recurrence_rhs(n):
    """R(n), the inhomogeneous backward-shift equation, n>4."""
    return (2*n**3+3*n**2-7*n + 1/(n-4)+5/(n-3))
