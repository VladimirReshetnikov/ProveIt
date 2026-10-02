#!/usr/bin/env python3
"""Evaluate the finite two-neighborhood formula of Theorem 4.1.

Cumulants are first computed with exact rational arithmetic. Gaussian/Hermite
expressions are evaluated numerically; this is not interval arithmetic.
The theorem's uniform error is ABSOLUTE, not relative at arbitrary tail k.
Increasing the asymptotic order at fixed n need not improve an approximation.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import math
from typing import Iterator, Sequence
import mpmath as mp


def cumulants_from_moments(moments: Sequence[Fraction]) -> list[Fraction]:
    result = [Fraction(0)]
    for r in range(1, len(moments)):
        result.append(moments[r] - sum(
            (math.comb(r - 1, ell - 1) * result[ell] * moments[r - ell]
             for ell in range(1, r)), Fraction(0)))
    return result


def cumulant_lists(n: int, order: int) -> tuple[list[Fraction], list[Fraction]]:
    """Exact cumulants of P_n(e^t)/(n+1)! and of B_n(t)."""
    if n < 2 or order < 2:
        raise ValueError("Require n >= 2 and order >= 2.")
    plus = [Fraction(0)] * (order + 1)
    # (exp(t)-1)/t is the uniform[0,1] mgf, with raw moment 1/(r+1).
    minus = cumulants_from_moments([Fraction(1, r + 1) for r in range(order + 1)])
    power_sums = [0] * (order + 1)
    for j in range(1, n + 1):
        for r in range(1, order + 1):
            power_sums[r] += (2 * j - 1) ** r
        plus_moments = [Fraction(1)] + [
            Fraction(power_sums[r], j + 1) for r in range(1, order + 1)]
        one = cumulants_from_moments(plus_moments)
        for r in range(1, order + 1):
            plus[r] += one[r]
        if j >= 2:
            signed_moments = [Fraction(1)] + [
                Fraction(power_sums[r], j - 1) for r in range(1, order + 1)]
            one_signed = cumulants_from_moments(signed_moments)
            for r in range(1, order + 1):
                minus[r] += one_signed[r]
    return plus, minus


def multi_indices(budget: int) -> Iterator[tuple[int, ...]]:
    """Yield (m_3,...,m_(R+2)) with sum((r-2)*m_r) <= R."""
    def visit(weight: int, remaining: int, prefix: tuple[int, ...]):
        if weight > budget:
            yield prefix
            return
        for multiplicity in range(remaining // weight + 1):
            yield from visit(weight + 1, remaining - multiplicity * weight,
                             prefix + (multiplicity,))
    if budget < 0:
        raise ValueError("Expansion budget R must be nonnegative.")
    yield from visit(1, budget, ())


def as_mpf(value: Fraction):
    return mp.mpf(value.numerator) / value.denominator


def gaussian_hermite_sum(k: int, cumulants: Sequence[Fraction], budget: int, extra: int):
    mean = as_mpf(cumulants[1])
    variance = as_mpf(cumulants[2])
    if variance <= 0:
        raise ValueError("The second-neighborhood variance must be positive; use larger n.")
    sigma = mp.sqrt(variance)
    z = (k - mean) / sigma
    maximum_degree = 3 * budget + extra
    hermite = [mp.mpf(1), z]
    for degree in range(2, maximum_degree + 1):
        hermite.append(z * hermite[-1] - (degree - 1) * hermite[-2])
    standardized = {
        r: as_mpf(cumulants[r]) / (math.factorial(r) * sigma ** r)
        for r in range(3, budget + 3)
    }
    total = mp.mpf(0)
    for index in multi_indices(budget):
        degree = sum(r * m for r, m in enumerate(index, start=3))
        coefficient = mp.mpf(1)
        for r, multiplicity in enumerate(index, start=3):
            if multiplicity:
                coefficient *= standardized[r] ** multiplicity / math.factorial(multiplicity)
        total += coefficient * hermite[degree + extra]
    return mp.exp(-z * z / 2) * total / (mp.sqrt(2 * mp.pi) * sigma ** (1 + extra))


def approximation(n: int, k: int, budget: int):
    plus, minus = cumulant_lists(n, budget + 2)
    main = gaussian_hermite_sum(k, plus, budget, 0)
    secondary = ((-1) ** (n + k) / mp.mpf(n * (n + 1))
                 * gaussian_hermite_sum(k, minus, budget, 1))
    return main, secondary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=100)
    parser.add_argument("--k", type=int, default=None,
                        help="Default: integer nearest the mean, not a claimed exact mode.")
    parser.add_argument("--order", type=int, default=8, help="Weight budget R in Theorem 4.1.")
    parser.add_argument("--digits", type=int, default=70)
    parser.add_argument("--check", action="store_true", help="Compute the exact coefficient as a check.")
    args = parser.parse_args()
    if args.digits < 40:
        parser.error("--digits must be at least 40")
    mp.mp.dps = args.digits
    k = args.k
    if k is None:
        mean = (Fraction(args.n * (args.n - 1), 2)
                + sum((Fraction(1, j) for j in range(1, args.n + 2)), Fraction()) - 1)
        k = math.floor(mean + Fraction(1, 2))
    main, secondary = approximation(args.n, k, args.order)
    print(f"n={args.n}, k={k}, R={args.order}, digits={args.digits}")
    print("Principal probability contribution:", mp.nstr(main, 40))
    print("Secondary probability contribution:", mp.nstr(secondary, 40))
    print("Two-neighborhood probability:", mp.nstr(main + secondary, 40))
    if args.check:
        from verify import next_row
        row = [1]
        for n in range(1, args.n + 1):
            row = next_row(row, n)
        value = row[k] if 0 <= k < len(row) else 0
        exact = mp.mpf(value) / math.factorial(args.n + 1)
        print("Exact coefficient probability (numerical):", mp.nstr(exact, 40))
        print("Absolute error:", mp.nstr(main + secondary - exact, 30))
        if value:
            print("Relative error:", mp.nstr((main + secondary - exact) / exact, 30))
    print("Numerical values, not certified intervals; see the theorem for asymptotic scope.")
