#!/usr/bin/env python3
"""Exact rational verification of the asymptotic series in article.tex.

Python 3.10+, standard library only.  This verifies formal identities and
coefficients, not the analytic remainder estimates proved in the article.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from math import comb, factorial
from pathlib import Path


class SeriesRing:
    """Truncated rational power series modulo z**(degree+1)."""

    def __init__(self, degree: int):
        if degree < 1:
            raise ValueError("degree must be positive")
        self.degree = degree

    def const(self, value: int | F) -> list[F]:
        return [F(value)] + [F(0)] * self.degree

    def add(self, a: list[F], b: list[F]) -> list[F]:
        return [x + y for x, y in zip(a, b)]

    def scale(self, a: list[F], c: int | F) -> list[F]:
        return [c * x for x in a]

    def mul(self, a: list[F], b: list[F]) -> list[F]:
        out = self.const(0)
        for i, x in enumerate(a):
            if x:
                for j in range(self.degree + 1 - i):
                    out[i + j] += x * b[j]
        return out

    def power(self, a: list[F], n: int) -> list[F]:
        if n < 0:
            return self.power(self.inverse(a), -n)
        out = self.const(1)
        while n:
            if n & 1:
                out = self.mul(out, a)
            n >>= 1
            if n:
                a = self.mul(a, a)
        return out

    def inverse(self, a: list[F]) -> list[F]:
        if not a[0]:
            raise ValueError("cannot invert a series with zero constant term")
        out = self.const(1 / a[0])
        for n in range(1, self.degree + 1):
            out[n] = -sum(a[k] * out[n-k] for k in range(1, n+1)) / a[0]
        return out

    def shift(self, a: list[F], j: int) -> list[F]:
        """Return a(z/(1-j*z)); j may be negative."""
        out = self.const(a[0])
        for s in range(1, self.degree + 1):
            for t in range(self.degree + 1 - s):
                out[s+t] += a[s] * comb(s+t-1, t) * j**t
        return out

    def log(self, a: list[F]) -> list[F]:
        if a[0] != 1:
            raise ValueError("formal logarithm requires constant term one")
        derivative = self.const(0)
        for k in range(self.degree):
            derivative[k] = (k+1) * a[k+1]
        quotient = self.mul(derivative, self.inverse(a))
        out = self.const(0)
        for n in range(1, self.degree+1):
            out[n] = quotient[n-1] / n
        return out

    def exp(self, a: list[F]) -> list[F]:
        if a[0] != 0:
            raise ValueError("formal exponential requires constant term zero")
        out = self.const(1)
        for n in range(1, self.degree+1):
            out[n] = sum(k*a[k]*out[n-k] for k in range(1, n+1)) / n
        return out

    def rhs(self, r: list[F]) -> list[F]:
        """Right side of the article's formal equation for R."""
        out = self.const(0)
        k = 1
        while 2**k-k-1 <= self.degree:
            leading_degree = 2**k-k-1
            numerator, denominator = self.const(1), self.const(1)
            for h in range(k):
                linear = self.const(1)
                linear[1] = F(-h)
                numerator = self.mul(numerator, linear)
            for j in range(1, k):
                linear = self.const(1)
                linear[1] = F(-j)
                factor = self.mul(linear, self.shift(r, j))
                denominator = self.mul(denominator, self.power(factor, 2**j))
            term = self.mul(numerator, self.inverse(denominator))
            coefficient = F((-1)**(k+1), factorial(k))
            for d in range(self.degree+1-leading_degree):
                out[d+leading_degree] += coefficient * term[d]
            k += 1
        return out


def compute(degree: int) -> dict:
    ring = SeriesRing(degree)
    r = ring.const(1)
    for _ in range(degree + 1):
        r = ring.rhs(r)
    assert r == ring.rhs(r), "formal fixed point failed"
    logr = ring.log(r)
    # M_s = sum_{j>=1} j**s / 2**j.  The recurrence follows by shifting j.
    moments = [1]
    for s in range(1, degree+1):
        moments.append(2 + sum(comb(s, k)*moments[k] for k in range(1, s)))
    c = ring.const(0)
    for s in range(1, degree+1):
        coefficient = F((-1)**(s+1) * moments[s], s)
        for t in range(1, s+1):
            coefficient += logr[t] * (-1)**(s-t) * comb(s-1, s-t) * moments[s-t]
        c[s] = -coefficient
    multiplicative = ring.exp(c)
    assert ring.log(multiplicative) == c, "exp/log round trip failed"
    expected_r = [F(1), F(-1, 2), F(-1), F(-23, 8)]
    expected_c = [F(0), F(-3, 2), F(25, 8), F(-27, 4)]
    expected_a = [F(1), F(-3, 2), F(17, 4), F(-12)]
    stop = min(degree+1, 4)
    assert r[:stop] == expected_r[:stop]
    assert c[:stop] == expected_c[:stop]
    assert multiplicative[:stop] == expected_a[:stop]
    return {
        "arithmetic": "exact fractions.Fraction; no floating-point operations",
        "degree": degree,
        "R_coefficients_starting_degree_zero": list(map(str, r)),
        "log_R_coefficients_starting_degree_zero": list(map(str, logr)),
        "geometric_moments_starting_degree_zero": moments,
        "C_log_correction_coefficients_starting_degree_zero": list(map(str, c)),
        "exp_C_multiplicative_coefficients_starting_degree_zero": list(map(str, multiplicative)),
        "checks": ["formal R fixed point", "exp/log round trip", "all displayed first-three correction coefficients"],
        "scope": "Formal identities only. Analytic remainder estimates are proved in article.tex, not certified by this script."
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, default=10)
    parser.add_argument("--output", type=Path, default=Path("formal_series_report.json"))
    args = parser.parse_args()
    if not 1 <= args.degree <= 30:
        parser.error("degree must be between 1 and 30")
    report = compute(args.degree)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("Exact formal-series checks passed.")
    print("R =", report["R_coefficients_starting_degree_zero"])
    print("C =", report["C_log_correction_coefficients_starting_degree_zero"])
    print("exp(C) =", report["exp_C_multiplicative_coefficients_starting_degree_zero"])
    print(f"Report: {args.output}")


if __name__ == "__main__":
    main()
