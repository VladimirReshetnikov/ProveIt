#!/usr/bin/env python3
"""Exact finite checks for Surcomplex Analysis via Hahn-Supported Holomorphic Functions.

Run with Python 3 and SymPy:
    python verify_examples.py

These checks test selected finite algebraic truncations. They do not implement
surreal numbers and do not certify the article's infinite-support theorems.
"""
from __future__ import annotations

from fractions import Fraction
from math import factorial
from typing import Sequence

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("This script requires SymPy: python -m pip install sympy") from exc


def exponential_coefficients(a: Sequence[Fraction], degree: int) -> list[Fraction]:
    """Return exp(sum a[k] t**k) modulo t**(degree+1), assuming a[0] == 0."""
    if degree < 0 or not a or a[0] != 0:
        raise ValueError("A nonnegative degree and a zero constant coefficient are required")
    b = [Fraction(0) for _ in range(degree + 1)]
    b[0] = Fraction(1)
    for n in range(1, degree + 1):
        b[n] = sum(
            (k * a[k] * b[n - k] for k in range(1, min(n, len(a) - 1) + 1)),
            Fraction(0),
        ) / n
    return b


def check_simple_root(degree: int = 12) -> str:
    a = [Fraction(0)] + [
        Fraction((-1)**n * n**(n - 1), factorial(n))
        for n in range(1, degree + 1)
    ]
    e = exponential_coefficients(a, degree - 1)
    residual = [a[0]] + [a[n] + e[n - 1] for n in range(1, degree + 1)]
    if any(residual):
        raise AssertionError(f"Simple-root identity failed: {residual}")
    shown = ", ".join(str(c) for c in a[1:7])
    return f"PASS: z + t exp(z) = 0 modulo t^{degree + 1}; first coefficients: {shown}."


def check_preparation(order: int = 3) -> list[str]:
    if order != 3:
        raise ValueError("The independently specified reference coefficients use order 3")
    z, t = sp.symbols("z t")
    p: dict[int, sp.Expr] = {}
    v: dict[int, sp.Expr] = {}
    for n in range(1, order + 1):
        forcing = sp.exp(z) if n == 1 else sp.Integer(0)
        h = forcing - sum((p[k] * v[n - k] for k in range(1, n)), sp.Integer(0))
        p[n] = sp.expand(sp.series(h, z, 0, 2).removeO())
        v[n] = sp.cancel((h - p[n]) / z**2)

    expected = {
        1: 1 + z,
        2: -sp.Rational(1, 2) - sp.Rational(2, 3) * z,
        3: sp.Rational(11, 24) + sp.Rational(27, 40) * z,
    }
    for n in range(1, order + 1):
        if sp.simplify(p[n] - expected[n]) != 0:
            raise AssertionError(f"Unexpected prepared coefficient at t^{n}: {p[n]}")
        coefficient = p[n] + z**2 * v[n] + sum(
            (p[k] * v[n - k] for k in range(1, n)), sp.Integer(0)
        )
        target = sp.exp(z) if n == 1 else sp.Integer(0)
        if sp.simplify(coefficient - target) != 0:
            raise AssertionError(f"Prepared factorization failed at t^{n}")

    b0 = sp.expand(sum(p[n].coeff(z, 0) * t**n for n in p))
    b1 = sp.expand(sum(p[n].coeff(z, 1) * t**n for n in p))
    return [
        "PASS: exact analytic preparation factorization through t^3.",
        f"  b0 = {b0} + O(t^4)",
        f"  b1 = {b1} + O(t^4)",
    ]


def check_residues() -> str:
    z, q = sp.symbols("z q", nonzero=True)
    denominator = z**2 - q**2
    expected = {
        sp.Integer(1): (1 / (2 * q), -1 / (2 * q)),
        z: (sp.Rational(1, 2), sp.Rational(1, 2)),
        2 * z: (sp.Integer(1), sp.Integer(1)),
    }
    for numerator, targets in expected.items():
        # For a simple root r, Res N/P = N(r)/P'(r).
        actual = tuple(sp.simplify(numerator.subs(z, r) / (2 * r)) for r in (q, -q))
        if any(sp.simplify(a - b) != 0 for a, b in zip(actual, targets)):
            raise AssertionError(f"Residues failed for numerator {numerator}: {actual}")
    return "PASS: actual residues for 1/(z^2-q^2), z/(z^2-q^2), and 2z/(z^2-q^2)."


def main() -> None:
    lines = [
        "Exact symbolic verification of article examples",
        f"SymPy version: {sp.__version__}",
        "",
        check_simple_root(),
        *check_preparation(),
        check_residues(),
        "",
        "All checks passed. These are finite symbolic checks, not formal proofs of the general theory.",
    ]
    print("\n".join(lines))


if __name__ == "__main__":
    main()
