#!/usr/bin/env python3
"""Exact and high-precision checks of the order-two moment-rank theorem.

The all-orders proof is in sections/03_moment_rank.tex.  This program checks its
normalizations, determinant formula, Padé contractions, rational extraction
rows, and two ordinary-series examples independently at finite orders.
It is not a replacement for the proof.

Usage: python verify_moment_rank.py --max-b 14 --output moment_rank_checks.json
Requirements: sympy, mpmath (only when --numerical is requested).
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp


def bernoulli_moment(n: int) -> sp.Expr:
    return sp.bernoulli(2 * n) / sp.factorial(2 * n)


def source_matrix(b: int) -> sp.Matrix:
    """Direct specialization of the source formula; no factorization used."""
    def entry(t: int, k: int) -> sp.Expr:
        d = 2 * (b + t) + 1
        p, q = 2, 2 * b
        e = d - p - q + 2 * k + 1
        if e < 0:
            return sp.S.Zero
        terms = [(d - q + 1, p - 2 * k),
                 (d - p + 1, q - 2 * k)]
        return sp.bernoulli(e) * sum(
            sp.binomial(upper, lower) / upper
            for upper, lower in terms if 2 <= lower <= upper
        )
    return sp.Matrix(b, b, entry)


def q_coeff(n: int, ell: int) -> sp.Expr:
    return (2 * sp.factorial(4 * n + 1 - 2 * ell)
            * sp.factorial(2 * n + 1)
            / (sp.factorial(4 * n + 2)
               * sp.factorial(2 * ell + 1)
               * sp.factorial(2 * n - 2 * ell)))


def rank_checks(b: int) -> dict:
    M = source_matrix(b)
    actual_det = sp.factor(M.det())
    claimed_det = ((-1) ** (b - 1) * (2 - sp.bernoulli(2 * b - 2))
                   / (2 ** b * sp.factorial(2 * b - 2)))
    assert actual_det == claimed_det

    H = sp.Matrix(b, b, lambda t, k: bernoulli_moment(t + k))
    rows = [sp.factorial(2 * b + 2 * t - 1) for t in range(b)]
    cols = [1 / sp.factorial(2 * b - 2 * k) for k in range(b)]
    rho = [sp.factorial(2 * b) * sp.factorial(2 * t + 1)
           / (2 * sp.factorial(2 * b + 2 * t - 1))
           for t in range(b)]
    u = sp.Matrix([bernoulli_moment(t) * rho[t] for t in range(b)])
    e0 = sp.eye(b)[:, 0]
    assert M == sp.diag(*rows) * (H + u * e0.T) * sp.diag(*cols)

    n = b - 1
    c = ((2 * n + 1) * sp.factorial(2 * n + 2)
         / sp.factorial(4 * n + 2))
    pade_row = sp.Matrix([[q_coeff(n, n - t) / c for t in range(b)]])
    assert pade_row * H == e0.T
    contraction = sp.factor((pade_row * u)[0])
    assert contraction == 1 - sp.bernoulli(2 * b - 2)

    extraction = sp.Matrix([[
        2 * sp.binomial(2 * b - 1, 2 * t)
        / ((2 * b - 1) * (2 - sp.bernoulli(2 * b - 2)))
        for t in range(b)
    ]])
    assert extraction * M == e0.T

    delta = sp.prod(
        sp.factorial(2 * j + 1) ** 2
        / (sp.factorial(4 * j + 2) * sp.factorial(4 * j + 3))
        for j in range(b - 1)
    )
    assert H.det() == (-1) ** (b - 1) * c * delta
    assert (sp.prod(rows) * sp.prod(cols) * H.det()
            == (-1) ** (b - 1)
            / (sp.Integer(2) ** b * sp.factorial(2 * b - 2)))

    return {"b": b, "p": 2, "q": 2 * b,
            "determinant": str(actual_det),
            "bernoulli_factor": str(2 - sp.bernoulli(2 * b - 2)),
            "all_checks_passed": True}


def pade_checks(n: int) -> None:
    coeffs = [q_coeff(n, ell) for ell in range(n + 1)]
    assert coeffs[0] == 1
    for r in range(n + 1, 2 * n + 1):
        assert sum(coeffs[ell] * bernoulli_moment(r - ell)
                   for ell in range(n + 1)) == 0
    leading = sum(coeffs[ell] * bernoulli_moment(2 * n + 1 - ell)
                  for ell in range(n + 1))
    assert (leading == sp.factorial(2 * n + 1) ** 2
            / (sp.factorial(4 * n + 2) * sp.factorial(4 * n + 3)))


def centered_tail_coefficient(s: int, h: int) -> sp.Expr:
    if h == 0:
        return sp.Rational(1, s - 1)
    return (sp.bernoulli(2 * h, sp.Rational(1, 2))
            * sp.rf(s, 2 * h - 1) / sp.factorial(2 * h))


def ordinary_polynomials(b: int):
    x = sp.Symbol("x")

    def primitive(y):
        return y ** (2 * b + 1) * (
            (1 + y) ** (2 * b - 1) + (1 - y) ** (2 * b - 1)
        ) / 2

    W = sp.Poly(sp.expand(primitive(x + sp.Rational(1, 2))
                         - primitive(x - sp.Rational(1, 2))), x)
    weights = [sum(
        sp.binomial(2 * b - 1, 2 * t)
        * sp.binomial(2 * b + 2 * t + 1, 2 * r)
        * sp.Integer(2) ** (-2 * (b + t - r))
        for t in range(b) if r <= b + t
    ) for r in range(2 * b)]
    assert all(W.nth(2 * r) == weights[r] for r in range(2 * b))

    def tail_product(h):
        return sum(centered_tail_coefficient(2, i)
                   * centered_tail_coefficient(2 * b, h - i)
                   for i in range(h + 1))

    R = sp.Poly(sp.expand(sum(
        weights[r] * tail_product(h) * x ** (2 * (r - b - h))
        for r in range(b, 2 * b) for h in range(r - b + 1)
    )), x)
    rhs = -sp.Rational(2 * b - 1, 4) * (2 - sp.bernoulli(2 * b - 2))
    scale = sp.ilcm(*[sp.denom(v) for v in W.all_coeffs()])
    return W, R, rhs, scale, tail_product


def numerical_series_check(b: int) -> dict:
    """Independent numerical check with 24-term asymptotic tail acceleration."""
    import mpmath as mp
    mp.mp.dps = 100
    W, R, rhs, _, tail_product = ordinary_polynomials(b)

    def mpq(value):
        a, d = sp.fraction(value)
        return mp.mpf(str(a)) / mp.mpf(str(d))

    w = [mpq(v) for v in W.all_coeffs()]
    r = [mpq(v) for v in R.all_coeffs()]
    cutoff, terms = 100, 24
    partial = mp.fsum(
        mp.polyval(w, mp.mpf(n) + mp.mpf("0.5"))
        * mp.zeta(2, n + 1) * mp.zeta(2 * b, n + 1)
        - mp.polyval(r, mp.mpf(n) + mp.mpf("0.5"))
        for n in range(cutoff)
    )
    tail = mp.mpf(0)
    for j in range(1, terms + 1):
        coefficient = sum(
            W.nth(2 * rr) * tail_product(rr - b + j)
            for rr in range(2 * b) if rr - b + j >= 0
        )
        tail += mpq(coefficient) * mp.zeta(2 * j, mp.mpf(cutoff) + mp.mpf("0.5"))
    residual = abs(partial + tail - mpq(rhs))
    assert residual < mp.mpf("1e-40"), (b, residual)
    return {"b": b, "partial_sum_cutoff": cutoff,
            "asymptotic_tail_terms": terms,
            "absolute_residual": mp.nstr(residual, 12),
            "interpretation": "numerical validation, not a certified bound"}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-b", type=int, default=12)
    parser.add_argument("--numerical", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.max_b < 2:
        raise SystemExit("--max-b must be at least 2")

    for n in range(args.max_b):
        pade_checks(n)
    result = {"proof": "sections/03_moment_rank.tex (all orders)",
              "finite_exact_checks": [rank_checks(b)
                                      for b in range(2, args.max_b + 1)]}
    examples = []
    for b in (2, 3, 4):
        W, R, rhs, scale, _ = ordinary_polynomials(b)
        examples.append({"b": b, "scale": str(scale),
                         "scaled_weight": str(sp.expand(scale * W.as_expr())),
                         "scaled_subtraction": str(sp.expand(scale * R.as_expr())),
                         "scaled_rhs": str(scale * rhs)})
    result["ordinary_series_examples"] = examples
    if args.numerical:
        result["numerical_checks"] = [numerical_series_check(b) for b in (2, 3)]
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
    print(output)


if __name__ == "__main__":
    main()
