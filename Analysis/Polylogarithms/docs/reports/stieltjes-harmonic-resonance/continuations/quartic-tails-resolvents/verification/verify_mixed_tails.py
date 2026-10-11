#!/usr/bin/env python3
"""Exact and independent numerical checks for centered mixed harmonic tails.

Dependencies: Python 3, sympy, mpmath. Run from any directory.
Writes mixed_tail_results.json beside this script unless --output is provided.

The finite-head/Hurwitz-tail calculation does not use the new moment formula.
An analytic truncation envelope is computed separately. Floating-point
rounding is not enclosed, so these are diagnostics, not interval certificates.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import json
from pathlib import Path
import platform

import mpmath as mp
import sympy as sp

Z = sp.Function("Z")


@lru_cache(None)
def double_even_odd(p: int, b: int):
    """Classical odd-weight double-zeta reduction, outer order p even."""
    assert p >= 2 and p % 2 == 0 and b >= 1 and b % 2 == 1
    weight = p + b
    if b == 1:
        return sp.Rational(p, 2) * Z(weight) - sum(
            Z(2 * k) * Z(weight - 2 * k) for k in range(1, p // 2)
        )
    return sp.expand(
        sp.Rational(int(sp.binomial(weight, p)) - 1, 2) * Z(weight)
        + Z(p) * Z(b)
        - sum(
            (
                sp.binomial(weight - 2 * k - 1, b - 1)
                + sp.binomial(weight - 2 * k - 1, p - 1)
            )
            * Z(2 * k)
            * Z(weight - 2 * k)
            for k in range(1, (weight - 1) // 2)
        )
    )


def ordered_block(p: int, q: int, d: int):
    if d < q:
        return double_even_odd(p, q - d) + Z(p + q - d) / 2
    return sum(
        sp.binomial(d - q + 1, 2 * h)
        * sp.bernoulli(d - q + 1 - 2 * h)
        * Z(p - 2 * h)
        / sp.Integer(d - q + 1)
        for h in range(1, min((d - q + 1) // 2, p // 2 - 1) + 1)
    )


def rational_block(p: int, q: int, d: int):
    if d < p + q - 1:
        return sp.Integer(0)
    return -sp.bernoulli(d - p - q + 1) * (
        sp.binomial(d - q, p - 1) / sp.Integer(p)
        + sp.binomial(d - p, q - 1) / sp.Integer(q)
    ) / 2


@lru_cache(None)
def block(p: int, q: int, d: int):
    assert p % 2 == q % 2 == 0 and min(p, q) >= 2 and d >= 1 and d % 2
    return sp.expand(
        ordered_block(p, q, d) + ordered_block(q, p, d)
        + rational_block(p, q, d)
    )


@lru_cache(None)
def moment(p: int, q: int, r: int):
    return sp.expand(sum(
        sp.binomial(2 * r, 2 * j)
        * sp.bernoulli(2 * r - 2 * j, sp.Rational(1, 2))
        * block(p, q, 2 * j + 1) / sp.Integer(2 * j + 1)
        for j in range(r + 1)
    ))


def numeric(expr):
    if expr.func == Z:
        return mp.zeta(int(expr.args[0]))
    if expr.is_Rational:
        return mp.mpf(int(expr.p)) / int(expr.q)
    if expr.is_Add:
        return mp.fsum(numeric(a) for a in expr.args)
    if expr.is_Mul:
        return mp.fprod(numeric(a) for a in expr.args)
    if expr.is_Pow:
        return numeric(expr.base) ** int(expr.exp)
    raise TypeError(expr)


@lru_cache(None)
def centered_coeff(p: int, j: int):
    return (
        sp.binomial(p + 2 * j - 2, p - 2)
        * sp.bernoulli(2 * j, sp.Rational(1, 2))
        / sp.Integer(p - 1)
    )


def direct_moment(p: int, q: int, r: int, cutoff: int, order: int):
    cp = [numeric(centered_coeff(p, j)) for j in range(order + 1)]
    cq = [numeric(centered_coeff(q, j)) for j in range(order + 1)]
    product = [mp.fsum(
        cp[j] * cq[ell - j]
        for j in range(max(0, ell - order), min(order, ell) + 1)
    ) for ell in range(2 * order + 1)]
    start = max(0, r - (p + q) // 2 + 2)
    assert start <= order
    head = []
    for n in range(cutoff):
        x = mp.mpf(n) + mp.mpf("0.5")
        subtraction = mp.fsum(
            product[ell] * x ** (2 * r - p - q + 2 - 2 * ell)
            for ell in range(start)
        )
        head.append(x ** (2 * r) * mp.zeta(p, n + 1)
                    * mp.zeta(q, n + 1) - subtraction)
    a = mp.mpf(cutoff) + mp.mpf("0.5")
    tail = mp.fsum(
        product[ell] * mp.zeta(p + q - 2 + 2 * ell - 2 * r, a)
        for ell in range(start, 2 * order + 1)
    )
    rp = 2 * mp.factorial(p + 2 * order) / (
        mp.factorial(p - 1) * (2 * mp.pi) ** (2 * order + 2)
    )
    rq = 2 * mp.factorial(q + 2 * order) / (
        mp.factorial(q - 1) * (2 * mp.pi) ** (2 * order + 2)
    )
    bound_p = mp.fsum(abs(cp[j]) * a ** (-2 * j) for j in range(order + 1))
    bound_q = mp.fsum(abs(cq[j]) * a ** (-2 * j) for j in range(order + 1))
    prefactor = min(rp / (q - 1) + bound_p * rq,
                    rq / (p - 1) + bound_q * rp)
    envelope = prefactor * mp.zeta(p + q + 2 * order - 2 * r, a)
    return mp.fsum(head) + tail, envelope


def uncentered_tail(p: int, degree: int, z):
    return z ** (p - 1) / sp.Integer(p - 1) - z ** p / 2 + sum(
        sp.binomial(p + 2 * j - 2, p - 2) * sp.bernoulli(2 * j)
        * z ** (p + 2 * j - 1) / sp.Integer(p - 1)
        for j in range(1, degree + 1)
        if p + 2 * j - 1 <= degree
    )


def exact_checks():
    # Direct finite coefficient extraction, separate from the simplified formula.
    z = sp.Symbol("z")
    count = 0
    for p, q in [(2, 2), (2, 4), (4, 4), (2, 6), (4, 6), (6, 6)]:
        for d in range(1, 22, 2):
            ap = uncentered_tail(p, d, z)
            aq = uncentered_tail(q, d, z)
            raw = z ** (-d) * ap * aq
            for u, v, au in [(p, q, ap), (q, p, aq)]:
                m = d - v
                if m >= 0:
                    f = (sp.bernoulli(m + 1, 1 / z + 1)
                         - sp.bernoulli(m + 1)) / sp.Integer(m + 1)
                    raw += au * f
            constant = sp.expand(raw).coeff(z, 0)
            assert sp.simplify(constant - rational_block(p, q, d)) == 0
            count += 1
    for j in range(13):
        explicit = (
            sp.Rational(15, 2) * Z(5) - 3 * Z(2) * Z(3) if j == 0 else
            sp.Rational(3, 2) * Z(3) + Z(2) / 2 if j == 1 else
            sp.Rational(2 * j - 1, 2) * sp.bernoulli(2 * j - 2) * Z(2)
            - sp.Rational((2 * j - 3) * (2 * j * j - 3 * j + 7), 24)
            * sp.bernoulli(2 * j - 4)
        )
        assert sp.expand(block(2, 4, 2 * j + 1) - explicit) == 0
        count += 1
    for r in range(13):
        previous_square = 3 * sp.bernoulli(2 * r, sp.Rational(1, 2)) * Z(3)
        previous_square -= sum(
            sp.binomial(2 * r, 2 * j) * sp.Rational(2 * j - 1, 2 * j + 1)
            * sp.bernoulli(2 * r - 2 * j, sp.Rational(1, 2))
            * sp.bernoulli(2 * j - 2) / 2
            for j in range(1, r + 1)
        )
        assert sp.expand(moment(2, 2, r) - previous_square) == 0
        count += 1
    initial = [moment(2, 4, r) for r in range(4)]
    assert sp.expand(sum(a * b for a, b in zip([7, 412, 2000, 1344], initial)) + 88) == 0
    assert sp.expand(sum(a * b for a, b in zip([23, 524, -2480, -4032], initial)) - 176 * Z(2)) == 0
    count += 2
    return count


def generator_integral(p: int, q: int, t):
    def integral(a, b):
        # Scaling to a fixed interval also works for complex t.
        return t ** (a + b + 1) * mp.quad(
            lambda v: v ** a * (1 - v) ** b * mp.coth(t * v / 2)
            if v else mp.mpf(0), [0, 1]
        )
    parts = []
    for u, v in [(p, q), (q, p)]:
        polynomial = mp.fsum(
            numeric(double_even_odd(u, v - d) + Z(p + q - d) / 2)
            * t ** (d - 1) / mp.factorial(d)
            for d in range(1, v, 2)
        )
        middle = mp.fsum(
            mp.zeta(u - 2 * h) * integral(2 * h, v - 1)
            / (2 * t * mp.factorial(2 * h) * mp.factorial(v - 1))
            for h in range(1, u // 2)
        )
        last = -integral(u, v - 1) / (
            4 * t * mp.factorial(u) * mp.factorial(v - 1)
        )
        parts.append(polynomial + middle + last)
    return t / (2 * mp.sinh(t / 2)) * mp.fsum(parts)


def generator_24_polylog(t):
    li = {k: mp.polylog(k, mp.exp(-t)) for k in range(2, 7)}
    z = {k: mp.zeta(k) for k in range(2, 7)}
    inner = (
        4 * z[5] - 2 * z[2] * z[3] + t * t * z[3] / 6
        + 3 * t * z[4] / 4 + t ** 3 * z[2] / 48 - t ** 5 / 1440
        + (t * z[2] / 2 - t ** 3 / 48) * li[2]
        + (2 * z[2] - t * t / 6) * li[3] - t * li[4] - 4 * li[5]
        + 3 * z[2] * (li[4] - z[4]) / t
        + 15 * (z[6] - li[6]) / (2 * t)
    )
    return t / (2 * mp.sinh(t / 2)) * inner


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("mixed_tail_results.json"))
    args = parser.parse_args()
    mp.mp.dps = 110
    report = {
        "python": platform.python_version(), "sympy": sp.__version__,
        "mpmath": mp.__version__, "decimal_precision": mp.mp.dps,
        "exact_checks": exact_checks(), "moments": [], "generators": [],
        "interpretation": "Analytic proofs establish the identities. Numerical arithmetic is not interval-enclosed. Truncation envelopes below are proved analytic bounds."
    }
    for p, q in [(2, 2), (2, 4), (4, 4), (2, 6), (4, 6), (6, 6)]:
        for r in [0, 1, 2, 3, 5, 6]:
            value, envelope = direct_moment(p, q, r, cutoff=64, order=30)
            formula = numeric(moment(p, q, r))
            discrepancy = abs(value - formula)
            assert discrepancy < envelope * mp.mpf("1.001") + mp.mpf("1e-100")
            row = {"p": p, "q": q, "r": r, "cutoff": 64, "order": 30,
                   "formula": str(moment(p, q, r)),
                   "value": mp.nstr(formula, 60),
                   "absolute_discrepancy": mp.nstr(discrepancy, 12),
                   "analytic_truncation_envelope": mp.nstr(envelope, 12)}
            report["moments"].append(row)
            print(f"({p},{q}), r={r}: residual={mp.nstr(discrepancy, 6)}, envelope={mp.nstr(envelope, 6)}", flush=True)
    for p, q, t_string in [(2, 4, "0.7"), (2, 4, "1.3"), (4, 6, "0.8")]:
        t = mp.mpf(t_string)
        integral = generator_integral(p, q, t)
        series = mp.fsum(numeric(moment(p, q, r)) * t ** (2 * r)
                         / mp.factorial(2 * r) for r in range(41))
        row = {"p": p, "q": q, "t": t_string, "series_terms": 41,
               "series_integral_difference": mp.nstr(abs(series - integral), 12)}
        if (p, q) == (2, 4):
            row["integral_polylog_difference"] = mp.nstr(
                abs(integral - generator_24_polylog(t)), 12)
            assert abs(integral - generator_24_polylog(t)) < mp.mpf("1e-100")
        report["generators"].append(row)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"Saved {args.output}")


if __name__ == "__main__":
    main()
