#!/usr/bin/env python3
"""Exact finite regression checks for the nonlinear two-scale example.

All identities are checked in Q(i)[u]/(u^N), with rational exponents of
principal units computed by the finite binomial formula. These checks do not
verify the infinite Hahn, maximality, class-theoretic, or cardinality proofs.

Usage: python3 code/verify_finite.py --order 12 --output data/verification.json
Requires only Python's standard library (3.10 or later).
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path
from typing import TypeAlias

Gaussian: TypeAlias = tuple[F, F]
Series: TypeAlias = tuple[Gaussian, ...]
ZERO: Gaussian = (F(0), F(0))
ONE: Gaussian = (F(1), F(0))
I: Gaussian = (F(0), F(1))


def gadd(x: Gaussian, y: Gaussian) -> Gaussian:
    return x[0] + y[0], x[1] + y[1]


def gneg(x: Gaussian) -> Gaussian:
    return -x[0], -x[1]


def gmul(x: Gaussian, y: Gaussian) -> Gaussian:
    return x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0]


def constant(x: Gaussian, n: int) -> Series:
    return (x,) + (ZERO,) * (n - 1)


def add(x: Series, y: Series) -> Series:
    if len(x) != len(y):
        raise ValueError("Truncation orders differ")
    return tuple(gadd(a, b) for a, b in zip(x, y))


def scale(x: Series, q: F) -> Series:
    return tuple((q * a, q * b) for a, b in x)


def mul(x: Series, y: Series) -> Series:
    if len(x) != len(y):
        raise ValueError("Truncation orders differ")
    n = len(x)
    out = [ZERO] * n
    for j, a in enumerate(x):
        if a == ZERO:
            continue
        for k in range(n - j):
            if y[k] != ZERO:
                out[j + k] = gadd(out[j + k], gmul(a, y[k]))
    return tuple(out)


def conjugate(x: Series) -> Series:
    return tuple((a, -b) for a, b in x)


def unit_pow(x: Series, q: F) -> Series:
    """The unique q-th binomial power of a principal unit, modulo u^N."""
    if x[0] != ONE:
        raise ValueError("unit_pow requires constant coefficient exactly one")
    n = len(x)
    r = add(x, constant(gneg(ONE), n))
    term = constant(ONE, n)
    result = term
    binomial = F(1)
    for j in range(1, n):
        term = mul(term, r)
        binomial *= (q - (j - 1)) / j
        result = add(result, scale(term, binomial))
    return result


def serialized(x: Series) -> list[dict[str, str]]:
    return [{"real": str(a), "imaginary": str(b)} for a, b in x]


def run(n: int) -> dict[str, object]:
    if n < 5 or n > 30:
        raise ValueError("Use a truncation order from 5 through 30")
    unit = constant(ONE, n)
    plus = (ONE, I) + (ZERO,) * (n - 2)
    minus = conjugate(plus)
    w = mul(plus, unit_pow(minus, F(-1)))
    exponents = sorted({F(a, b) for a in range(-4, 5) for b in range(1, 5)})
    checks: dict[str, int] = {}

    def check(name: str, lhs: object, rhs: object) -> None:
        if lhs != rhs:
            raise AssertionError(f"Failed {name}: {lhs!r} != {rhs!r}")
        checks[name] = checks.get(name, 0) + 1

    check("phase_unit_inverse", mul(w, conjugate(w)), unit)
    check("phase_expansion", w[:5], (ONE, (F(0), F(2)), (F(-2), F(0)),
                                      (F(0), F(-2)), (F(2), F(0))))
    all_powers = {q: unit_pow(w, q) for q in exponents}
    all_half_powers = {q: unit_pow(w, q / 2) for q in exponents}
    binomial_plus = {q: unit_pow(plus, q) for q in exponents}
    binomial_minus = {q: unit_pow(minus, q) for q in exponents}
    sum_powers = {q + r: unit_pow(w, q + r)
                  for q in exponents for r in exponents}

    # For each q, P(z^q)=z^q (1+iu)^q and sigma(z^q)=z^q W^q.
    # H(z^q)=z^q W^(q/2). These are coefficient-factor identities.
    for q in exponents:
        wq = all_powers[q]
        hq = all_half_powers[q]
        check("sigma_squared", mul(wq, conjugate(wq)), unit)
        check("norm_section_invariant", mul(wq, conjugate(hq)), hq)
        check("norm_section_squares", mul(hq, hq), wq)
        check("conjugacy_factor", mul(mul(unit_pow(w, -q / 2), wq),
                                      conjugate(hq)), unit)
        check("P_conjugacy_factor", mul(binomial_plus[q],
                                        unit_pow(binomial_minus[q], F(-1))), wq)
        check("inverse_H", mul(hq, unit_pow(w, -q / 2)), unit)
        check("constant_coefficient", hq[0], ONE)
        for r in exponents:
            check("section_multiplicativity", mul(wq, all_powers[r]),
                  sum_powers[q + r])

    # Multiplicativity of sigma on finitely supported z-Laurent expressions.
    # A sparse expression is {outer exponent: inner truncated series}.
    def sparse_mul(x: dict[F, Series], y: dict[F, Series]) -> dict[F, Series]:
        out: dict[F, Series] = {}
        for a, ax in x.items():
            for b, by in y.items():
                out[a + b] = add(out.get(a + b, constant(ZERO, n)), mul(ax, by))
        return {a: s for a, s in out.items() if s != constant(ZERO, n)}

    def sigma(x: dict[F, Series]) -> dict[F, Series]:
        return {a: mul(conjugate(s), unit_pow(w, a)) for a, s in x.items()}

    samples = [
        {F(-1): plus, F(0): constant(I, n), F(1, 2): minus},
        {F(-3, 2): w, F(2): add(plus, minus)},
        {F(-2): constant((F(3), F(-2)), n), F(1): w},
    ]
    for x in samples:
        check("sparse_involution", sigma(sigma(x)), x)
        for y in samples:
            check("sparse_multiplicativity", sigma(sparse_mul(x, y)),
                  sparse_mul(sigma(x), sigma(y)))

    # Rational parameters keep the negative lexicographic cone under the
    # shifts which occur in the example; outer exponent zero is unchanged.
    for a in exponents:
        for b in exponents:
            if (a, b) < (F(0), F(0)):
                offsets = range(n) if a != 0 else range(1)
                for j in offsets:
                    check("negative_support_finite_window", (a, b + j) < (0, 0), True)

    return {
        "status": "passed",
        "arithmetic": "exact Q(i)[u]/(u^N)",
        "truncation_order_N": n,
        "rational_exponents": [str(q) for q in exponents],
        "counts_by_family": checks,
        "total_assertions": sum(checks.values()),
        "W_coefficients": serialized(w),
        "scope": (
            "Finite polynomial and binomial regression checks only. "
            "Not a verification of Hahn summability, spherical completeness, "
            "class-sized constructions, the main theorem, or cardinalities."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=12)
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()
    report = run(args.order)
    text = json.dumps(report, indent=2)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
