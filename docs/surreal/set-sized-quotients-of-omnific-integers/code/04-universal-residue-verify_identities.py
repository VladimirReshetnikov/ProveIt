#!/usr/bin/env python3
"""Exact finite illustrations for the accompanying surreal-arithmetic article.

This program is not a verifier for infinite Hahn identities or class-size
statements. It checks finite sparse-series identities over Q with exponent
group Q x Q in lexicographic order. Only the Python standard library is used.
Run with Python 3.9 or later; the output is deterministic.
"""
from __future__ import annotations

import json
import random
from fractions import Fraction
from pathlib import Path
from typing import Dict, Tuple

Exponent = Tuple[Fraction, Fraction]
Series = Dict[Exponent, Fraction]
ZERO_EXP: Exponent = (Fraction(0), Fraction(0))


def exp_add(x: Exponent, y: Exponent) -> Exponent:
    return x[0] + y[0], x[1] + y[1]


def exp_neg(x: Exponent) -> Exponent:
    return -x[0], -x[1]


def exp_sub(x: Exponent, y: Exponent) -> Exponent:
    return exp_add(x, exp_neg(y))


def exp_scale(n: int, x: Exponent) -> Exponent:
    return n * x[0], n * x[1]


def normalized(terms: Series) -> Series:
    return {exponent: coefficient for exponent, coefficient in terms.items()
            if coefficient != 0}


def series_add(x: Series, y: Series) -> Series:
    result = dict(x)
    for exponent, coefficient in y.items():
        result[exponent] = result.get(exponent, Fraction(0)) + coefficient
    return normalized(result)


def series_neg(x: Series) -> Series:
    return {exponent: -coefficient for exponent, coefficient in x.items()}


def series_sub(x: Series, y: Series) -> Series:
    return series_add(x, series_neg(y))


def series_mul(x: Series, y: Series) -> Series:
    result: Series = {}
    for a, c in x.items():
        for b, d in y.items():
            exponent = exp_add(a, b)
            result[exponent] = result.get(exponent, Fraction(0)) + c * d
    return normalized(result)


def monomial(exponent: Exponent, coefficient: Fraction = Fraction(1)) -> Series:
    return {exponent: coefficient} if coefficient else {}


def constant_coefficient(x: Series) -> Fraction:
    return x.get(ZERO_EXP, Fraction(0))


def augmentation(x: Series) -> Fraction:
    return sum(x.values(), Fraction(0))


def check(condition: bool, label: str) -> None:
    # Deliberately not Python assert: checks remain enabled with python -O.
    if not condition:
        raise AssertionError(label)


def random_series(rng: random.Random, sign: int) -> Series:
    """Generate finite nonnegative, nonpositive, or mixed support."""
    terms: Series = {}
    for _ in range(rng.randint(1, 10)):
        first = Fraction(rng.randint(0, 4), rng.randint(1, 5))
        second = Fraction(rng.randint(0 if first == 0 else -5, 5),
                          rng.randint(1, 5))
        exponent = (first, second)
        if sign == -1 or (sign == 0 and rng.choice((False, True))):
            exponent = exp_neg(exponent)
        coefficient = Fraction(rng.randint(-9, 9), rng.randint(1, 7))
        terms[exponent] = terms.get(exponent, Fraction(0)) + coefficient
    # Include a possibly nonzero constant to exercise cross terms.
    terms[ZERO_EXP] = terms.get(ZERO_EXP, Fraction(0)) + Fraction(rng.randint(-5, 5))
    return normalized(terms)


def run_checks() -> dict:
    counts = {
        "finite_telescopes": 0,
        "positive_support_exponents": 0,
        "same_sign_constant_coefficient_products": 0,
        "finite_augmentation_products": 0,
        "rank_one_support_failures": 0,
        "explicit_distinguishing_examples": 0,
    }
    a: Exponent = (Fraction(1), Fraction(0))
    for r in range(1, 6):
        for s in range(1, 7):
            gamma: Exponent = (Fraction(0), Fraction(r, 7))
            delta: Exponent = (Fraction(0), Fraction(r, 7) + Fraction(s, 11))
            d = exp_sub(delta, gamma)
            difference = series_sub(monomial(delta), monomial(gamma))
            partial: Series = {}
            for n in range(65):
                exponent = exp_sub(exp_sub(a, delta), exp_scale(n, d))
                check(exponent > ZERO_EXP, f"nonpositive lexicographic support at {r,s,n}")
                counts["positive_support_exponents"] += 1
                partial = series_add(partial, monomial(exponent))
                remainder_exp = exp_sub(a, exp_scale(n + 1, d))
                expected = series_sub(monomial(a), monomial(remainder_exp))
                actual = series_mul(difference, partial)
                check(actual == expected, f"finite telescope failed at {r,s,n}")
                check(remainder_exp > ZERO_EXP, "finite remainder lost positivity")
                check(actual != monomial(a), "finite telescope incorrectly dropped remainder")
                counts["finite_telescopes"] += 1

    rng = random.Random(20260922)
    for sign in (1, -1, 0):
        for case in range(300):
            x, y = random_series(rng, sign), random_series(rng, sign)
            product = series_mul(x, y)
            check(augmentation(product) == augmentation(x) * augmentation(y),
                  f"augmentation product failed at {sign,case}")
            counts["finite_augmentation_products"] += 1
            if sign:
                check(constant_coefficient(product) ==
                      constant_coefficient(x) * constant_coefficient(y),
                      f"same-sign constant coefficient failed at {sign,case}")
                counts["same_sign_constant_coefficient_products"] += 1

    # In rank one the proposed positive-support progression eventually fails.
    for step in (Fraction(1, 2), Fraction(1, 10), Fraction(2, 17)):
        real_a, real_delta = Fraction(1), 2 * step
        n = 0
        while real_a - real_delta - n * step > 0:
            n += 1
        check(real_a - real_delta - n * step <= 0, "rank-one termination failed")
        counts["rank_one_support_failures"] += 1

    positive = monomial((Fraction(1), Fraction(0)))
    negative = monomial((Fraction(-1), Fraction(0)))
    for series in (positive, negative):
        check(augmentation(series) == 1 and constant_coefficient(series) == 0,
              "augmentation did not distinguish a monomial from its residue")
        counts["explicit_distinguishing_examples"] += 1
    check(series_mul(positive, negative) == monomial(ZERO_EXP),
          "opposite-support monomials failed to multiply to one")
    check(constant_coefficient(series_mul(positive, negative)) == 1,
          "mixed-support residue failure was not detected")
    counts["explicit_distinguishing_examples"] += 1

    return {
        "status": "all finite checks passed",
        "arithmetic": "exact Fraction coefficients and lexicographic Q x Q exponents",
        "seed": 20260922,
        "counts": counts,
        "scope": "Finite identities and counterexample illustrations only.",
        "not_verified_by_this_program": [
            "existence or uniqueness of surreal normal forms",
            "countable Hahn support or infinite multiplication identities",
            "proper-class cardinal separation and universal factorization",
            "Lean kernel verification",
            "novelty or publication priority",
        ],
    }


def main() -> None:
    report = run_checks()
    output = Path(__file__).resolve().with_name("verification.json")
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    print(f"Report written to {output.name}")


if __name__ == "__main__":
    main()
