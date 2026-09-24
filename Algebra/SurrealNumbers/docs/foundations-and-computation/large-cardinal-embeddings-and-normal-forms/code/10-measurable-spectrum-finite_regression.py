#!/usr/bin/env python3
"""Exact finite regression checks for the article's algebraic identities.

This is NOT a simulation of a nonprincipal complete ultrafilter. The finite
functional is a single coefficient projection, so it does NOT vanish on all
monomials. No transfinite summation or large-cardinal claim is checked here.
Uses only Python's standard library. Run from any working directory.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
import json
from pathlib import Path
import random
from typing import Mapping

Series = dict[F, F]
checks: Counter[str] = Counter()


def clean(x: Mapping[F, F]) -> Series:
    return {F(g): F(a) for g, a in x.items() if a}


def add(x: Mapping[F, F], y: Mapping[F, F]) -> Series:
    result = dict(x)
    for g, a in y.items():
        result[g] = result.get(g, F(0)) + a
    return clean(result)


def scale(c: F, x: Mapping[F, F]) -> Series:
    return clean({g: c * a for g, a in x.items()})


def mul(x: Mapping[F, F], y: Mapping[F, F]) -> Series:
    result: Series = {}
    for g, a in x.items():
        for h, b in y.items():
            result[g + h] = result.get(g + h, F(0)) + a * b
    return clean(result)


def monomial(g: F, a: F = F(1)) -> Series:
    return clean({g: a})


def ct(x: Mapping[F, F]) -> F:
    return x.get(F(0), F(0))


def leading(x: Mapping[F, F]) -> tuple[F, F] | None:
    if not x:
        return None
    g = min(x)
    return g, x[g]


def sign(x: Mapping[F, F]) -> int:
    lt = leading(x)
    return 0 if lt is None else (1 if lt[1] > 0 else -1)


def omnific_type(x: Mapping[F, F]) -> bool:
    return all(g <= 0 for g in x) and ct(x).denominator == 1


# Detector e lies below correction d; their supports are disjoint.
E = F(-3, 2)
D = F(-1)
A = monomial(D)


def lam(x: Mapping[F, F]) -> F:
    return x.get(E, F(0))


def nilpotent(x: Mapping[F, F]) -> Series:
    return scale(lam(x), A)


def transvection(c: F, x: Mapping[F, F]) -> Series:
    return add(x, scale(c, nilpotent(x)))


def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(f"Regression failed: {name}")
    checks[name] += 1


def random_series(rng: random.Random, *, omnific: bool = False) -> Series:
    exponents = [F(j, 2) for j in range(-8, 1 if omnific else 7)]
    result: Series = {}
    for g in exponents:
        if rng.randrange(3) == 0:
            denominator = 1 if omnific and g == 0 else rng.randint(1, 5)
            result[g] = F(rng.randint(-9, 9), denominator)
    return clean(result)


def main() -> None:
    rng = random.Random(20260923)
    for _ in range(600):
        x, y = random_series(rng), random_series(rng)
        z = random_series(rng, omnific=True)
        c, b, r = (F(rng.randint(-9, 9), rng.randint(1, 5)) for _ in range(3))
        check("nilpotence", nilpotent(nilpotent(x)) == {})
        check("group_law", transvection(c, transvection(b, x)) == transvection(c + b, x))
        check("inverse", transvection(-c, transvection(c, x)) == x)
        check("additivity", transvection(c, add(x, y)) == add(transvection(c, x), transvection(c, y)))
        check("scalar_linearity", transvection(c, scale(r, x)) == scale(r, transvection(c, x)))
        check("leading_term", leading(transvection(c, x)) == leading(x))
        check("order_on_differences", sign(add(x, scale(F(-1), y))) == sign(add(transvection(c, x), scale(F(-1), transvection(c, y)))))
        check("constant_term", ct(transvection(c, x)) == ct(x))
        check("omnific_preservation", omnific_type(z) and omnific_type(transvection(c, z)))
        check("omnific_inverse", omnific_type(transvection(-c, z)))
        check("finite_sum_identity", transvection(c, add(add(x, y), z)) == add(add(transvection(c, x), transvection(c, y)), transvection(c, z)))
        # The finite coefficient matrix has a single off-diagonal entry.
        for g in set(x) | {D, E, F(0)}:
            expected = x.get(g, F(0)) + (c * x.get(E, F(0)) if g == D else 0)
            check("coordinate_matrix", transvection(c, x).get(g, F(0)) == expected)
        # A finite weighted-coordinate functional is a finite sum of principal
        # ultrafilter evaluations: this tests only the finite algebraic formula.
        indices = [F(-2), E, F(0), F(1)]
        weights = [F(2), F(-3, 2), F(0), F(5, 3)]
        ell = lambda v: sum((w * v.get(g, F(0)) for g, w in zip(indices, weights)), F(0))
        check("weighted_coordinate_additivity", ell(add(x, y)) == ell(x) + ell(y))
        check("weighted_coordinate_scalar", ell(scale(r, x)) == r * ell(x))

    detector = monomial(E)
    for c in [F(1), F(-1), F(2, 3), F(-7, 5)]:
        check("nonmultiplicativity", transvection(c, mul(A, detector)) != mul(transvection(c, A), transvection(c, detector)))
        defect = add(mul(transvection(c, A), transvection(c, detector)), scale(F(-1), transvection(c, mul(A, detector))))
        check("exact_multiplicative_defect", defect == scale(c, mul(A, A)))
        check("correction_monomial_fixed", transvection(c, A) == A)
        check("detector_monomial_not_fixed_finite_only", transvection(c, detector) != detector)

    report = {
        "status": "passed",
        "seed": 20260923,
        "random_cases": 600,
        "total_assertions": sum(checks.values()),
        "assertions_by_category": dict(sorted(checks.items())),
        "arithmetic": "exact rational coefficients and exact rational exponents",
        "scope": "finite algebraic regression checks only",
        "not_verified": [
            "existence or consistency of measurable cardinals",
            "complete nonprincipal ultrafilters",
            "monomial-invisible infinite functionals",
            "countable or uncountable Hahn summation",
            "class elementary embeddings and normal-form absoluteness",
            "the mathematical proofs or publication novelty"
        ],
        "finite_analogue_warning": "The finite coefficient functional is principal and does not vanish on every monomial."
    }
    destination = Path(__file__).resolve().parents[1] / "data"
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "finite_regression_results.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {report['total_assertions']} exact finite assertions across {len(checks)} categories.")
    print(report["finite_analogue_warning"])
    print("No infinite summation, large-cardinal assertion, or proof is computationally verified.")


if __name__ == "__main__":
    main()
