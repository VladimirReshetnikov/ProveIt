#!/usr/bin/env python3
"""Exact finite checks for The Universal Set-Sized Quotient of Oz.

This checks finite algebraic identities, NOT the class, cardinal, support-
existence, primality, or homological theorems of the accompanying article.
Python 3.10 or newer; no external packages. Run: python3 verify.py
"""
from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction as Q
from pathlib import Path
from typing import TypeAlias

Exponent: TypeAlias = tuple[Q, Q, Q]
Series: TypeAlias = dict[Exponent, Q]
ZERO: Exponent = (Q(0), Q(0), Q(0))


def exponent_add(a: Exponent, b: Exponent) -> Exponent:
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def exponent_scale(a: Exponent, scalar: Q | int) -> Exponent:
    return (a[0] * scalar, a[1] * scalar, a[2] * scalar)


def exponent_sub(a: Exponent, b: Exponent) -> Exponent:
    return exponent_add(a, exponent_scale(b, -1))


def monomial(exponent: Exponent, coefficient: Q | int = 1) -> Series:
    coefficient = Q(coefficient)
    return {exponent: coefficient} if coefficient else {}


def add(f: Series, g: Series) -> Series:
    result = dict(f)
    for exponent, coefficient in g.items():
        result[exponent] = result.get(exponent, Q(0)) + coefficient
        if not result[exponent]:
            del result[exponent]
    return result


def multiply(f: Series, g: Series) -> Series:
    result: Series = {}
    for a, ca in f.items():
        for b, cb in g.items():
            exponent = exponent_add(a, b)
            result[exponent] = result.get(exponent, Q(0)) + ca * cb
            if not result[exponent]:
                del result[exponent]
    return result


def euler(f: Series) -> Series:
    # An additive rational weight on the exponent group. The article uses
    # constant-coefficient extraction on surreal exponents instead.
    def weight(e: Exponent) -> Q:
        return 2 * e[0] - 3 * e[1] + Q(5, 7) * e[2]
    return {e: c * weight(e) for e, c in f.items() if c * weight(e)}


class Checks:
    def __init__(self) -> None:
        self.counts: dict[str, int] = {}

    def require(self, group: str, condition: bool, message: str) -> None:
        if not condition:
            raise AssertionError(f"{group}: {message}")
        self.counts[group] = self.counts.get(group, 0) + 1


def geometric_checks(checks: Checks) -> int:
    cases = 0
    for a0 in [Q(1, 3), Q(1), Q(7, 2)]:
        for a1 in [Q(-5), Q(0), Q(9, 4)]:
            a: Exponent = (a0, a1, Q(-2, 3))
            for c1 in [Q(1, 5), Q(1), Q(5, 2)]:
                for step in [Q(1, 7), Q(1), Q(4, 3)]:
                    c: Exponent = (Q(0), c1, Q(-1, 2))
                    b: Exponent = (Q(0), c1 + step, Q(3, 5))
                    d = exponent_sub(b, c)
                    checks.require("geometric", ZERO < c < b, "0<c<b")
                    qn: Series = {}
                    previous: Exponent | None = None
                    difference = add(monomial(exponent_add(a, b)),
                                     monomial(exponent_add(a, c), -1))
                    for n in range(31):
                        exponent = exponent_sub(exponent_sub(a, b),
                                                exponent_scale(d, n))
                        checks.require("geometric", exponent > ZERO,
                                       "witness exponent must be positive")
                        if previous is not None:
                            checks.require("geometric", exponent < previous,
                                           "strictly decreasing witness support")
                        previous = exponent
                        qn = add(qn, monomial(exponent))
                        expected = add(monomial(exponent_scale(a, 2)),
                                       monomial(exponent_sub(exponent_scale(a, 2),
                                                             exponent_scale(d, n + 1)), -1))
                        checks.require("geometric", multiply(difference, qn) == expected,
                                       f"finite remainder identity at N={n}")
                        checks.require("geometric", len(qn) == n + 1,
                                       "no repeated witness exponents")
                        cases += 1
    return cases


def random_series(rng: random.Random, positive_only: bool) -> Series:
    result: Series = {}
    for _ in range(rng.randrange(1, 12)):
        if rng.randrange(5) == 0:
            exponent = ZERO
        else:
            exponent = (Q(rng.randrange(-4, 5), rng.randrange(1, 5)),
                        Q(rng.randrange(-4, 5), rng.randrange(1, 5)),
                        Q(rng.randrange(-4, 5), rng.randrange(1, 5)))
            if positive_only and exponent < ZERO:
                exponent = exponent_scale(exponent, -1)
        coefficient = Q(rng.randrange(-6, 7), rng.randrange(1, 6))
        result = add(result, monomial(exponent, coefficient))
    return result


def coefficient_checks(checks: Checks, rng: random.Random) -> None:
    for _ in range(1000):
        f, g = random_series(rng, True), random_series(rng, True)
        product = multiply(f, g)
        checks.require("constant_coefficient", all(e >= ZERO for e in product),
                       "nonnegative support is multiplicatively closed")
        checks.require("constant_coefficient",
                       product.get(ZERO, Q(0)) == f.get(ZERO, Q(0)) * g.get(ZERO, Q(0)),
                       "constant coefficient of a product")
        checks.require("constant_coefficient",
                       add(f, g).get(ZERO, Q(0)) == f.get(ZERO, Q(0)) + g.get(ZERO, Q(0)),
                       "constant coefficient of a sum")
    # Deliberate boundary example: extraction is not multiplicative on the field.
    x = monomial((Q(1), Q(0), Q(0)))
    invx = monomial((Q(-1), Q(0), Q(0)))
    checks.require("boundary", multiply(x, invx).get(ZERO) == Q(1), "X times inverse X")
    checks.require("boundary", x.get(ZERO, Q(0)) * invx.get(ZERO, Q(0)) == Q(0),
                   "the separate constant coefficients vanish")


def derivation_checks(checks: Checks, rng: random.Random) -> None:
    for _ in range(1000):
        f, g = random_series(rng, False), random_series(rng, False)
        checks.require("euler_derivation", euler(add(f, g)) == add(euler(f), euler(g)),
                       "additivity")
        checks.require("euler_derivation", euler(multiply(f, g)) ==
                       add(multiply(euler(f), g), multiply(f, euler(g))), "Leibniz rule")
        checks.require("euler_derivation", set(euler(f)).issubset(f),
                       "the derivation does not enlarge support")


def matrix_checks(checks: Checks) -> None:
    for size in range(2, 22, 2):
        j = [[0] * size for _ in range(size)]
        for i in range(0, size, 2):
            j[i][i + 1] = -1
            j[i + 1][i] = 1
        for r in range(size):
            for c in range(size):
                entry = sum(j[r][k] * j[k][c] for k in range(size))
                checks.require("complex_structure_blocks", entry == (-1 if r == c else 0),
                               f"J^2=-I in dimension {size}, entry ({r},{c})")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().with_name("verification.json"))
    parser.add_argument("--seed", type=int, default=20260922)
    args = parser.parse_args()
    checks = Checks()
    rng = random.Random(args.seed)
    geometric_cases = geometric_checks(checks)
    coefficient_checks(checks, rng)
    derivation_checks(checks, rng)
    matrix_checks(checks)
    result = {
        "status": "all exact finite checks passed",
        "arithmetic": "fractions.Fraction; no floating-point arithmetic",
        "seed": args.seed,
        "geometric_remainder_cases": geometric_cases,
        "assertions_by_group": checks.counts,
        "total_assertions": sum(checks.counts.values()),
        "scope": ["finite geometric remainder identity",
                  "positivity and monotonicity of finite witness supports",
                  "constant-coefficient addition and multiplication",
                  "Euler-type diagonal derivation",
                  "real complex-structure matrices"],
        "not_verified_by_this_program": ["class or cardinal arguments",
                  "existence and multiplication of infinite Hahn supports",
                  "external primality theorem", "Tor or Ext computations",
                  "Lean formalization", "novelty or priority"]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
