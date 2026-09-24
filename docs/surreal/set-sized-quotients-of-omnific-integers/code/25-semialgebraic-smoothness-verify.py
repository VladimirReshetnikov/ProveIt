#!/usr/bin/env python3
"""Exact, finite sanity checks accompanying the omnific smoothness manuscript.

Standard library only. These checks do not prove arbitrary Hahn summability,
proper-class statements, semialgebraic calculus, or historical novelty.
Run from any directory: python code/verify.py [--output path/to/results.json]
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from math import comb
from pathlib import Path
import json
import platform
import random
import sys


class Checks:
    def __init__(self) -> None:
        self.counts: dict[str, int] = defaultdict(int)

    def equal(self, group: str, actual: object, expected: object, detail: str) -> None:
        if actual != expected:
            raise AssertionError(f"{group}: {detail}: {actual!r} != {expected!r}")
        self.counts[group] += 1

    def true(self, group: str, condition: bool, detail: str) -> None:
        self.equal(group, condition, True, detail)


def choose_q(x: Q, n: int) -> Q:
    if n < 0:
        return Q(0)
    result = Q(1)
    for j in range(n):
        result *= (x - j) / (j + 1)
    return result


def evaluate(coefficients: list[Q], x: Q) -> Q:
    result = Q(0)
    for coefficient in reversed(coefficients):
        result = result * x + coefficient
    return result


def forward_difference(values: list[Q]) -> Q:
    n = len(values) - 1
    return sum(((-1) ** (n - j) * comb(n, j) * value
                for j, value in enumerate(values)), Q(0))


def multieval(poly: dict[tuple[int, ...], Q], point: tuple[Q, ...]) -> Q:
    total = Q(0)
    for powers, coefficient in poly.items():
        term = coefficient
        for value, power in zip(point, powers):
            term *= value ** power
        total += term
    return total


def newton_coeff(poly: dict[tuple[int, ...], Q], alpha: tuple[int, ...]) -> Q:
    total = Q(0)
    for node in product(*(range(a + 1) for a in alpha)):
        weight = 1
        for a, j in zip(alpha, node):
            weight *= (-1) ** (a - j) * comb(a, j)
        total += weight * multieval(poly, tuple(Q(j) for j in node))
    return total


def run_checks() -> dict[str, object]:
    c = Checks()
    rng = random.Random(20260923)

    # Formal power-series square identities: only the indicated finite jets.
    for sign in (-1, 1):
        coefficients = [choose_q(Q(1, 2), j) * sign ** j for j in range(65)]
        for n in range(65):
            square_coefficient = sum((coefficients[j] * coefficients[n - j]
                                      for j in range(n + 1)), Q(0))
            target = Q(1 if n == 0 else sign if n == 1 else 0)
            c.equal("binomial_square_jets", square_coefficient, target,
                    f"sign={sign}, degree={n}")
        for n, coefficient in enumerate(coefficients):
            c.true("nonzero_half_binomial_coefficients", coefficient != 0,
                   f"sign={sign}, degree={n}")

    # Newton's difference identity, evaluated exactly at nonintegral points too.
    for degree in range(1, 13):
        for x in (Q(-7, 3), Q(-1), Q(0), Q(2, 5), Q(9), Q(37, 2)):
            c.equal("binomial_difference", choose_q(x + 1, degree) - choose_q(x, degree),
                    choose_q(x, degree - 1), f"degree={degree}, x={x}")

    # Extrapolation uses arbitrary nonzero field steps, not just the step 1.
    for degree in range(13):
        for _ in range(8):
            poly = [Q(rng.randint(-20, 20), rng.randint(1, 9))
                    for _ in range(degree + 1)]
            a = Q(rng.randint(-100, 100), rng.randint(1, 9))
            h = Q(rng.randint(1, 100), rng.randint(1, 7))
            rhs = sum(((-1) ** (j + 1) * comb(degree + 1, j)
                       * evaluate(poly, a + j * h)
                       for j in range(1, degree + 2)), Q(0))
            c.equal("arbitrary_step_extrapolation", rhs, evaluate(poly, a),
                    f"degree={degree}, a={a}, h={h}")
            values = [evaluate(poly, a + j * h) for j in range(degree + 2)]
            c.equal("high_difference_zero", forward_difference(values), Q(0),
                    f"degree={degree}, a={a}, h={h}")

    # Multivariate Newton reconstruction, with ordinary integer coefficients.
    # Integrality checks concern these finite arithmetic models, not Oz itself.
    for dimensions, bounds in ((2, (3, 4)), (3, (2, 2, 2))):
        alphas = list(product(*(range(d + 1) for d in bounds)))
        for case in range(6):
            poly = {alpha: Q(rng.randint(-7, 7)) for alpha in alphas}
            newton = {alpha: newton_coeff(poly, alpha) for alpha in alphas}
            for alpha, value in newton.items():
                c.equal("integer_newton_coefficients", value.denominator, 1,
                        f"dimension={dimensions}, case={case}, alpha={alpha}")
            for node_number in range(12):
                point = tuple(Q(rng.randint(-10, 12), rng.randint(1, 5))
                              for _ in range(dimensions))
                reconstructed = Q(0)
                for alpha, coefficient in newton.items():
                    term = coefficient
                    for value, order in zip(point, alpha):
                        term *= choose_q(value, order)
                    reconstructed += term
                c.equal("multivariate_newton_reconstruction", reconstructed,
                        multieval(poly, point),
                        f"dimension={dimensions}, case={case}, node={node_number}")

    # Lexicographic rank-two illustration of b + (1/2-j)a > 0.
    previous: tuple[Q, Q] | None = None
    for j in range(129):
        exponent = (Q(1), Q(1, 2) - j)   # b=(1,0), a=(0,1)
        c.true("rank_two_positive_exponents", exponent > (Q(0), Q(0)), f"j={j}")
        if previous is not None:
            c.true("rank_two_descending_exponents", exponent < previous, f"j={j}")
        previous = exponent
    for finite_height in range(-10, 41):
        j = max(0, finite_height + 2)
        exponent = Q(finite_height) + Q(1, 2) - j
        c.true("rank_one_negative_witness", exponent < 0,
               f"height={finite_height}, j={j}")

    # Endpoint algebra: the (k+1)-st falling-factorial coefficient is nonzero;
    # the remaining exponent is -1/2. This is not a continuity proof.
    for k in range(21):
        coefficient = Q(1)
        for j in range(k + 1):
            coefficient *= Q(2 * k + 1, 2) - j
        c.true("endpoint_nonzero_coefficient", coefficient > 0, f"k={k}")
        c.equal("endpoint_derivative_exponent", Q(2 * k + 1, 2) - (k + 1),
                Q(-1, 2), f"k={k}")
        c.equal("odd_root_multiplicity", (2 * k + 1) % 2, 1, f"k={k}")

    # Exact exponents in the quadratic sampling counterexample.
    for b in (Q(j, denominator) for denominator in (1, 2, 3) for j in range(1, 21)):
        exponents = [b + (1 - 2 * j) * (b + 1) for j in range(8)]
        c.equal("quadratic_witness_leading_exponent", exponents[0], 2 * b + 1, f"b={b}")
        c.equal("quadratic_witness_negative_exponent", exponents[1], Q(-1), f"b={b}")
        c.equal("quadratic_witness_third_exponent", exponents[2], -2 * b - 3, f"b={b}")
        c.true("quadratic_witness_strict_order", all(x > y for x, y in zip(exponents, exponents[1:])),
               f"b={b}")
    c.equal("quadratic_witness_nonzero_coefficient", choose_q(Q(1, 2), 1), Q(1, 2),
            "coefficient of omega^-1")

    return {
        "status": "passed",
        "total_exact_assertions": sum(c.counts.values()),
        "groups": dict(sorted(c.counts.items())),
        "python_version": platform.python_version(),
        "implementation": platform.python_implementation(),
        "dependencies": "Python standard library only",
        "random_seed": 20260923,
        "scope": "Finite exact algebraic and exponent-model sanity checks.",
        "not_verified": [
            "General semialgebraic calculus over arbitrary real closed fields",
            "Unrestricted normal-form supports and infinite Hahn summability",
            "Proper-class quantifiers and foundational size reductions",
            "The complete theorems by a proof assistant",
            "Historical novelty or independent correctness review",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    default_output = Path(__file__).resolve().parent.parent / "audit" / "verification.json"
    parser.add_argument("--output", type=Path, default=default_output)
    args = parser.parse_args()
    try:
        result = run_checks()
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    except (AssertionError, OSError, ValueError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
