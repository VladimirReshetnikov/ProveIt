#!/usr/bin/env python3
"""Exact finite checks accompanying the surreal-arithmetic manuscript.

These tests do NOT prove the infinite support or topological theorems.
They check algebraic identities and finite witness construction steps only.
No packages beyond Python's standard library are required.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
from random import Random
from typing import Mapping

SEED = 20260923
Series = dict[F, F]
COUNTS: Counter[str] = Counter()


def check(condition: bool, category: str) -> None:
    if not condition:
        raise AssertionError(f"Failed finite check in {category}")
    COUNTS[category] += 1


def clean(series: Mapping[F, F]) -> Series:
    return {g: a for g, a in series.items() if a}


def add(left: Mapping[F, F], right: Mapping[F, F]) -> Series:
    result = dict(left)
    for g, a in right.items():
        result[g] = result.get(g, F(0)) + a
    return clean(result)


def mul(left: Mapping[F, F], right: Mapping[F, F]) -> Series:
    result: Series = {}
    for g, a in left.items():
        for h, b in right.items():
            result[g + h] = result.get(g + h, F(0)) + a * b
    return clean(result)


def ct(series: Mapping[F, F]) -> F:
    return series.get(F(0), F(0))


def pairing(left: Mapping[F, F], right: Mapping[F, F]) -> F:
    return ct(mul(left, right))


def binom(a: F, n: int) -> F:
    if n < 0:
        raise ValueError("The binomial index must be nonnegative")
    result = F(1)
    for j in range(n):
        result *= (a - j) / (j + 1)
    return result


def random_series(rng: Random) -> Series:
    return clean({F(g): F(rng.randint(-5, 5), rng.randint(1, 5))
                  for g in rng.sample(range(-10, 11), rng.randint(1, 8))})


def run() -> dict[str, object]:
    COUNTS.clear()
    rng = Random(SEED)
    for _ in range(350):
        f, g, h = (random_series(rng) for _ in range(3))
        check(pairing(f, h) == pairing(h, f), "pairing")
        check(pairing(add(f, g), h) == pairing(f, h) + pairing(g, h), "pairing")
        for exponent, coefficient in f.items():
            check(pairing(f, {-exponent: F(1)}) == coefficient, "coefficient_extraction")
        scale, base = rng.randint(1, 4), F(rng.randint(1, 4))

        def transport(s: Mapping[F, F]) -> Series:
            # Inputs have integer exponents, so powers remain rational.
            return {scale * x: a * base ** int(x) for x, a in s.items()}

        check(transport(mul(f, g)) == mul(transport(f), transport(g)), "monomial_transport")
        check(pairing(transport(f), transport(h)) == pairing(f, h), "monomial_transport")
        check(ct(transport(f)) == ct(f), "monomial_transport")

    # Finite locally finite incidence systems and disjoint-row interpolation.
    for trial in range(200):
        rows: list[dict[int, F]] = []
        for i in range(80):
            cols = {i, i + 1, i + 3}
            rows.append({n: F(rng.choice([-3, -2, -1, 1, 2, 3]), rng.randint(1, 4))
                         for n in cols})
        selected: list[int] = []
        used: set[int] = set()
        for i, row in enumerate(rows):
            if not used.intersection(row):
                selected.append(i)
                used.update(row)
        detector: dict[int, F] = {}
        target: dict[int, F] = {}
        for i in selected:
            coordinate = min(rows[i])
            target[i] = F(rng.randint(-8, 8), rng.randint(1, 4))
            detector[coordinate] = target[i] / rows[i][coordinate]
        for i in selected:
            value = sum((a * detector.get(n, F(0)) for n, a in rows[i].items()), F(0))
            check(value == target[i], "sparse_detector_interpolation")
        for i, j in zip(selected, selected[1:]):
            check(not set(rows[i]).intersection(rows[j]), "disjoint_rows")

    # Naive unit coefficients really do cancel, while sparse tests do not.
    for n in range(1, 100):
        f = {F(-n): F(1), F(-n - 1): F(-1)}
        h = {F(j): F(1) for j in range(1, 101)}
        check(pairing(f, h) == 0, "cancellation_boundary")
        check(pairing(f, {F(n): F(1)}) == 1, "cancellation_boundary")

    parameters = [F(a, b) for a in range(-5, 6) for b in range(1, 4)]
    for _ in range(250):
        a, b = rng.choice(parameters), rng.choice(parameters)
        for n in range(12):
            convolution = sum((binom(a, j) * binom(b, n - j) for j in range(n + 1)), F(0))
            check(convolution == binom(a + b, n), "rank_two_vandermonde")
            inverse = sum((binom(a, j) * binom(-a, n - j) for j in range(n + 1)), F(0))
            check(inverse == (1 if n == 0 else 0), "rank_two_inverse")

    # Finite algebraic/order steps of the new topological proof.
    # A finite mesh is NOT a verification of the dense-interval theorem.
    for denominator in range(2, 80):
        gamma = F(-rng.randint(1, 9), rng.randint(1, 5))
        a = F(rng.choice([-5, -2, -1, 1, 2, 5]), rng.randint(1, 5))
        points = [(-gamma) * F(j, denominator) + gamma for j in range(1, denominator)]
        for x in points:
            y = gamma - x
            check(gamma < x < 0 and gamma < y < 0, "negative_interval")
            check(mul({x: a}, {y: F(1)}) == {gamma: a}, "fixed_product")
        for x, y in zip(points, points[1:]):
            check(x < y and gamma - x > gamma - y, "order_reflection")
    for n in range(2, 250):
        check(F(-1, n) < F(-1, n + 1) < 0, "bounded_increasing_support")
        check(F(-1, n) < 1, "valuation_nonescape")
    for m in range(1, 300):
        step = F(1, rng.randint(1, 20))
        g = m * step
        least_n = m + 1
        remainder = g - (least_n - 1) * step
        check(remainder == 0 and 0 <= remainder < step, "cyclic_remainder")

    return {
        "status": "passed",
        "seed": SEED,
        "exact_arithmetic": "fractions.Fraction",
        "assertions": sum(COUNTS.values()),
        "categories": dict(sorted(COUNTS.items())),
        "scope": "Finite algebra and order checks only; not a proof-assistant certificate.",
        "not_tested": [
            "Universal claims about arbitrary topologies",
            "Infinite dense-interval covering obstruction",
            "Arbitrary or proper-class Hahn supports",
            "Historical priority of any result",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification.json"))
    args = parser.parse_args()
    report = run()
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
