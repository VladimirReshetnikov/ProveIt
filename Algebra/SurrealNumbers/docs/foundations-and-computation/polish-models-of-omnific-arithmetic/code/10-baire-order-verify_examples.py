#!/usr/bin/env python3
"""Exact finite regression checks for Baire Order Forces Arithmetic Rigidity.

Python 3.10+, standard library only. These checks are not proofs of the
infinite theorems and do not test Baire category, cardinality, or topology.
Run: python3 verify_examples.py --output verification_results.json
"""
from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction
from pathlib import Path
from typing import Iterable

Poly = tuple[Fraction, ...]
Point = tuple[tuple[Fraction, ...], int]
ZERO: Poly = ()
ONE: Poly = (Fraction(1),)
SEED = 20261003


def poly(xs: Iterable[int | Fraction]) -> Poly:
    values = [Fraction(x) for x in xs]
    while values and values[-1] == 0:
        values.pop()
    return tuple(values)


def add(p: Poly, q: Poly) -> Poly:
    n = max(len(p), len(q))
    return poly((p[i] if i < len(p) else 0) +
                (q[i] if i < len(q) else 0) for i in range(n))


def neg(p: Poly) -> Poly:
    return tuple(-c for c in p)


def mul(p: Poly, q: Poly) -> Poly:
    if not p or not q:
        return ZERO
    result = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            result[i + j] += a * b
    return poly(result)


def sign(p: Poly) -> int:
    return 0 if not p else (1 if p[-1] > 0 else -1)


def monomial(k: int) -> Poly:
    if k < 0:
        raise ValueError("Exponent must be nonnegative")
    return poly([0] * k + [1])


def random_poly(rng: random.Random, max_degree: int = 7) -> Poly:
    degree = rng.randrange(max_degree + 1)
    return poly([rng.randint(-8, 8)] +
                [Fraction(rng.randint(-8, 8), rng.randint(1, 7))
                 for _ in range(degree)])


def quotient_tail(p: Poly, max_removed_degree: int) -> Poly:
    """Representative of p modulo polynomials of degree <= given degree."""
    return poly(0 if i <= max_removed_degree else c
                for i, c in enumerate(p))


def point_add(p: Point, q: Point) -> Point:
    if len(p[0]) != len(q[0]):
        raise ValueError("Dimension mismatch")
    return (tuple(a + b for a, b in zip(p[0], q[0])), p[1] + q[1])


def point_scale(m: int, p: Point) -> Point:
    return (tuple(m * a for a in p[0]), m * p[1])


def point_less(p: Point, q: Point) -> bool:
    return (*p[0], p[1]) < (*q[0], q[1])


def random_point(rng: random.Random, dimension: int = 3) -> Point:
    return (tuple(Fraction(rng.randint(-5, 5), rng.randint(1, 5))
                  for _ in range(dimension)), rng.randint(-30, 30))


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def run_checks() -> dict[str, object]:
    rng = random.Random(SEED)
    counts: dict[str, int] = {}

    for _ in range(6000):
        p, q = random_poly(rng), random_poly(rng)
        k = rng.randint(0, 6)
        a = monomial(k)
        image = mul(a, p)
        in_hull = len(image) <= k + 1
        is_finite = len(p) <= 1
        check(in_hull == is_finite, "Principal hull kernel identity failed")
        difference = add(p, neg(q))
        source = quotient_tail(difference, 0)
        target = quotient_tail(mul(a, difference), k)
        check(sign(source) == sign(target), "Quotient order embedding failed")
    counts["principal_hull_kernel_cases"] = 6000
    counts["principal_hull_quotient_order_cases"] = 6000

    a = poly([2, 0, 1])
    for _ in range(4000):
        hs = [random_poly(rng, 1) for _ in range(rng.randint(1, 8))]
        result, power = ZERO, ONE
        for h in hs:
            result = add(result, mul(power, h))
            power = mul(power, a)
        nonzero = [j for j, h in enumerate(hs) if h]
        expected = sign(hs[nonzero[-1]]) if nonzero else 0
        check(sign(result) == expected, "Highest-index sign identity failed")
        # Remove the zeroth summand. H consists of integer constants + Q X.
        positive_sum = add(result, neg(hs[0]))
        check((len(positive_sum) <= 2) == (not any(hs[1:])),
              "Positive-index quotient injection failed")
    counts["bounded_subgroup_sign_cases"] = 4000
    counts["positive_index_quotient_cases"] = 4000

    for _ in range(6000):
        g = random_point(rng)
        m = rng.randint(1, 20)
        zq, r = divmod(g[1], m)
        q = (tuple(x / m for x in g[0]), zq)
        remainder = (tuple(Fraction(0) for _ in g[0]), r)
        check(point_add(point_scale(m, q), remainder) == g,
              "Presburger reconstruction failed")
        check(0 <= r < m, "Remainder out of range")
        # Search every admissible standard remainder, keeping vector part fixed.
        possible = [rr for rr in range(m) if (g[1] - rr) % m == 0]
        check(possible == [r], "Standard remainder uniqueness failed")
    counts["presburger_division_and_remainder_cases"] = 6000

    for _ in range(3000):
        m = rng.randint(1, 12)
        residues = {r for r in range(m) if rng.randrange(2)}
        lower = [random_point(rng) for _ in range(rng.randrange(4))]
        upper = [random_point(rng) for _ in range(rng.randrange(4))]
        def accepts(x: Point) -> bool:
            return (all(point_less(b, x) for b in lower) and
                    all(point_less(x, b) for b in upper) and
                    x[1] % m in residues)
        key = lambda x: (*x[0], x[1])
        if lower:
            b = max(lower, key=key)
            candidates = [(b[0], b[1] + 1 + r) for r in range(m)]
        elif upper:
            b = min(upper, key=key)
            candidates = [(b[0], b[1] - 1 - r) for r in range(m)]
        else:
            candidates = [(tuple(Fraction(0) for _ in range(3)), r)
                          for r in range(m)]
        witnesses = [random_point(rng) for _ in range(12)]
        if any(accepts(w) for w in witnesses):
            check(any(accepts(c) for c in candidates),
                  "Cooper finite-candidate implication failed")
    counts["cooper_finite_candidate_cases"] = 3000

    for n in range(41):
        geometric = poly([1] * (n + 1))
        lhs = mul(poly([1, -1]), geometric)
        rhs = add(ONE, neg(monomial(n + 1)))
        check(lhs == rhs, "Truncated geometric inverse identity failed")
    counts["geometric_inverse_cases"] = 41

    return {
        "status": "PASS",
        "seed": SEED,
        "arithmetic": "Exact fractions.Fraction; no floating-point arithmetic",
        "case_counts": counts,
        "total_reported_checks": sum(counts.values()),
        "scope": (
            "Finite algebraic regression checks only. These are not a proof "
            "of the infinite theorems and do not verify Baire category, "
            "topology, uncountability, arbitrary orders, or Lean/Rocq code."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path("verification_results.json"))
    args = parser.parse_args()
    results = run_checks()
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
