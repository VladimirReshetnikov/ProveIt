#!/usr/bin/env python3
"""Exact finite diagnostics for Ordinal Rigidity of Borel Hilbert Orders.

Python 3.10+, standard library only. These tests check finite algebraic
instances, not Baire category, topology, infinite sums, or transfinite proofs.
Run: python3 verify.py [--output verification_results.json]
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import random
import sys
from typing import Sequence

Vector = tuple[Q, ...]
Matrix = tuple[Vector, ...]
SEED = 231113699
COUNTS: Counter[str] = Counter()


def check(condition: bool, category: str, message: str = "") -> None:
    """Count each explicit logical check, stopping at the first failure."""
    COUNTS[category] += 1
    if not condition:
        raise AssertionError(f"{category} check {COUNTS[category]}: {message}")


def sign(x: Sequence[Q]) -> int:
    for a in x:
        if a:
            return 1 if a > 0 else -1
    return 0


def rank(x: Sequence[Q]) -> int | None:
    return next((i for i, a in enumerate(x) if a), None)


def add(x: Vector, y: Vector) -> Vector:
    if len(x) != len(y):
        raise ValueError("Vector lengths must agree")
    return tuple(a + b for a, b in zip(x, y))


def scale(a: Q, x: Vector) -> Vector:
    return tuple(a * b for b in x)


def compare(x: Vector, y: Vector) -> int:
    return sign(add(x, scale(Q(-1), y)))


def matvec(a: Matrix, x: Vector) -> Vector:
    if not a or any(len(row) != len(x) for row in a):
        raise ValueError("Incompatible or empty matrix")
    return tuple(sum((v * w for v, w in zip(row, x)), Q(0)) for row in a)


def inverse(a: Matrix) -> Matrix:
    """Gauss--Jordan inversion using exact rational arithmetic."""
    n = len(a)
    if n == 0 or any(len(row) != n for row in a):
        raise ValueError("Expected a nonempty square matrix")
    m = [list(row) + [Q(i == j) for j in range(n)] for i, row in enumerate(a)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if m[i][j]), None)
        if pivot is None:
            raise ValueError("Singular matrix")
        m[j], m[pivot] = m[pivot], m[j]
        p = m[j][j]
        m[j] = [v / p for v in m[j]]
        for i in range(n):
            if i == j:
                continue
            c = m[i][j]
            if c:
                m[i] = [v - c * w for v, w in zip(m[i], m[j])]
    return tuple(tuple(row[n:]) for row in m)


def random_vector(rng: random.Random, n: int) -> Vector:
    return tuple(Q(rng.randint(-4, 4), rng.randint(1, 4)) for _ in range(n))


def cone_tests(rng: random.Random) -> None:
    cat = "lexicographic_cone_and_translation"
    for n in range(1, 7):
        zero = (Q(0),) * n
        check(sign(zero) == 0, cat)
        for _ in range(700):
            x, y, z = (random_vector(rng, n) for _ in range(3))
            sx = sign(x)
            check(sx in (-1, 0, 1), cat)
            check((sx == 0) == all(a == 0 for a in x), cat)
            check(sign(scale(Q(-1), x)) == -sx, cat)
            check(compare(add(x, z), add(y, z)) == compare(x, y), cat)
            q = Q(rng.randint(1, 7), rng.randint(1, 7))
            check(sign(scale(q, x)) == sx, cat)
            if sign(x) > 0 and sign(y) > 0:
                check(sign(add(x, y)) > 0, cat)
            if compare(x, y) < 0 and compare(y, z) < 0:
                check(compare(x, z) < 0, cat)


def pivot_tests(rng: random.Random) -> None:
    cat = "rectangular_increasing_pivots"
    for n in range(1, 6):
        for extra in range(4):
            m = n + extra
            for _ in range(9):
                pivots = sorted(rng.sample(range(m), n))
                rows: list[list[Q]] = [[Q(0) for _ in range(n)] for _ in range(m)]
                for j, pivot in enumerate(pivots):
                    rows[pivot][j] = Q(rng.randint(1, 5), rng.randint(1, 4))
                    for i in range(pivot + 1, m):
                        rows[i][j] = Q(rng.randint(-4, 4), rng.randint(1, 4))
                a = tuple(tuple(row) for row in rows)
                for _ in range(65):
                    x = random_vector(rng, n)
                    tx = matvec(a, x)
                    check(sign(tx) == sign(x), cat)
                    r = rank(x)
                    check(rank(tx) == (None if r is None else pivots[r]), cat)
                    y = random_vector(rng, n)
                    check(matvec(a, add(x, y)) == add(tx, matvec(a, y)), cat)
                    check(compare(tx, matvec(a, y)) == compare(x, y), cat)


def automorphism_tests(rng: random.Random) -> None:
    cat = "triangular_automorphisms"
    for n in range(1, 7):
        for _ in range(10):
            a = tuple(tuple(
                Q(0) if j > i else
                Q(rng.randint(1, 5), rng.randint(1, 3)) if i == j else
                Q(rng.randint(-3, 3), rng.randint(1, 3))
                for j in range(n)) for i in range(n))
            b = inverse(a)
            for i in range(n):
                e = tuple(Q(i == j) for j in range(n))
                check(matvec(a, matvec(b, e)) == e, cat)
                check(matvec(b, matvec(a, e)) == e, cat)
                check(b[i][i] > 0, cat)
                check(all(b[i][j] == 0 for j in range(i + 1, n)), cat)
            for _ in range(60):
                x = random_vector(rng, n)
                check(matvec(b, matvec(a, x)) == x, cat)
                check(sign(matvec(b, x)) == sign(x), cat)


def division_tests(rng: random.Random) -> None:
    cat = "presburger_division_and_congruence"
    for n in range(1, 5):
        for _ in range(180):
            x = random_vector(rng, n)
            if rng.randrange(5) == 0:
                x = (Q(0),) * n
            k = rng.randint(-30, 30)
            for m in range(1, 10):
                q, r = divmod(k, m)
                y = scale(Q(1, m), x)
                check(scale(Q(m), y) == x and m * q + r == k, cat)
                check(0 <= r < m, cat)
                # The nonnegative cone permits k < 0 when x is lex-positive.
                if sign(x) > 0 or (sign(x) == 0 and k >= 0):
                    check(sign(y) > 0 or (sign(y) == 0 and q >= 0), cat)
                check((r == 0) == (k % m == 0), cat)
                residues = [s for s in range(m) if (k - s) % m == 0]
                check(residues == [r], cat)


def boundary_tests(rng: random.Random) -> None:
    cat = "finite_flag_boundary_witnesses"
    for n in range(1, 9):
        for alpha in range(n):
            for _ in range(35):
                x = (Q(0),) * (alpha + 1) + random_vector(rng, n - alpha - 1)
                for denominator in (1, 3, 11, 101):
                    t = Q(1, denominator)
                    delta = tuple(t if j == alpha else Q(0) for j in range(n))
                    xp, xm = add(x, delta), add(x, scale(Q(-1), delta))
                    check(rank(xp) == alpha and rank(xm) == alpha, cat)
                    check(sign(xp) == 1 and sign(xm) == -1, cat)
                    check(sum((a * a for a in delta), Q(0)) == t * t, cat)
                    check(all(xp[j] == xm[j] == 0 for j in range(alpha)), cat)


def hahn_encode(x: Vector, k: int) -> dict[int, Q]:
    """Finite analogue only: exponents n,...,1 and integer constant term."""
    n = len(x)
    result = {n - j: v for j, v in enumerate(x) if v}
    if k:
        result[0] = Q(k)
    return result


def hahn_add(a: dict[int, Q], b: dict[int, Q]) -> dict[int, Q]:
    result = {j: a.get(j, Q(0)) + b.get(j, Q(0)) for j in a.keys() | b.keys()}
    return {j: v for j, v in result.items() if v}


def hahn_sign(a: dict[int, Q]) -> int:
    if not a:
        return 0
    return 1 if a[max(a)] > 0 else -1


def hahn_tests(rng: random.Random) -> None:
    cat = "finite_fixed_support_hahn_addition"
    for n in range(1, 8):
        for _ in range(320):
            x, y = random_vector(rng, n), random_vector(rng, n)
            k, l = rng.randint(-10, 10), rng.randint(-10, 10)
            a, b = hahn_encode(x, k), hahn_encode(y, l)
            check(hahn_add(a, b) == hahn_encode(add(x, y), k + l), cat)
            check(hahn_sign(a) == sign(x + (Q(k),)), cat)
            check(set(a) <= set(range(n + 1)), cat)
            decoded = tuple(a.get(n - j, Q(0)) for j in range(n))
            check(decoded == x and a.get(0, Q(0)) == k, cat)
        for mask in product((False, True), repeat=n):
            x = tuple(Q(1, 2 ** (j + 1)) if on else Q(0) for j, on in enumerate(mask))
            check({n - j for j, on in enumerate(mask) if on} == set(hahn_encode(x, 0)), cat)
            check(sum((a * a for a in x), Q(0)) < Q(1, 3), cat)


def counterexample_tests() -> None:
    cat = "necessary_pivot_hypotheses"
    swap: Matrix = ((Q(0), Q(1)), (Q(1), Q(0)))
    x = (Q(1), Q(-2))
    check(sign(x) > 0 and sign(matvec(swap, x)) < 0, cat)
    negative: Matrix = ((Q(-1), Q(0)), (Q(0), Q(1)))
    check(sign(matvec(negative, (Q(1), Q(0)))) < 0, cat)
    collision: Matrix = ((Q(1), Q(1)), (Q(0), Q(1)))
    check(sign(x) > 0 and sign(matvec(collision, x)) < 0, cat)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification_results.json"))
    args = parser.parse_args()
    rng = random.Random(SEED)
    for test in (cone_tests, pivot_tests, automorphism_tests, division_tests,
                 boundary_tests, hahn_tests):
        test(rng)
    counterexample_tests()
    result = {
        "status": "PASS",
        "seed": SEED,
        "arithmetic": "fractions.Fraction; exact rational comparisons only",
        "total_assertions": sum(COUNTS.values()),
        "assertions_by_category": dict(sorted(COUNTS.items())),
        "python_version": sys.version.split()[0],
        "scope": "Finite algebraic examples and explicit finite boundary perturbations",
        "not_verified_by_this_program": [
            "Baire category and the halfspace lemma",
            "Borel regularity and completeness of topologies",
            "Transfinite flag termination and ordinal classification",
            "Infinite Hilbert sums and operator boundedness",
            "Surreal normal-form foundations",
            "Presburger quantifier elimination"
        ]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
