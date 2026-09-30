#!/usr/bin/env python3
"""Exact finite regression checks for Beyond Finite Surreal Polytopes.

Python 3.10+, standard library only. No floating point, network, or CAS.
These tests check finite algebraic ingredients, not saturation, all faces of
an infinite hull, or a model of the entire surreal field. The proofs are in
article.tex. Counts count completed test cases, not independent theorems.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
import json
from pathlib import Path
import random
import sys
from typing import Iterable, Sequence

Poly = tuple[F, ...]  # coefficients in increasing degree
Vector = tuple[F, ...]
COUNTS: Counter[str] = Counter()
RNG = random.Random(20260930)


def require(condition: bool, category: str, detail: str = "") -> None:
    if not condition:
        raise AssertionError(f"{category}: {detail}")
    COUNTS[category] += 1


def trim(p: Iterable[F]) -> Poly:
    result = list(p)
    if not result:
        return (F(0),)
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result)


def add(p: Poly, q: Poly) -> Poly:
    return trim((p[i] if i < len(p) else F(0))
                + (q[i] if i < len(q) else F(0))
                for i in range(max(len(p), len(q))))


def scale(p: Poly, c: F) -> Poly:
    return trim(c * a for a in p)


def mul(p: Poly, q: Poly) -> Poly:
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return trim(out)


def evaluate(p: Poly, t: F) -> F:
    out = F(0)
    for a in reversed(p):
        out = out * t + a
    return out


def square_product(roots: Sequence[F]) -> Poly:
    out = (F(1),)
    for a in roots:
        out = mul(out, (a * a, -2 * a, F(1)))
    return out


def dot(x: Sequence[F], y: Sequence[F]) -> F:
    if len(x) != len(y):
        raise ValueError("Mismatched vector dimensions")
    return sum((a * b for a, b in zip(x, y)), F(0))


def rank(rows: Sequence[Sequence[F]]) -> int:
    if not rows:
        return 0
    a = [list(map(F, row)) for row in rows]
    n = len(a[0])
    if any(len(row) != n for row in a):
        raise ValueError("Ragged matrix")
    r = 0
    for col in range(n):
        pivot = next((i for i in range(r, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        p = a[r][col]
        a[r] = [v / p for v in a[r]]
        for i in range(r + 1, len(a)):
            c = a[i][col]
            if c:
                a[i] = [v - c * w for v, w in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def determinant(rows: Sequence[Sequence[F]]) -> F:
    n = len(rows)
    if any(len(row) != n for row in rows):
        raise ValueError("Determinant requires a square matrix")
    a = [list(map(F, row)) for row in rows]
    out = F(1)
    for col in range(n):
        pivot = next((i for i in range(col, n) if a[i][col]), None)
        if pivot is None:
            return F(0)
        if pivot != col:
            a[pivot], a[col] = a[col], a[pivot]
            out = -out
        p = a[col][col]
        out *= p
        for i in range(col + 1, n):
            c = a[i][col] / p
            for j in range(col + 1, n):
                a[i][j] -= c * a[col][j]
            a[i][col] = F(0)
    return out


def moment(t: F, d: int) -> Vector:
    return tuple(t ** j for j in range(1, d + 1))


def leading_sign(p: Sequence[F]) -> int:
    """Sign at a positive infinitesimal for a rational polynomial."""
    a = next((a for a in p if a), F(0))
    return int(a > 0) - int(a < 0)


def test_moment_and_polar() -> list[dict[str, int]]:
    roots = tuple(map(F, range(-3, 4)))
    probes = tuple(F(i, 2) for i in range(-9, 10))
    dimensions = []
    for d in range(2, 9):
        k = d // 2
        center = tuple(sum((moment(F(r), d)[j] for r in range(d + 1)), F(0))
                       / (d + 1) for j in range(d))
        sets_checked = 0
        for size in range(1, k + 1):
            for subset in combinations(roots, size):
                p = square_product(subset)
                require(len(p) - 1 == 2 * size <= d,
                        "moment_degree_bounds")
                padded = p + (F(0),) * (d + 1 - len(p))
                c, u = padded[0], tuple(-a for a in padded[1:])
                alpha = c - dot(u, center)
                require(alpha > 0, "polar_normalization_positive")
                require(alpha == sum((evaluate(p, F(r)) for r in range(d + 1)),
                                     F(0)) / (d + 1), "polar_center_identity")
                y = tuple(a / alpha for a in u)
                active_rows = []
                for t in probes:
                    q = evaluate(p, t)
                    require(q >= 0 and ((q == 0) == (t in subset)),
                            "moment_square_product_slacks")
                    require(c - dot(u, moment(t, d)) == q,
                            "moment_affine_slack_identity")
                    row = tuple(a - b for a, b in zip(moment(t, d), center))
                    slack = 1 - dot(y, row)
                    require(slack == q / alpha and slack >= 0,
                            "polar_slack_identity")
                    require((slack == 0) == (t in subset),
                            "polar_exact_sample_active_set")
                for a in subset:
                    active_rows.append(tuple(v - b for v, b in
                                             zip(moment(a, d), center)))
                require(rank(active_rows) == size, "polar_active_rank")
                require(d - size >= (d + 1) // 2 >= 1,
                        "polar_face_dimension_gap")
                # A finite convex combination tests the affine, not univariate,
                # interpretation of the slack polynomial.
                ts = tuple(RNG.sample(probes, 4))
                ws = [F(RNG.randrange(1, 8)) for _ in ts]
                total = sum(ws, F(0))
                ws = [w / total for w in ws]
                x = tuple(sum((w * moment(t, d)[j] for w, t in zip(ws, ts)), F(0))
                          for j in range(d))
                weighted = sum((w * evaluate(p, t) for w, t in zip(ws, ts)), F(0))
                require(c - dot(u, x) == weighted >= 0,
                        "convex_combination_slack")
                sets_checked += 1
        dimensions.append({"d": d, "k": k, "root_subsets_checked": sets_checked,
                           "minimum_polar_face_dimension": d - k})
    return dimensions


def test_vandermonde() -> None:
    for n in range(2, 11):
        for trial in range(12):
            ts = tuple(sorted(F(a, 3) for a in RNG.sample(range(-25, 26), n)))
            matrix = [[t ** j for j in range(n)] for t in ts]
            expected = F(1)
            for i in range(n):
                for j in range(i + 1, n):
                    expected *= ts[j] - ts[i]
            require(determinant(matrix) == expected != 0,
                    "vandermonde_determinants", f"n={n}, trial={trial}")


def test_sharp_family() -> list[dict[str, int]]:
    grid = tuple(F(i, 2) for i in range(-2, 3))
    points: set[Vector] = {(F(0),), (F(1, 2),), (F(1),)}
    counts = []
    for d in range(1, 8):
        base = {(F(0),)}  # zero section of K_1
        if d > 1:
            base = {p + (F(0),) for p in points}
            graph = set()
            for z in product(grid, repeat=d - 1):
                norm2 = dot(z, z)
                if norm2 <= 1:
                    graph.add(tuple(z) + (norm2,))
            points = base | graph
        require({x for x in points if x[-1] == 0} == base,
                "sharp_zero_section_sample_identity", f"d={d}")
        ordered = sorted(points)
        for x in ordered:
            coeffs = tuple(-v for v in reversed(x))
            require(leading_sign(coeffs) == (0 if not any(x) else -1),
                    "sharp_generator_leading_sign", f"d={d}, x={x}")
        for _ in range(100):
            chosen = [RNG.choice(ordered) for _ in range(4)]
            weights = [F(RNG.randint(1, 6)) for _ in chosen]
            total = sum(weights, F(0))
            weights = [w / total for w in weights]
            x = tuple(sum((w * p[j] for w, p in zip(weights, chosen)), F(0))
                      for j in range(d))
            require(leading_sign(tuple(-v for v in reversed(x)))
                    == (0 if not any(x) else -1), "sharp_combination_leading_sign")
        counts.append({"dimension": d, "sampled_generators": len(points)})
    e = (F(0), F(1))
    tangent = scale(e, F(-1, 2))
    height = mul(tangent, tangent)
    value = add(scale(height, F(-1)), scale(mul(e, tangent), F(-1)))
    require(value == (F(0), F(0), F(1, 4)),
            "definable_extension_counterexample_identity")
    require(leading_sign(value) == 1, "definable_extension_positive_sign")
    return counts


def test_finite_halfspaces() -> None:
    for d in range(1, 7):
        rows = [tuple(F(sign if j == i else 0) for j in range(d))
                for i in range(d) for sign in (-1, 1)]
        for _ in range(60):
            lambdas = [F(RNG.randint(0, 9), RNG.randint(1, 5)) for _ in rows]
            v = tuple(sum((c * row[j] for c, row in zip(lambdas, rows)), F(0))
                      for j in range(d))
            beta = sum(lambdas, F(0))
            require(sum(map(abs, v), F(0)) <= beta,
                    "cube_farkas_combination_certificates")
        for x in product((F(-1), F(0), F(1)), repeat=d):
            active = [a for a in rows if dot(a, x) == 1]
            require(rank(active) == sum(v != 0 for v in x),
                    "cube_active_face_ranks")
            require((rank(active) == d) == all(abs(v) == 1 for v in x),
                    "cube_extreme_point_criterion")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write a deterministic JSON result")
    args = parser.parse_args()
    try:
        dimensions = test_moment_and_polar()
        test_vandermonde()
        sharp = test_sharp_family()
        test_finite_halfspaces()
        result = {
            "status": "PASS",
            "arithmetic": "fractions.Fraction; exact rational polynomial operations",
            "random_seed": 20260930,
            "scope": "Finite algebraic regression checks only; not a proof of saturation "
                     "or classification of infinitely many faces.",
            "total_checks": sum(COUNTS.values()),
            "checks_by_category": dict(sorted(COUNTS.items())),
            "moment_and_polar": dimensions,
            "sharp_family_samples": sharp,
        }
        text = json.dumps(result, indent=2, sort_keys=True) + "\n"
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(text, encoding="utf-8")
        print(text, end="")
        return 0
    except (AssertionError, ValueError, OSError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
