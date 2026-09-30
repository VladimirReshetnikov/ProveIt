#!/usr/bin/env python3
"""Exact finite regression checks for Surreal Polytopes at Finite and Transfinite Scales.

Python 3.10+, standard library only.  These tests do not prove the infinite or
transfinite theorems and do not implement the surreal number field.  All finite
arithmetic is exact Fraction arithmetic.  Run from any working directory.
"""
from __future__ import annotations

import itertools
import json
import random
from fractions import Fraction as F
from pathlib import Path
from typing import Iterable, Sequence

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data"
CHECKS: dict[str, int] = {}


def check(condition: bool, group: str, detail: str = "") -> None:
    if not condition:
        raise AssertionError(f"{group}: {detail}")
    CHECKS[group] = CHECKS.get(group, 0) + 1


def sign(x: F) -> int:
    return (x > 0) - (x < 0)


def dot(a: Sequence[F], b: Sequence[F]) -> F:
    if len(a) != len(b):
        raise ValueError("dot-product dimensions differ")
    return sum((x * y for x, y in zip(a, b)), F(0))


def lexsign(xs: Iterable[F]) -> int:
    return next((sign(x) for x in xs if x), 0)


def rank(rows: Sequence[Sequence[F]]) -> int:
    if not rows:
        return 0
    a = [list(map(F, row)) for row in rows]
    cols = len(a[0])
    if any(len(row) != cols for row in a):
        raise ValueError("ragged matrix")
    r = 0
    for col in range(cols):
        pivot = next((k for k in range(r, len(a)) if a[k][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        z = a[r][col]
        a[r] = [x / z for x in a[r]]
        for k in range(len(a)):
            if k != r and a[k][col]:
                z = a[k][col]
                a[k] = [x - z * y for x, y in zip(a[k], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def solve(matrix: Sequence[Sequence[F]], rhs: Sequence[F]) -> list[F]:
    n = len(rhs)
    if len(matrix) != n or any(len(row) != n for row in matrix):
        raise ValueError("solve requires a square matrix")
    a = [list(map(F, row)) + [F(y)] for row, y in zip(matrix, rhs)]
    for col in range(n):
        pivot = next((k for k in range(col, n) if a[k][col]), None)
        if pivot is None:
            raise ValueError("singular matrix")
        a[col], a[pivot] = a[pivot], a[col]
        z = a[col][col]
        a[col] = [x / z for x in a[col]]
        for k in range(n):
            if k != col:
                z = a[k][col]
                a[k] = [x - z * y for x, y in zip(a[k], a[col])]
    return [a[k][-1] for k in range(n)]


def basis_slacks(points: Sequence[Sequence[F]]):
    """All affine bases and their fundamental real relation vectors."""
    n, d = len(points), len(points[0])
    cols = [[F(1)] + list(map(F, p)) for p in points]
    result = []
    for basis in itertools.combinations(range(n), d + 1):
        matrix = [[cols[b][r] for b in basis] for r in range(d + 1)]
        if rank(matrix) != d + 1:
            continue
        rels = []
        for j in range(n):
            if j in basis:
                continue
            lam = solve(matrix, cols[j])
            c = [F(0)] * n
            c[j] = F(1)
            for b, x in zip(basis, lam):
                c[b] -= x
            rels.append((j, tuple(c)))
        result.append((basis, rels))
    if not result:
        raise ValueError("configuration does not span its ambient affine space")
    return result


def lower_cells(slacks, rows: Sequence[Sequence[F]]) -> set[frozenset[int]]:
    """Maximal marked lower cells for lexicographically ordered height rows."""
    result = set()
    for basis, rels in slacks:
        signs = [(j, lexsign(dot(c, row) for row in rows)) for j, c in rels]
        if all(s >= 0 for _, s in signs):
            result.add(frozenset(basis) | frozenset(j for j, s in signs if s == 0))
    return result


def compress(slacks, rows: Sequence[Sequence[F]]) -> list[int]:
    """Greedy coefficient-span pivots, after an affine gauge is removed."""
    relations = [c for _, c in slacks[0][1]]
    selected: list[int] = []
    residuals: list[list[F]] = []
    for i, row in enumerate(rows):
        residual = [dot(c, row) for c in relations]
        if rank(residuals + [residual]) > len(residuals):
            residuals.append(residual)
            selected.append(i)
    return selected


def epsilon_bound(slacks, rows: Sequence[Sequence[F]]) -> F:
    eta = F(1, 2)
    for _, rels in slacks:
        for _, c in rels:
            values = [dot(c, row) for row in rows]
            lead = next((j for j, x in enumerate(values) if x), None)
            if lead is None:
                continue
            tail = sum((abs(x) for x in values[lead + 1:]), F(0))
            if tail:
                eta = min(eta, abs(values[lead]) / (2 * tail))
    return eta


def evaluate(rows: Sequence[Sequence[F]], eps: F, n: int) -> list[F]:
    return [sum((eps**j * row[i] for j, row in enumerate(rows)), F(0))
            for i in range(n)]


def polygon(n: int):
    if n < 4:
        raise ValueError("need n >= 4")
    points = [[F(i), F(i * i)] for i in range(n)]
    rows = [[F(max(0, i * (i - k))) for i in range(n)] for k in range(2, n - 1)]
    return points, rows


def serial_cells(cells):
    return sorted([sorted(cell) for cell in cells])


def test_polygons():
    table = []
    for n in range(4, 13):
        points, rows = polygon(n)
        slacks = basis_slacks(points)
        q = n - 3
        selected = compress(slacks, rows)
        check(selected == list(range(q)), "polygon_rank", str(n))
        eta = epsilon_bound(slacks, rows)
        previous = {frozenset(range(n))}
        history = []
        for j in range(q + 1):
            cells = lower_cells(slacks, rows[:j])
            expected = {frozenset((0, k, k + 1)) for k in range(1, j + 1)}
            expected.add(frozenset([0] + list(range(j + 1, n))))
            check(cells == expected, "polygon_cells", f"n={n}, j={j}")
            check(len(cells) == j + 1, "polygon_cells_count")
            check(all(any(c <= p for p in previous) for c in cells), "polygon_refinement")
            real_height = evaluate(rows[:j], eta, n)
            check(lower_cells(slacks, [real_height]) == cells, "polygon_specialization")
            for _, rels in slacks:
                for _, c in rels:
                    check(sign(dot(c, real_height)) == lexsign(dot(c, row) for row in rows[:j]),
                          "polygon_all_slack_signs")
            history.append(serial_cells(cells))
            previous = cells
        table.append({"n": n, "d": 2, "q": q, "p": len(selected),
                      "strict_changes": q, "epsilon_certificate": str(eta),
                      "maximal_cells_by_stage": list(range(1, q + 2))})
        if n == 6:
            (OUT / "hexagon_example.json").write_text(json.dumps({
                "points": [[int(x) for x in p] for p in points],
                "height_rows": [[int(x) for x in row] for row in rows],
                "epsilon_certificate": str(eta), "history": history}, indent=2) + "\n")
    return table


def test_compression():
    rng = random.Random(20260930)
    for trial in range(30):
        n = rng.randrange(5, 9)
        points, hinge_rows = polygon(n)
        slacks = basis_slacks(points)
        # Some genuinely new quotient directions interspersed with many redundant rows.
        dimension = rng.randrange(1, n - 2)
        generators = hinge_rows[:dimension]
        rows = []
        for k in range(13):
            visible = min(dimension, 1 + k // 4)
            weights = [F(rng.randrange(-3, 4)) for _ in range(visible)]
            affine = [F(rng.randrange(-3, 4)) for _ in range(3)]
            rows.append([sum((weights[j] * generators[j][i] for j in range(visible)), F(0))
                         + affine[0] + affine[1] * points[i][0] + affine[2] * points[i][1]
                         for i in range(n)])
        selected = compress(slacks, rows)
        compressed = [rows[i] for i in selected]
        check(len(selected) <= n - 3, "random_rank_bound")
        eta = epsilon_bound(slacks, compressed)
        previous = {frozenset(range(n))}
        for end in range(len(rows) + 1):
            prefix = rows[:end]
            reduced = [rows[i] for i in selected if i < end]
            check(lower_cells(slacks, prefix) == lower_cells(slacks, reduced),
                  "random_prefix_cells")
            cells = lower_cells(slacks, prefix)
            check(all(any(c <= p for p in previous) for c in cells), "random_refinement")
            previous = cells
            real_height = evaluate(reduced, eta, n)
            for _, rels in slacks:
                for _, c in rels:
                    target = lexsign(dot(c, row) for row in prefix)
                    check(target == lexsign(dot(c, row) for row in reduced), "random_prefix_signs")
                    check(target == sign(dot(c, real_height)), "random_epsilon_signs")


def reciprocal_pair(signs: Sequence[int]) -> tuple[list[F], list[F]]:
    """Coefficients through N, implementing the paper's arbitrary-history construction.

    signs[n-1] is the requested sign of 1 - f_{<=n} g_{<=n} at degree n+1.
    The first sign must be +1.  The continuation beyond N can be arbitrary.
    """
    if not signs or signs[0] != 1 or any(s not in (-1, 1) for s in signs):
        raise ValueError("a nonempty +/-1 sequence beginning with +1 is required")
    a, b = [F(1), F(1)], [F(1), F(-1)]  # g, f
    for n in range(2, len(signs) + 1):
        c = -sum((a[k] * b[n - k] for k in range(1, n)), F(0))
        middle = sum((b[k] * a[n + 1 - k] for k in range(2, n)), F(0))
        an = (F(signs[n - 1]) + c + middle) / 2
        a.append(an)
        b.append(c - an)
    return a, b


def convolution(a: Sequence[F], b: Sequence[F]) -> list[F]:
    result = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return result


def check_history(signs: Sequence[int]):
    a, b = reciprocal_pair(signs)
    nmax = len(signs)
    full = convolution(a, b)
    for k in range(1, nmax + 1):
        check(full[k] == 0, "universal_reciprocal_jets")
    for k in range(2, nmax + 1):
        check(a[k] + b[k] == signs[k - 2], "universal_sum_jets")
    for n in range(1, nmax + 1):
        product = convolution(a[:n + 1], b[:n + 1])
        defect = [-x for x in product]
        defect[0] += 1
        first = next((k for k, x in enumerate(defect) if x), None)
        check(first == n + 1, "universal_defect_order")
        check(defect[n + 1] == signs[n - 1], "universal_defect_coefficient")
        check(lexsign(defect) == signs[n - 1], "universal_orientation")
        # Other directed triangle-side tests: 2g - gf - 1, 2g, and 2.
        side = [-x for x in product]
        side[0] -= 1
        for k, x in enumerate(a[:n + 1]):
            side[k] += 2 * x
        check(lexsign(side) > 0, "universal_other_sides")
    return a, b


def test_universality():
    for tail in itertools.product((-1, 1), repeat=7):
        check_history([1] + list(tail))
    rng = random.Random(31415926)
    for _ in range(12):
        check_history([1] + [rng.choice((-1, 1)) for _ in range(31)])
    example = [1, -1, -1, 1, -1, 1, 1, -1, 1, 1, -1, -1]
    a, b = check_history(example)
    (OUT / "universal_history_example.json").write_text(json.dumps({
        "requested_signs": example,
        "hulls": ["quadrilateral" if s > 0 else "triangle" for s in example],
        "g_coefficients": list(map(str, a)), "f_coefficients": list(map(str, b)),
        "interpretation": "Exact finite jets, not numerical evaluations at a real t."}, indent=2) + "\n")
    # Independent direct verification of the rational alternating example.
    for n in range(1, 65):
        f = [F((-1)**k) for k in range(n + 1)]
        g = [F(1), F(1)]
        defect = [-x for x in convolution(f, g)]
        defect[0] += 1
        expected = [F(0)] * (n + 2)
        expected[n + 1] = F((-1)**(n + 1))
        check(defect == expected, "rational_alternation_identity")


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    polygons = test_polygons()
    test_compression()
    test_universality()
    report = {
        "status": "PASS", "arithmetic": "Python fractions.Fraction; no floating point",
        "seed_compression": 20260930, "seed_universality": 31415926,
        "checks_by_group": CHECKS, "total_checks": sum(CHECKS.values()),
        "polygon_cases": polygons,
        "limitations": [
            "Finite regression tests do not prove the universal or transfinite theorems.",
            "No Lean build was performed and no surreal field implementation is claimed.",
            "The all-real-linear-functional assertion is established by the written rank proof.",
            "Random tests are deterministic samples, not exhaustive classification."]}
    (OUT / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "total_checks": report["total_checks"],
                      "checks_by_group": CHECKS, "data_directory": str(OUT)}, indent=2))


if __name__ == "__main__":
    main()
