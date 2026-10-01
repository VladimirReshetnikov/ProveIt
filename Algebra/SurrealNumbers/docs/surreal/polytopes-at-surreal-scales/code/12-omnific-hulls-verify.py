#!/usr/bin/env python3
"""Exact finite checks accompanying the omnific integer-hull manuscript.

Uses only the Python standard library. These checks are NOT a computation in
No and are NOT a substitute for the general proofs in the article.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from itertools import combinations, product
import json
from math import isqrt
from pathlib import Path
from typing import Iterable, Sequence

Point = tuple[int | Q, int | Q]
A = ((-1, 0), (0, -1), (2, 3))
POS_G = ((1, 0), (0, 1), (1, -1), (2, -1), (3, -2))
G = POS_G + tuple((-x, -y) for x, y in POS_G)
M = tuple(max(abs(a*x + b*y) for x, y in G) for a, b in A)


def dot(a: Sequence[int | Q], b: Sequence[int | Q]) -> int | Q:
    return sum(x*y for x, y in zip(a, b))


def graph(u: Point) -> tuple[int | Q, ...]:
    return (*u, *(dot(a, u) for a in A))


def conformal(u: Sequence[int | Q], v: Sequence[int | Q]) -> bool:
    return all(x*y >= 0 and abs(x) <= abs(y) for x, y in zip(u, v))


def decompose(u: tuple[int, int]) -> dict[tuple[int, int], int]:
    """Closed-form conformal decomposition proved in the manuscript."""
    x, y = u
    sign = -1 if (x < 0 or (x == 0 and y < 0)) else 1
    x, y = sign*x, sign*y
    terms: list[tuple[tuple[int, int], int]]
    if y >= 0:
        terms = [((1, 0), x), ((0, 1), y)]
    else:
        t = -y
        if 2*x >= 3*t:
            k, r = divmod(t, 2)
            terms = [((3, -2), k), ((2, -1), r),
                     ((1, 0), x-3*k-2*r)]
        else:
            k, r = divmod(x, 3)
            terms = [((3, -2), k), ((1, -1), r),
                     ((0, -1), t-2*k-r)]
    result: dict[tuple[int, int], int] = {}
    for (a, b), coeff in terms:
        assert coeff >= 0
        if coeff:
            key = sign*a, sign*b
            result[key] = result.get(key, 0) + coeff
    return result


def cross(o: Point, a: Point, b: Point) -> int | Q:
    return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])


def hull(points: Iterable[Point]) -> list[Point]:
    """Exact monotone-chain convex hull, with no collinear interior points."""
    pts = sorted(set(points))
    if len(pts) <= 1:
        return pts
    lo: list[Point] = []
    hi: list[Point] = []
    for p in pts:
        while len(lo) >= 2 and cross(lo[-2], lo[-1], p) <= 0:
            lo.pop()
        lo.append(p)
    for p in reversed(pts):
        while len(hi) >= 2 and cross(hi[-2], hi[-1], p) <= 0:
            hi.pop()
        hi.append(p)
    return lo[:-1] + hi[:-1]


def intersection(a: Point, b: Point, rhs_a: int, rhs_b: int) -> Point | None:
    det = a[0]*b[1] - a[1]*b[0]
    if not det:
        return None
    return (Q(rhs_a*b[1]-a[1]*rhs_b, det),
            Q(a[0]*rhs_b-rhs_a*b[0], det))


def lattice_points(B: int) -> list[Point]:
    return [(x, y) for x in range(B//2+1)
            for y in range((B-2*x)//3+1)]


def candidates(B: int) -> tuple[list[Point], int]:
    beta = (0, 0, B)
    out: list[Point] = []
    labels = 0
    for i, j in combinations(range(3), 2):
        for r, s in product(range(M[i]), range(M[j])):
            labels += 1
            v = intersection(A[i], A[j], beta[i]-r, beta[j]-s)
            assert v is not None
            if all(Q(x).denominator == 1 for x in v) and all(
                dot(a, v) <= b for a, b in zip(A, beta)
            ):
                out.append(v)
    return out, labels


def cut_vertices(B: int) -> list[Point]:
    rows = (*A, (1, 1), (1, 2), (0, 1))
    rhs = (0, 0, B, B//2, (2*B)//3, B//3)
    vertices: list[Point] = []
    for i, j in combinations(range(len(rows)), 2):
        v = intersection(rows[i], rows[j], rhs[i], rhs[j])
        if v is not None and all(dot(a, v) <= b for a, b in zip(rows, rhs)):
            vertices.append(v)
    return hull(vertices)


def table_vertices(T: int, r: int) -> list[Point]:
    cases: tuple[list[Point], ...] = (
        [(0, 0), (3*T, 0), (0, 2*T)],
        [(0, 0), (3*T, 0), (3*T-1, 1), (2, 2*T-1), (0, 2*T)],
        [(0, 0), (3*T+1, 0), (1, 2*T), (0, 2*T)],
        [(0, 0), (3*T+1, 0), (3*T, 1), (0, 2*T+1)],
        [(0, 0), (3*T+2, 0), (2, 2*T), (0, 2*T+1)],
        [(0, 0), (3*T+2, 0), (3*T+1, 1), (1, 2*T+1), (0, 2*T+1)],
    )
    return cases[r]


def check_graver(radius: int) -> tuple[int, int]:
    count = 0
    for x, y in product(range(-radius, radius+1), repeat=2):
        if (x, y) == (0, 0):
            continue
        parts = decompose((x, y))
        assert parts and all(g in G for g in parts)
        assert (sum(n*g[0] for g, n in parts.items()),
                sum(n*g[1] for g, n in parts.items())) == (x, y)
        assert all(conformal(graph(g), graph((x, y))) for g in parts)
        count += 1
    minimality_checks = 0
    for g in G:
        for u in product(range(-abs(g[0]), abs(g[0])+1),
                         range(-abs(g[1]), abs(g[1])+1)):
            if u != (0, 0) and u != g:
                assert not conformal(graph(u), graph(g))
                minimality_checks += 1
    return count, minimality_checks


def check_augmentation(max_B: int) -> int:
    checked = 0
    objectives = list(product(range(-3, 4), repeat=2))
    for B in range(max_B+1):
        pts = lattice_points(B)
        pointset = set(pts)
        for c in objectives:
            optimum = max(dot(c, p) for p in pts)
            for p in pts:
                improving = any(
                    dot(c, g) > 0 and (p[0]+g[0], p[1]+g[1]) in pointset
                    for g in G
                )
                assert (not improving) == (dot(c, p) == optimum)
                checked += 1
    return checked


def irrational_certificates() -> list[dict[str, int]]:
    """Certify 1/2-1/D < m-sqrt(2)*n < 1/2 using rational squares."""
    out = []
    for D in (10, 100, 1000, 10000):
        for n in range(1, 200001):
            m = (isqrt(8*n*n)+1)//2
            lower = Q(m)-Q(1, 2)
            upper = lower+Q(1, D)
            if lower >= 0 and lower*lower < 2*n*n < upper*upper:
                out.append({"D": D, "n": n, "m": m})
                break
        else:
            raise AssertionError(f"No certificate found for D={D}")
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    parser.add_argument("--max-T", type=int, default=40)
    parser.add_argument("--radius", type=int, default=80)
    args = parser.parse_args()
    if args.max_T < 2 or args.radius < 3:
        parser.error("--max-T must be at least 2 and --radius at least 3")

    decomposition_count, minimality_count = check_graver(args.radius)
    lattice_count = 0
    full_hull_cases = 0
    table_cases = 0
    max_vertices = 0
    for B in range(6*args.max_T+6):
        pts = lattice_points(B)
        lattice_count += len(pts)
        reference = hull(pts)
        candidate_pts, label_count = candidates(B)
        assert label_count == 21
        assert hull(candidate_pts) == reference
        assert cut_vertices(B) == reference
        full_hull_cases += 1
        max_vertices = max(max_vertices, len(reference))
        T, r = divmod(B, 6)
        if T >= 2:
            assert table_vertices(T, r) == reference
            table_cases += 1
    augmentation_cases = check_augmentation(35)
    results = {
        "status": "all checks passed",
        "arithmetic": "integers and fractions.Fraction; no floating-point decisions",
        "scope": "finite ordinary-integer specializations; not a formal proof or surreal implementation",
        "matrix_A": A,
        "graver_set": G,
        "slack_thresholds_M": M,
        "candidate_label_bound": 21,
        "graver_decomposition_radius": args.radius,
        "conformal_decomposition_checks": decomposition_count,
        "graver_minimality_checks": minimality_count,
        "integer_hull_cases": full_hull_cases,
        "B_range_inclusive": [0, 6*args.max_T+5],
        "enumerated_lattice_points_across_cases": lattice_count,
        "six_residue_table_cases": table_cases,
        "largest_vertex_count_observed": max_vertices,
        "local_global_augmentation_checks": augmentation_cases,
        "irrational_density_certificates": irrational_certificates(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
