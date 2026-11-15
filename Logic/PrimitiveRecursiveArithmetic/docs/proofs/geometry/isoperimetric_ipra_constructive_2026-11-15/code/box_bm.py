#!/usr/bin/env python3
"""Exact rational reference implementation of the finite-box BM argument.

This is a reference implementation with regression checks. It is NOT a proof
checker for iPRA and is NOT a substitute for the uniform mathematical proof.

A box is a tuple of (lower, upper) Fraction pairs. Each input family is nonempty
and has pairwise disjoint interiors. At a recursive call we keep the clipped
box lists; we never grid-decompose them. The sum of the two list lengths drops
in EACH child, which supplies the depth bound. A coordinate grid is used only
for independently measuring the actual Minkowski union in the regression audit.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from fractions import Fraction
from itertools import combinations, product
import json
from math import prod
from pathlib import Path
import random
from typing import Iterable, Sequence

Q = Fraction
Interval = tuple[Q, Q]
Box = tuple[Interval, ...]
Family = tuple[Box, ...]


def box(intervals: Iterable[tuple[object, object]]) -> Box:
    result = tuple((Q(lo), Q(hi)) for lo, hi in intervals)
    if not result or any(lo >= hi for lo, hi in result):
        raise ValueError("boxes must have positive side lengths in dimension >= 1")
    return result


def box_volume(b: Box) -> Q:
    return prod((hi - lo for lo, hi in b), start=Q(1))


def interiors_overlap(a: Box, b: Box) -> bool:
    return all(max(x[0], y[0]) < min(x[1], y[1]) for x, y in zip(a, b))


def validate_family(bs: Family) -> int:
    if not bs:
        raise ValueError("a family must be nonempty")
    n = len(bs[0])
    if n < 1 or any(len(b) != n or any(lo >= hi for lo, hi in b) for b in bs):
        raise ValueError("inconsistent dimensions or nonpositive side lengths")
    if any(interiors_overlap(a, b) for a, b in combinations(bs, 2)):
        raise ValueError("input boxes must have pairwise disjoint interiors")
    return n


def disjoint_volume(bs: Family) -> Q:
    return sum((box_volume(b) for b in bs), start=Q(0))


def box_sum(a: Box, b: Box) -> Box:
    return tuple((x[0] + y[0], x[1] + y[1]) for x, y in zip(a, b))


def minkowski_boxes(xs: Family, ys: Family) -> Family:
    return tuple(box_sum(x, y) for x in xs for y in ys)


def union_volume(bs: Family) -> Q:
    """Measure an arbitrary overlapping finite box union by its endpoint grid."""
    if not bs:
        return Q(0)
    n = len(bs[0])
    endpoints = [sorted({z for b in bs for z in b[i]}) for i in range(n)]
    intervals = [list(zip(points, points[1:])) for points in endpoints]
    total = Q(0)
    for cell in product(*intervals):
        mid = tuple((lo + hi) / 2 for lo, hi in cell)
        if any(all(lo < point < hi for point, (lo, hi) in zip(mid, b)) for b in bs):
            total += prod((hi - lo for lo, hi in cell), start=Q(1))
    return total


def intersection(a: Box, b: Box) -> Box | None:
    result = tuple((max(x[0], y[0]), min(x[1], y[1])) for x, y in zip(a, b))
    return result if all(lo < hi for lo, hi in result) else None


def volume_contained(b: Box, bs: Family) -> bool:
    """Exact grid check of containment up to cell boundaries (irrelevant to volume)."""
    pieces = tuple(c for a in bs if (c := intersection(a, b)) is not None)
    return union_volume(pieces) == box_volume(b)


def split_family(bs: Family, coordinate: int, cut: Q) -> tuple[Family, Family]:
    """At most one clipped piece per original box in either child."""
    lower: list[Box] = []
    upper: list[Box] = []
    for b in bs:
        lo, hi = b[coordinate]
        if lo < min(hi, cut):
            piece = list(b)
            piece[coordinate] = (lo, min(hi, cut))
            lower.append(tuple(piece))
        if max(lo, cut) < hi:
            piece = list(b)
            piece[coordinate] = (max(lo, cut), hi)
            upper.append(tuple(piece))
    result = (tuple(lower), tuple(upper))
    assert disjoint_volume(result[0]) + disjoint_volume(result[1]) == disjoint_volume(bs)
    return result


def separating_cut(bs: Family) -> tuple[int, Q]:
    """Separate the first two boxes, keeping one whole box in each half-space."""
    if len(bs) < 2:
        raise ValueError("a separating cut needs two boxes")
    a, b = bs[:2]
    for i, (x, y) in enumerate(zip(a, b)):
        if x[1] <= y[0]:
            return i, (x[1] + y[0]) / 2
        if y[1] <= x[0]:
            return i, (y[1] + x[0]) / 2
    raise AssertionError("disjoint interiors must admit a separating coordinate")


def matched_volume_cut(bs: Family, coordinate: int, fraction: Q) -> Q:
    """Compute a rational cut whose lower part has the prescribed volume fraction."""
    if not 0 < fraction < 1:
        raise ValueError("the matched fraction must lie strictly between zero and one")
    target = fraction * disjoint_volume(bs)
    points = sorted({z for b in bs for z in b[coordinate]})
    accumulated = Q(0)
    for lo, hi in zip(points, points[1:]):
        midpoint = (lo + hi) / 2
        area = sum((prod((b[j][1] - b[j][0] for j in range(len(b)) if j != coordinate), start=Q(1))
                    for b in bs if b[coordinate][0] < midpoint < b[coordinate][1]), start=Q(0))
        if area > 0 and accumulated + area * (hi - lo) >= target:
            cut = lo + (target - accumulated) / area
            lower, upper = split_family(bs, coordinate, cut)
            assert disjoint_volume(lower) == target
            assert disjoint_volume(upper) == (1 - fraction) * disjoint_volume(bs)
            return cut
        accumulated += area * (hi - lo)
    raise AssertionError("the rational volume target was not reached")


@dataclass
class Audit:
    dimension: int
    root_measure: int
    nodes: int = 0
    leaves: int = 0
    max_depth: int = 0
    strict_child_decreases: int = 0
    matched_cuts: list[dict] = field(default_factory=list)
    leaf_checks: list[dict] = field(default_factory=list)


def recurse(xs: Family, ys: Family, q: Q, depth: int, audit: Audit) -> tuple[Family, Q]:
    n = audit.dimension
    measure = len(xs) + len(ys)
    vx, vy = disjoint_volume(xs), disjoint_volume(ys)
    audit.nodes += 1
    audit.max_depth = max(audit.max_depth, depth)
    assert xs and ys and q ** n * vx <= vy
    assert depth <= audit.root_measure - measure
    if len(xs) == len(ys) == 1:
        summed = box_sum(xs[0], ys[0])
        exact_volume = box_volume(summed)
        lower_bound = vx * (1 + q) ** n
        ratios = [(ys[0][i][1] - ys[0][i][0]) / (xs[0][i][1] - xs[0][i][0]) for i in range(n)]
        assert prod(ratios, start=Q(1)) >= q ** n
        assert prod((1 + t for t in ratios), start=Q(1)) >= (1 + q) ** n
        assert exact_volume >= lower_bound
        audit.leaves += 1
        audit.leaf_checks.append({"depth": depth, "x_volume": str(vx), "y_volume": str(vy),
                                  "sum_box_volume": str(exact_volume), "bm_lower_bound": str(lower_bound)})
        return (summed,), lower_bound

    if len(xs) >= 2:
        coordinate, xcut = separating_cut(xs)
        xm, xp = split_family(xs, coordinate, xcut)
        fraction = disjoint_volume(xm) / vx
        ycut = matched_volume_cut(ys, coordinate, fraction)
        ym, yp = split_family(ys, coordinate, ycut)
        selected_family = "X"
        assert len(xm) <= len(xs) - 1 and len(xp) <= len(xs) - 1
        assert len(ym) <= len(ys) and len(yp) <= len(ys)
    else:
        coordinate, ycut = separating_cut(ys)
        ym, yp = split_family(ys, coordinate, ycut)
        fraction = disjoint_volume(ym) / vy
        xcut = matched_volume_cut(xs, coordinate, fraction)
        xm, xp = split_family(xs, coordinate, xcut)
        selected_family = "Y"
        assert len(ym) <= len(ys) - 1 and len(yp) <= len(ys) - 1
        assert len(xm) <= len(xs) and len(xp) <= len(xs)

    assert all((xm, xp, ym, yp))
    assert disjoint_volume(xm) == fraction * vx
    assert disjoint_volume(ym) == fraction * vy
    assert disjoint_volume(xp) == (1 - fraction) * vx
    assert disjoint_volume(yp) == (1 - fraction) * vy
    child_measures = [len(xm) + len(ym), len(xp) + len(yp)]
    assert all(child < measure for child in child_measures)
    audit.strict_child_decreases += 2
    audit.matched_cuts.append({"depth": depth, "selected_family": selected_family,
                              "coordinate": coordinate, "x_cut": str(xcut), "y_cut": str(ycut),
                              "matched_fraction": str(fraction), "parent_measure": measure,
                              "child_measures": child_measures})
    lower_boxes, lower_bound = recurse(xm, ym, q, depth + 1, audit)
    upper_boxes, upper_bound = recurse(xp, yp, q, depth + 1, audit)
    separating_sum_cut = xcut + ycut
    assert all(b[coordinate][1] <= separating_sum_cut for b in lower_boxes)
    assert all(b[coordinate][0] >= separating_sum_cut for b in upper_boxes)
    assert lower_bound + upper_bound == vx * (1 + q) ** n
    return lower_boxes + upper_boxes, lower_bound + upper_bound


def encode_family(bs: Family) -> list:
    return [[[str(lo), str(hi)] for lo, hi in b] for b in bs]


def bm_certificate(xs: Sequence[Box], ys: Sequence[Box], q: Q) -> dict:
    """Run the cut recursion and independently measure its root Minkowski union."""
    xs, ys, q = tuple(xs), tuple(ys), Q(q)
    n = validate_family(xs)
    if validate_family(ys) != n or q < 0:
        raise ValueError("dimensions must agree and q must be nonnegative")
    vx, vy = disjoint_volume(xs), disjoint_volume(ys)
    if q ** n * vx > vy:
        raise ValueError("the hypothesis q**n * V(X) <= V(Y) does not hold")
    audit = Audit(n, len(xs) + len(ys))
    leaves, lower_bound = recurse(xs, ys, q, 0, audit)
    validate_family(leaves)  # Sum boxes from distinct leaves have disjoint interiors.
    leaf_volume = disjoint_volume(leaves)
    actual_sum_boxes = minkowski_boxes(xs, ys)
    actual_sum_volume = union_volume(actual_sum_boxes)
    assert all(volume_contained(b, actual_sum_boxes) for b in leaves)
    assert lower_bound == vx * (1 + q) ** n
    assert lower_bound <= leaf_volume <= actual_sum_volume
    assert audit.max_depth <= audit.root_measure - 2
    assert audit.nodes < 1 << (audit.root_measure + 1)
    assert audit.nodes == 2 * audit.leaves - 1
    assert audit.strict_child_decreases == audit.nodes - 1
    return {"dimension": n, "x_boxes": encode_family(xs), "y_boxes": encode_family(ys),
            "q": str(q), "x_volume": str(vx), "y_volume": str(vy),
            "bm_lower_bound": str(lower_bound), "sum_of_leaf_box_volumes": str(leaf_volume),
            "actual_minkowski_union_volume": str(actual_sum_volume),
            "root_measure": audit.root_measure, "max_depth": audit.max_depth,
            "depth_bound": audit.root_measure - 2, "nodes": audit.nodes, "leaves": audit.leaves,
            "strict_child_decreases": audit.strict_child_decreases,
            "cuts": audit.matched_cuts, "leaf_checks": audit.leaf_checks,
            "status": "all exact rational checks passed"}


def random_grid_family(d: int, count: int, rng: random.Random) -> Family:
    cells = rng.sample(list(product(range(3), repeat=d)), count)
    widths = [Q(rng.randint(1, 4), rng.randint(1, 3)) for _ in range(d)]
    origins = [Q(rng.randint(-3, 3), rng.randint(1, 3)) for _ in range(d)]
    return tuple(tuple((origin + cell[i] * width, origin + (cell[i] + 1) * width)
                       for i, (origin, width) in enumerate(zip(origins, widths))) for cell in cells)


def admissible_q(xs: Family, ys: Family) -> Q:
    """A bounded rational scan supplies a q satisfying the hypothesis exactly."""
    a, b, n = disjoint_volume(xs), disjoint_volume(ys), len(xs[0])
    return max(Q(p, 16) for p in range(129) if Q(p, 16) ** n * a <= b)


def run_regressions(seed: int = 20261115, per_dimension: int = 12) -> dict:
    rng = random.Random(seed)
    cases: list[tuple[str, Family, Family, Q]] = []
    x = (box([(0, 1), (0, 1)]), box([(2, 4), (0, 1)]))
    y = (box([(0, 2), (0, Q(3, 2))]),)
    cases.append(("rational_split_in_X", x, y, Q(1)))
    cases.append(("rational_split_in_Y", y, x, Q(1)))
    cases.append(("homothetic_equality_2D", (box([(0, 2), (0, 3)]),),
                  (box([(1, 5), (2, 8)]),), Q(2)))
    cases.append(("separated_intervals_1D", (box([(0, 1)]), box([(3, 5)])),
                  (box([(0, Q(3, 2))]), box([(2, Q(7, 2))])), Q(1)))
    cases.append(("zero_parameter_3D", (box([(0, 1), (0, 1), (0, 1)]),),
                  (box([(0, 1), (0, 2), (0, 3)]),), Q(0)))
    for d in (2, 3):
        for index in range(per_dimension):
            xs = random_grid_family(d, rng.randint(2, 4), rng)
            ys = random_grid_family(d, rng.randint(1, 4), rng)
            cases.append((f"random_{d}D_{index:02d}", xs, ys, admissible_q(xs, ys)))
    results = []
    for name, xs, ys, q in cases:
        result = bm_certificate(xs, ys, q)
        result["case"] = name
        results.append(result)
    equality = next(r for r in results if r["case"] == "homothetic_equality_2D")
    assert equality["actual_minkowski_union_volume"] == equality["bm_lower_bound"]
    first = results[0]
    assert first["cuts"][0]["matched_fraction"] == "1/3"
    assert first["cuts"][0]["y_cut"] == "2/3"
    assert first["bm_lower_bound"] == "12"
    assert first["sum_of_leaf_box_volumes"] == "25/2"
    assert first["actual_minkowski_union_volume"] == "15"
    return {"purpose": "exact rational reference implementation and finite regression audit; NOT an iPRA proof checker",
            "seed": seed, "random_cases_per_dimension": per_dimension,
            "random_dimensions": [2, 3], "named_cases": 5, "total_cases": len(results),
            "total_nodes": sum(r["nodes"] for r in results),
            "total_leaves": sum(r["leaves"] for r in results),
            "total_matched_cuts": sum(len(r["cuts"]) for r in results),
            "total_strict_child_decreases": sum(r["strict_child_decreases"] for r in results),
            "max_observed_depth": max(r["max_depth"] for r in results),
            "status": "passed", "cases": results}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20261115)
    parser.add_argument("--per-dimension", type=int, default=12)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.per_dimension < 0:
        parser.error("--per-dimension must be nonnegative")
    result = run_regressions(args.seed, args.per_dimension)
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload)
    print(json.dumps({key: value for key, value in result.items() if key != "cases"}, indent=2))


if __name__ == "__main__":
    main()
