#!/usr/bin/env python3
"""Exact finite checks for Torus Defects and Sharp Affine Partition Laws.

Python 3.10+; standard library only.  These checks corroborate the paper and
are not substitutes for its proofs or for proof-assistant verification.
Run: python3 verify.py [--output verification_results.json]
"""
from __future__ import annotations

import argparse
import itertools as it
import json
from dataclasses import dataclass
from fractions import Fraction
from collections import deque
from math import isqrt
from pathlib import Path
from typing import Iterator


@dataclass(frozen=True)
class Field:
    """Prime fields, plus F_4 = F_2[u]/(u^2+u+1), encoded by 0,1,2,3."""
    q: int

    def __post_init__(self) -> None:
        if self.q != 4 and (self.q < 2 or any(self.q % p == 0 for p in range(2, isqrt(self.q) + 1))):
            raise ValueError("This checker implements prime fields and F_4 only.")

    def add(self, a: int, b: int) -> int:
        return a ^ b if self.q == 4 else (a + b) % self.q

    def mul(self, a: int, b: int) -> int:
        if self.q != 4:
            return (a * b) % self.q
        out = 0
        while b:
            if b & 1:
                out ^= a
            b >>= 1
            a <<= 1
            if a & 4:
                a ^= 7
        return out


def stirling_second(n: int, k: int) -> int:
    row = [1] + [0]*k
    for _ in range(n):
        row = [0] + [row[j-1] + j*row[j] for j in range(1, k+1)]
    return row[k]


def gaussian_binomial(n: int, d: int, q: int) -> int:
    out = Fraction(1)
    for j in range(d):
        out *= Fraction(q ** (n-j) - 1, q ** (d-j) - 1)
    if out.denominator != 1:
        raise AssertionError("Nonintegral Gaussian binomial.")
    return out.numerator


def all_affine_flats(field: Field, n: int) -> Iterator[tuple[int, tuple[int, ...], list[list[int]], tuple[int, ...], list[tuple[int, ...]]]]:
    """Enumerate every affine flat once, using RREF bases and canonical cosets.

    Pivot coordinates are the actual affine parameters.  Canonical offsets
    have zero entries at all pivot columns.  This also makes the equality
    classification test independent of point enumeration.
    """
    q = field.q
    for d in range(n + 1):
        for pivots in it.combinations(range(n), d):
            nonpivots = tuple(j for j in range(n) if j not in pivots)
            slots = [(i, j) for i, p in enumerate(pivots) for j in nonpivots if j > p]
            for entries in it.product(range(q), repeat=len(slots)):
                rows = [[0] * n for _ in range(d)]
                for i, p in enumerate(pivots):
                    rows[i][p] = 1
                for (i, j), a in zip(slots, entries):
                    rows[i][j] = a
                for tail in it.product(range(q), repeat=n-d):
                    offset = [0] * n
                    for j, a in zip(nonpivots, tail):
                        offset[j] = a
                    points = []
                    for z in it.product(range(q), repeat=d):
                        point = list(offset)
                        for i, a in enumerate(z):
                            for j in range(n):
                                point[j] = field.add(point[j], field.mul(a, rows[i][j]))
                        points.append(tuple(point))
                    yield d, pivots, rows, tuple(offset), points


def check_flats(q: int, n: int) -> dict:
    field, t = Field(q), q - 1
    counts = [0] * (n + 1)
    saturation_counts = [0] * (n + 1)
    seen: set[frozenset[tuple[int, ...]]] = set()
    for d, pivots, rows, offset, points in all_affine_flats(field, n):
        key = frozenset(points)
        assert len(key) == q**d and key not in seen
        seen.add(key)
        counts[d] += 1
        torus = sum(all(x != 0 for x in p) for p in points)
        assert torus <= t**d
        classified = True
        for j in range(n):
            nonzero = sum(rows[i][j] != 0 for i in range(d))
            coordinate_ok = (nonzero == 0 and offset[j] != 0) or (nonzero == 1 and offset[j] == 0)
            classified = classified and coordinate_ok
        assert (torus == t**d) == classified
        if classified:
            saturation_counts[d] += 1
        else:
            gap = 1 if d < 2 else (q-2) * t**(d-2)
            assert t**d - torus >= gap
    expected = [q**(n-d) * gaussian_binomial(n, d, q) for d in range(n+1)]
    assert counts == expected
    assert saturation_counts == [stirling_second(n+1, d+1)*t**(n-d) for d in range(n+1)]
    return {"field_order": q, "ambient_dimension": n, "flats_by_dimension": counts,
            "saturating_flats_by_dimension": saturation_counts, "total_flats": sum(counts),
            "capacity_equality_and_gap": "PASS", "uniqueness_Gaussian_and_Stirling_counts": "PASS"}


def power(a: int, n: int) -> Fraction:
    return Fraction(a) ** n


def defect_weight(q: int, k: int, d: int) -> Fraction:
    t = q-1
    return 1 + (q-2)*power(q, d-k) - power(t, d+1-k)


def moment_bound(s: int, m: int, q: int, k: int) -> Fraction:
    t = q-1
    return power(t, 1-k) * (s*t)**m - (q-2)*power(q, -k) * (1+s*t)**m


def ceil_fraction(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def rounded_lower(s: int, m: int, q: int) -> int:
    if m == 0:
        return 1
    t = q-1
    best = max(moment_bound(s, m, q, k) for k in range(m))
    return 1 + t*ceil_fraction((best-1)/t)


def block_upper(s: int, h: int, q: int) -> int:
    if h == 0:
        return 1
    if not 1 <= h <= s:
        raise ValueError("Require 0 <= h <= s.")
    t = q-1
    return (1+s*t)**h - h*s**(h-1)*t**h


def product_upper(s: int, m: int, q: int) -> int:
    r, ell = divmod(m, s)
    return block_upper(s, s, q)**r * block_upper(s, ell, q)


def hall_matching(s: int, h: int) -> dict[tuple[int, ...], tuple[int, ...]]:
    """A deterministic augmenting-path matching of facets into top words."""
    if not 1 <= h <= s:
        raise ValueError("Require 1 <= h <= s.")
    facets = []
    for zero in range(h):
        for values in it.product(range(1, s+1), repeat=h-1):
            f = list(values)
            f.insert(zero, 0)
            facets.append(tuple(f))
    facets.sort()
    top_to_bottom: dict[tuple[int, ...], tuple[int, ...]] = {}
    bottom_to_top: dict[tuple[int, ...], tuple[int, ...]] = {}

    for root in facets:
        queue = deque([root])
        seen_bottom = {root}
        prev_top: dict[tuple[int, ...], tuple[int, ...]] = {}
        end = None
        while queue and end is None:
            f = queue.popleft()
            z = f.index(0)
            for arm in range(1, s+1):
                top_list = list(f)
                top_list[z] = arm
                top = tuple(top_list)
                if top in prev_top:
                    continue
                prev_top[top] = f
                if top not in top_to_bottom:
                    end = top
                    break
                other = top_to_bottom[top]
                if other not in seen_bottom:
                    seen_bottom.add(other)
                    queue.append(other)
        assert end is not None
        top = end
        while True:
            bottom = prev_top[top]
            old_top = bottom_to_top.get(bottom)
            top_to_bottom[top] = bottom
            bottom_to_top[bottom] = top
            if old_top is None:
                break
            top = old_top
    matching = {f: top for top, f in top_to_bottom.items()}
    assert len(matching) == h*s**(h-1)
    assert len(set(matching.values())) == len(matching)
    for f, top in matching.items():
        assert all(a == 0 or a == b for a, b in zip(f, top))
    return matching


def point_arm_value(code: int, t: int) -> tuple[int, int]:
    if code == 0:
        return 0, 0
    return (code-1)//t + 1, (code-1)%t + 1


def cross_to_vector(point: tuple[int, ...], s: int, t: int) -> tuple[int, ...]:
    out = []
    for code in point:
        block = [0]*s
        arm, value = point_arm_value(code, t)
        if arm:
            block[arm-1] = value
        out.extend(block)
    return tuple(out)


def construct_block(s: int, h: int, q: int) -> list[tuple[int, frozenset[tuple[int, ...]]]]:
    """Build the affine-line/singleton partition as actual point sets."""
    matching, t = hall_matching(s, h), q-1
    cells: list[tuple[int, frozenset[tuple[int, ...]]]] = []
    covered: set[tuple[int, ...]] = set()
    for f, top in sorted(matching.items()):
        z = f.index(0)
        fixed_indices = [j for j in range(h) if j != z]
        for values in it.product(range(1, q), repeat=h-1):
            base = [0]*h
            for j, value in zip(fixed_indices, values):
                base[j] = (f[j]-1)*t + value
            line = []
            for a in range(q):
                p = list(base)
                p[z] = 0 if a == 0 else (top[z]-1)*t + a
                line.append(tuple(p))
            cell = frozenset(line)
            assert len(cell) == q and covered.isdisjoint(cell)
            # Independently verify the actual coordinates form an affine line.
            field = Field(q)
            origin = cross_to_vector(tuple(base), s, t)
            axis = z*s + top[z]-1
            expected = set()
            for a in range(q):
                v = list(origin)
                v[axis] = field.add(v[axis], a)
                expected.add(tuple(v))
            assert {cross_to_vector(p, s, t) for p in cell} == expected
            covered.update(cell)
            cells.append((1, cell))
    universe = set(it.product(range(1+s*t), repeat=h))
    for p in sorted(universe-covered):
        cells.append((0, frozenset([p])))
    assert covered <= universe
    assert len(cells) == block_upper(s, h, q)
    return cells


def check_partition(s: int, m: int, q: int, cells: list[tuple[int, frozenset[tuple[int, ...]]]]) -> dict:
    t, N, M = q-1, (1+s*(q-1))**m, (s*(q-1))**m
    covered: set[tuple[int, ...]] = set()
    counts = [0]*(m+1)
    for d, cell in cells:
        assert len(cell) == q**d and covered.isdisjoint(cell)
        covered.update(cell)
        counts[d] += 1
    assert len(covered) == N
    assert covered == set(it.product(range(1+s*t), repeat=m))
    for k in range(m+1):
        rhs = Fraction(0)
        torus_total = 0
        for d, cell in cells:
            torus = sum(all(a != 0 for a in p) for p in cell)
            assert torus <= t**d
            torus_total += torus
            rhs += defect_weight(q, k, d) + power(t, 1-k)*(t**d-torus)
        assert torus_total == M
        assert Fraction(len(cells))-moment_bound(s, m, q, k) == rhs
    return {"arms": s, "blocks": m, "field_order": q, "points": N,
            "cells": len(cells), "cells_by_dimension": counts,
            "coverage_disjointness_and_defect_identity": "PASS"}


def check_algebra() -> dict:
    comparisons = 0
    for q in range(3, 18):
        for k in range(13):
            for d in range(13):
                g = defect_weight(q, k, d)
                assert g >= 0 and ((g == 0) == (d in (k, k+1)))
                if k >= 1 and d <= k-1:
                    assert g >= Fraction(q-2, q)
                if d >= k+2:
                    assert g >= (q-1)*(q-2)*power(q, d-k-2)
                comparisons += 1
    grid = []
    for s in range(2, 7):
        for m in range(1, 13):
            for q in (3, 4, 5, 7, 8, 9, 11, 13, 16):
                lower, upper = rounded_lower(s, m, q), product_upper(s, m, q)
                assert lower <= upper
                assert (upper-1) % (q-1) == 0 and (lower-1) % (q-1) == 0
                grid.append((s, m, q))
    for q in range(3, 31):
        assert rounded_lower(2, 1, q) == q
        assert rounded_lower(2, 2, q) == 4*q-3
        assert rounded_lower(2, 3, q) == 4*q*q-5*q+2
        B = moment_bound(2, 3, q, 1) + defect_weight(q, 1, 3)
        plane_bound = 1+(q-1)*ceil_fraction((B-1)/(q-1))
        assert plane_bound == 5*q*q-8*q+4
        if q >= 5:
            assert plane_bound > product_upper(2, 3, q)
    return {"nonnegative_weight_and_stability_comparisons": comparisons,
            "lower_upper_grid_cases": len(grid), "three_block_and_plane_formulas": "PASS",
            "status": "PASS"}


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O: this exact checker requires assertions to be enabled.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("verification_results.json"))
    args = parser.parse_args()
    algebra = check_algebra()
    flat_results = [check_flats(q, n) for q, n in ((3, 3), (4, 3), (5, 3), (7, 3), (3, 4))]
    matching_cases = []
    # Enumeration of all 6^6 top faces is unnecessary for finite corroboration.
    for s in range(2, 6):
        for h in range(1, s+1):
            matching = hall_matching(s, h)
            matching_cases.append({"arms": s, "blocks": h, "matched_facets": len(matching)})
    construction_cases = ((2, 1, 3), (2, 2, 3), (2, 2, 4), (2, 2, 5),
                          (3, 2, 3), (3, 3, 3), (3, 3, 5), (4, 4, 3))
    partitions = [check_partition(s, h, q, construct_block(s, h, q)) for s, h, q in construction_cases]
    pair = construct_block(2, 2, 3)
    product_cells = [(d+e, frozenset(x+y for x in a for y in b)) for d, a in pair for e, b in pair]
    partitions.append(check_partition(2, 4, 3, product_cells))
    results = {"status": "ALL EXACT CHECKS PASSED",
               "scope": "Finite corroboration, not a formal proof or an exhaustive optimization over partitions.",
               "arithmetic": "Integer and fractions.Fraction; F_4 uses u^2+u+1.",
               "algebra": algebra, "exhaustive_affine_flat_checks": flat_results,
               "total_distinct_affine_flats_checked": sum(r["total_flats"] for r in flat_results),
               "Hall_matchings": matching_cases, "actual_partition_checks": partitions}
    args.output.write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": results["status"], "distinct_affine_flats": results["total_distinct_affine_flats_checked"],
                      "Hall_matchings": len(matching_cases), "actual_partitions": len(partitions),
                      "results_file": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
