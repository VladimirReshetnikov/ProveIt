#!/usr/bin/env python3
"""Exact, independent finite checks for the preorder/root-polytope correspondence.

Python 3.10+; standard library only.  A preorder is encoded by a tuple of bitmasks:
row[i] = {j : j <= i}.  No floating-point arithmetic, CAS, or external packages.
Run from any directory: python code/verify.py --output data

These finite checks are a reproducibility aid, not a proof of the universal theorems.
"""
from __future__ import annotations
import argparse
import csv
import itertools
import json
from functools import lru_cache
from math import comb
from pathlib import Path
from typing import Iterator

Preorder = tuple[int, ...]
Vector = tuple[int, ...]


def bits(mask: int) -> Iterator[int]:
    if mask < 0:
        raise ValueError("bitmask must be nonnegative")
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


def is_preorder(rows: Preorder) -> bool:
    n = len(rows)
    return all(0 <= row < (1 << n) for row in rows) and all(
        (rows[i] >> i) & 1 for i in range(n)
    ) and all(rows[j] & ~rows[i] == 0 for i in range(n) for j in bits(rows[i]))


def all_preorders(n: int) -> Iterator[Preorder]:
    if n < 0:
        raise ValueError("n must be nonnegative")
    choices = [[s for s in range(1 << n) if s & (1 << i)] for i in range(n)]
    for rows in itertools.product(*choices):
        if all(rows[j] & ~rows[i] == 0 for i in range(n) for j in bits(rows[i])):
            yield rows


def transpose(rows: Preorder) -> Preorder:
    n = len(rows)
    return tuple(sum(1 << j for j in range(n) if rows[j] & (1 << i)) for i in range(n))


def closure(n: int, comparisons: list[tuple[int, int]]) -> Preorder:
    """Input (j,i) means j <= i; reflexive/transitive closure is returned."""
    rows = [1 << i for i in range(n)]
    for j, i in comparisons:
        if not (0 <= i < n and 0 <= j < n):
            raise ValueError("comparison outside ground set")
        rows[i] |= 1 << j
    for k in range(n):
        for i in range(n):
            if rows[i] & (1 << k):
                rows[i] |= rows[k]
    result = tuple(rows)
    assert is_preorder(result)
    return result


def ideals(rows: Preorder) -> tuple[int, ...]:
    return tuple(s for s in range(1 << len(rows))
                 if all(rows[i] & ~s == 0 for i in bits(s)))


@lru_cache(None)
def compositions(total: int, length: int) -> tuple[Vector, ...]:
    if length == 0:
        return ((),) if total == 0 else ()
    if length == 1:
        return ((total,),)
    return tuple((a,) + tail for a in range(total + 1)
                 for tail in compositions(total - a, length - 1))


def subset_sums(x: Vector) -> list[int]:
    ans = [0] * (1 << len(x))
    for s in range(1, len(ans)):
        b = s & -s
        ans[s] = ans[s ^ b] + x[b.bit_length() - 1]
    return ans


@lru_cache(None)
def candidates(n: int) -> tuple[tuple[Vector, int, int], ...]:
    ans = []
    for a in compositions(n, n + 1):
        x = a[1:]
        sums = subset_sums(x)
        bad = sum(1 << s for s, val in enumerate(sums) if val > s.bit_count())
        ans.append((x, bad, sum(v > 0 for v in x)))
    return tuple(ans)


def lattice_points(rows: Preorder) -> tuple[Vector, ...]:
    flags = sum(1 << s for s in ideals(rows))
    return tuple(x for x, bad, _ in candidates(len(rows)) if not (bad & flags))


def support_polynomial(rows: Preorder) -> tuple[int, ...]:
    flags = sum(1 << s for s in ideals(rows))
    h = [0] * (len(rows) + 1)
    for _, bad, k in candidates(len(rows)):
        if not (bad & flags):
            h[k] += 1
    return tuple(h)


def edges(rows: Preorder) -> tuple[tuple[int, int], ...]:
    """Both shores are indexed 0,...,n; 0 is universal on each shore."""
    n = len(rows)
    return tuple((i, j) for i in range(n + 1) for j in range(n + 1)
                 if i == 0 or j == 0 or rows[i - 1] & (1 << (j - 1)))


def spanning_tree_hypertrees(rows: Preorder) -> tuple[set[Vector], int]:
    n = len(rows)
    es = edges(rows)
    hypertrees: set[Vector] = set()
    count = 0
    for choice in itertools.combinations(es, 2 * n + 1):
        parent = list(range(2 * n + 2))
        degree = [0] * (n + 1)
        def root(v: int) -> int:
            while parent[v] != v:
                parent[v] = parent[parent[v]]
                v = parent[v]
            return v
        for i, j in choice:
            ri, rj = root(i), root(n + 1 + j)
            if ri == rj:
                break
            parent[ri] = rj
            degree[i] += 1
        else:
            count += 1
            hypertrees.add(tuple(d - 1 for d in degree))
    return hypertrees, count


def interior_polynomial(hypertrees: set[Vector]) -> tuple[int, ...]:
    n = len(next(iter(hypertrees))) - 1
    result = [0] * (n + 1)
    for a in hypertrees:
        inactive = 0
        for i in range(n + 1):
            if a[i] == 0:
                continue
            for j in range(i):
                b = list(a)
                b[i] -= 1
                b[j] += 1
                if tuple(b) in hypertrees:
                    inactive += 1
                    break
        result[inactive] += 1
    return tuple(result)


def matching_tree(rows: Preorder, x: Vector) -> tuple[tuple[int, int], ...]:
    """Produce a spanning-tree certificate for a given preorder lattice point."""
    n = len(rows)
    clones = [i for i, val in enumerate(x) for _ in range(val)]
    owner = [-1] * n
    def augment(c: int, seen: set[int]) -> bool:
        for j in bits(rows[clones[c]]):
            if j in seen:
                continue
            seen.add(j)
            if owner[j] < 0 or augment(owner[j], seen):
                owner[j] = c
                return True
        return False
    for c in range(len(clones)):
        if not augment(c, set()):
            raise ValueError("Hall matching failed; input is not a lattice point")
    tree = [(i, 0) for i in range(n + 1)]
    tree += [(0 if c < 0 else clones[c] + 1, j + 1) for j, c in enumerate(owner)]
    assert len(tree) == 2 * n + 1
    assert set(tree) <= set(edges(rows))
    actual = tuple(sum(i == k for i, _ in tree) - 1 for k in range(n + 1))
    assert actual == (n - sum(x),) + x
    return tuple(tree)


def semigroup_counts(rows: Preorder, max_m: int) -> list[int]:
    """Enumerate sums of graph-edge vectors directly, independent of Hall inequalities."""
    n = len(rows)
    es = edges(rows)
    current = {(0,) * (2 * n + 2)}
    counts = [1]
    for _ in range(max_m):
        nxt = set()
        for vector in current:
            for i, j in es:
                w = list(vector)
                w[i] += 1
                w[n + 1 + j] += 1
                nxt.add(tuple(w))
        current = nxt
        counts.append(len(current))
    return counts


def hall_counts(rows: Preorder, max_m: int) -> list[int]:
    """Lattice margins via the complete ideal-inequality description."""
    masks = tuple(s for s in ideals(rows) if s)
    n = len(rows)
    counts = []
    for m in range(max_m + 1):
        vectors = compositions(m, n + 1)
        sums = [(v[0], tuple(subset_sums(v[1:])[s] for s in masks)) for v in vectors]
        counts.append(sum(all(ui <= v0 + vi for ui, vi in zip(us, vs))
                          for _, us in sums for v0, vs in sums))
    return counts


def ehrhart_numerator(counts: list[int], dimension: int) -> tuple[int, ...]:
    return tuple(sum((-1) ** j * comb(dimension + 1, j) * counts[k - j]
                     for j in range(min(k, dimension + 1) + 1))
                 for k in range(len(counts)))


def predicted_counts(h: tuple[int, ...], dimension: int, max_m: int) -> list[int]:
    return [sum(h[k] * comb(m + dimension - k, dimension)
                for k in range(min(m, len(h) - 1) + 1)) for m in range(max_m + 1)]


def quotient_polar_points(rows: Preorder) -> tuple[Vector, ...]:
    """All ternary integer points of C_tau^polar (includes all its vertices)."""
    n = len(rows)
    return tuple(z for z in itertools.product((-1, 0, 1), repeat=n)
                 if all(z[i] - z[j] <= 1 for i in range(n) for j in bits(rows[i])))


def gauge(rows: Preorder, y: Vector) -> int:
    """Least dilation of the directed root polytope containing the integer y."""
    sums = subset_sums(y)
    return sum(max(-v, 0) for v in y) + max(sums[s] for s in ideals(rows))


def check_fibers_and_interior(rows: Preorder) -> tuple[int, int]:
    n = len(rows)
    ims = ideals(rows)
    fiber_checks = interior_checks = 0
    # All margin pairs at m=2, whether or not they belong to the root polytope.
    for u in compositions(2, n + 1):
        for v in compositions(2, n + 1):
            y = tuple(a - b for a, b in zip(u[1:], v[1:]))
            sums = subset_sums(y)
            a = max(sums[s] for s in ims)
            inside = all(sums[s] <= v[0] for s in ims)
            w = (v[0] - a,) + tuple(min(p, q) for p, q in zip(u[1:], v[1:]))
            assert inside == all(k >= 0 for k in w)
            assert sum(w) + gauge(rows, y) == 2
            neg = sum(max(-k, 0) for k in y)
            pos = sum(max(k, 0) for k in y)
            base_u = (a + neg - pos,) + tuple(max(k, 0) for k in y)
            base_v = (a,) + tuple(max(-k, 0) for k in y)
            assert u == tuple(p + q for p, q in zip(base_u, w))
            assert v == tuple(p + q for p, q in zip(base_v, w))
            fiber_checks += 1
    # Enumerate strictly positive margins in dilations n+1,n+2,n+3.
    # The empty-preorder point has a separate relative-interior convention.
    if n:
        for extra in range(3):
            positive = [tuple(k + 1 for k in u) for u in compositions(extra, n + 1)]
            for u in positive:
                for v in positive:
                    us, vs = subset_sums(u[1:]), subset_sums(v[1:])
                    interior = all(us[s] < v[0] + vs[s] for s in ims if s)
                    uu, vv = tuple(k - 1 for k in u), tuple(k - 1 for k in v)
                    uus, vvs = subset_sums(uu[1:]), subset_sums(vv[1:])
                    exterior = all(uus[s] <= vv[0] + vvs[s] for s in ims if s)
                    assert interior == exterior
                    interior_checks += 1
    return fiber_checks, interior_checks


def quotient_counts(rows: Preorder, max_m: int) -> list[int]:
    polar = quotient_polar_points(rows)
    n = len(rows)
    result = []
    ims = ideals(rows)
    for m in range(max_m + 1):
        count = 0
        for x in itertools.product(range(-m, m + 1), repeat=n):
            polar_test = all(sum(a * b for a, b in zip(x, z)) <= m for z in polar)
            sums = subset_sums(x)
            norm_test = sum(max(-k, 0) for k in x) + max(sums[s] for s in ims) <= m
            assert polar_test == norm_test
            count += polar_test
        result.append(count)
    return result


def check_hall_reduction(rows: Preorder) -> int:
    """Compare all-subset Hall constraints with the ideal reduction at m=2."""
    n = len(rows)
    neigh = []
    for s in range(1 << n):
        d = 0
        for i in bits(s):
            d |= rows[i]
        neigh.append(d)
    ims = ideals(rows)
    tests = 0
    for u in compositions(2, n + 1):
        us = subset_sums(u[1:])
        for v in compositions(2, n + 1):
            vs = subset_sums(v[1:])
            all_hall = all(us[s] <= v[0] + vs[neigh[s]] for s in range(1 << n))
            ideal_hall = all(us[s] <= v[0] + vs[s] for s in ims)
            assert all_hall == ideal_hall
            tests += 1
    return tests


def check_special_simplex(rows: Preorder) -> int:
    """Check the zero set of every displayed supporting inequality on the diagonal."""
    n = len(rows)
    diag = range(n + 1)
    checks = 0
    for i in range(n + 1):
        assert sum(j != i for j in diag) == n  # u_i=0, and the same for v_i
        checks += 2
    for s in ideals(rows):
        if not s:
            continue
        slacks = [int(j == 0) for j in diag]  # v0+v(I)-u(I) at d_j
        assert slacks.count(0) == n and slacks[0] == 1
        for i, j in edges(rows):
            slack = int(j == 0) + int(j > 0 and bool(s & (1 << (j - 1))))
            slack -= int(i > 0 and bool(s & (1 << (i - 1))))
            assert slack in (0, 1)
        checks += 1
    return checks


def examples() -> dict[str, Preorder]:
    return {
        "antichain_4": closure(4, []),
        "chain_4": closure(4, [(0, 1), (1, 2), (2, 3)]),
        "indiscrete_4": (15, 15, 15, 15),
        "one_minimum_three_maxima": closure(4, [(0, 1), (0, 2), (0, 3)]),
        "diamond_4": closure(4, [(0, 1), (0, 2), (1, 3), (2, 3)]),
        # a~c<e, b<e, b<d; indices a,b,c,d,e.
        "paper_running_5": closure(5, [(0, 2), (2, 0), (0, 4), (1, 4), (1, 3)]),
        "crown_6": closure(6, [(0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (0, 5)]),
    }


def main() -> None:
    if not __debug__:
        raise SystemExit("Do not use Python -O: assertions are required for verification.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "data")
    parser.add_argument("--max-preorder-n", type=int, default=5, choices=range(0, 6))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    results: dict[str, object] = {"arithmetic": "exact integers; Python standard library", "exhaustive": []}
    all_small: dict[int, list[Preorder]] = {}
    enumerated_rows = []
    expected = [1, 1, 4, 29, 355, 6942]
    for n in range(args.max_preorder_n + 1):
        ps = list(all_preorders(n))
        assert len(ps) == expected[n], (n, len(ps))
        if n <= 3:
            all_small[n] = ps
        for rows in ps:
            h = support_polynomial(rows)
            assert h == support_polynomial(transpose(rows))
            assert h == h[::-1]
            assert all(h[k] <= h[k + 1] for k in range(n // 2))
            assert h[0] == h[-1] == 1
            if n:
                assert h[1] == sum(r.bit_count() for r in rows)
            check_special_simplex(rows)
            enumerated_rows.append([n, ";".join(map(str, rows)), ";".join(map(str, h))])
        entry = {"n": n, "labeled_preorders": len(ps), "duality_palindromicity_unimodality": "PASS"}
        results["exhaustive"].append(entry)  # type: ignore[union-attr]
        print(entry, flush=True)
    with (args.output / "preorders_through_5.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["n", "principal_ideal_bitmasks", "h_coefficients"])
        writer.writerows(enumerated_rows)

    tree_instances = tree_total = hall_checks = certificates = 0
    fiber_checks = interior_checks = 0
    small_details = []
    for n, ps in all_small.items():
        for rows in ps:
            h = support_polynomial(rows)
            hs, tree_count = spanning_tree_hypertrees(rows)
            expected_hs = {(n - sum(x),) + x for x in lattice_points(rows)}
            assert hs == expected_hs
            assert interior_polynomial(hs) == h
            for x in lattice_points(rows):
                matching_tree(rows, x)
                certificates += 1
            tree_instances += 1
            tree_total += tree_count
            counts = semigroup_counts(rows, 2 * n)
            assert counts == hall_counts(rows, 2 * n)
            assert counts == predicted_counts(h, 2 * n, 2 * n)
            numerator = ehrhart_numerator(counts, 2 * n)
            assert numerator == h + (0,) * n
            qc = quotient_counts(rows, n)
            assert qc == predicted_counts(h, n, n)
            assert ehrhart_numerator(qc, n) == h
            hall_checks += check_hall_reduction(rows)
            fc, ic = check_fibers_and_interior(rows)
            fiber_checks += fc
            interior_checks += ic
            small_details.append({"n": n, "rows": rows, "h": h, "spanning_trees": tree_count,
                                  "hypertrees": len(hs), "root_counts": counts, "quotient_counts": qc})
        print(f"independent trees, semigroup, margins, quotient: n={n} PASS", flush=True)
    results["independent_small_cases"] = {
        "preorders": tree_instances, "spanning_trees_enumerated": tree_total,
        "matching_certificates_checked": certificates, "hall_margin_pairs": hall_checks,
        "fiber_margin_pairs": fiber_checks, "interior_translation_pairs": interior_checks,
        "root_degrees_checked": "all m=0,...,2n", "quotient_degrees_checked": "all m=0,...,n",
        "details": small_details}

    ex_details = []
    for name, rows in examples().items():
        n = len(rows)
        h = support_polynomial(rows)
        assert h == h[::-1] == support_polynomial(transpose(rows))
        item: dict[str, object] = {"name": name, "n": n, "rows": rows, "h": h,
                                  "points": sum(h), "graph_edges": len(edges(rows))}
        if n == 4:
            counts = hall_counts(rows, 2 * n)
            assert counts == predicted_counts(h, 2 * n, 2 * n)
            assert ehrhart_numerator(counts, 2 * n) == h + (0,) * n
            qc = quotient_counts(rows, n)
            assert qc == predicted_counts(h, n, n)
            assert ehrhart_numerator(qc, n) == h
            assert semigroup_counts(rows, 3) == counts[:4]
            item.update(root_counts=counts, quotient_counts=qc)
        if name == "paper_running_5":
            assert h == (1, 11, 34, 34, 11, 1)
            x = (0, 0, 1, 2, 2)
            assert x in lattice_points(rows)
            item["sample_x"] = x
            item["sample_matching_tree"] = matching_tree(rows, x)
        ex_details.append(item)
        print(f"example {name}: {h} PASS", flush=True)
    results["examples"] = ex_details
    results["result"] = "ALL CHECKS PASSED"
    with (args.output / "verification_results.json").open("w") as f:
        json.dump(results, f, indent=2)
        f.write("\n")
    print("ALL CHECKS PASSED", flush=True)


if __name__ == "__main__":
    main()
