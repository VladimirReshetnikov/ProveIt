#!/usr/bin/env python3
"""Independent exact check of finite adaptive contraction-tree certificates.

This implementation does not import the exploratory/search implementation.
It reconstructs matrix-operation support vectors by assigning each vertex one
of three labels and classifying each undirected edge by its endpoint labels.
All certificate maxima are computed with integer arithmetic. Floating-point
coefficient displays are informational only.

Default: verify the final three-tree r=9 and r=13 certificates and an
earlier two-tree r=8 control, all embedded below.
With --candidates PATH: additionally verify selected entries in the supplied
candidate JSON. Default selected entries are (9, 3) and (13, 3); use --key
repeatedly to select others. The candidate score and coefficient fields are
ignored when constructing the exact certificate.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations, product
import json
from math import sqrt
from pathlib import Path


R8_TREES = [
    [[0, 1, 2], [3, 4, 5], [6, 7]],
    [[2, 4, 7], [6, 0, 5], [1, 3]],
]

R9_TREES = [
    [[0, 1, 2], [3, 4, 5], [6, 7, 8]],
    [[6, 2, 5], [4, 7, 0], [1, 8, 3]],
    [[5, 2, 8], [4, 6, 1], [0, 7, 3]],
]

R13_TREES = [
    [[0, 1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]],
    [[12, 10, 1, 6, 4], [9, 0, 3, 8], [5, 2, 7, 11]],
    [[0, 8, 11, 12, 1], [7, 10, 4, 3], [5, 2, 6, 9]],
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def independent_rows(r: int, blocks: list[list[int]]) -> list[tuple[int, ...]]:
    """Return 5 times each possible local exponent's edge-support vector."""
    require(r >= 3, "At least three groups are required")
    require(len(blocks) == 3, "Exactly three final blocks are required")
    require(all(blocks), "Final blocks must be nonempty")
    require(sorted(v for b in blocks for v in b) == list(range(r)),
            "Final blocks must partition the vertices exactly once")
    edge_list = list(combinations(range(r), 2))
    rows: list[tuple[int, ...]] = []

    def classify(parts: tuple[tuple[int, ...], ...]) -> None:
        labels = {v: i for i, part in enumerate(parts) for v in part}
        require(sorted(v for part in parts for v in part) == list(range(r)),
                "A merge tripartition does not cover the graph exactly once")
        for discounted_pair in ((0, 1), (0, 2), (1, 2)):
            row = []
            for x, y in edge_list:
                lo, hi = sorted((labels[x], labels[y]))
                row.append(0 if lo == hi else
                           2 if (lo, hi) == discounted_pair else 5)
            rows.append(tuple(row))

    def build(block: tuple[int, ...]) -> None:
        if len(block) < 2:
            return
        cut = len(block) // 2
        left, right = block[:cut], block[cut:]
        outside = tuple(v for v in range(r) if v not in block)
        build(left)
        build(right)
        classify((left, right, outside))

    final_parts = tuple(tuple(b) for b in blocks)
    for block in final_parts:
        build(block)
    classify(final_parts)
    require(len(rows) == 3 * (r - 2), "Unexpected number of operation masks")
    require(all(len(row) == r * (r - 1) // 2 for row in rows),
            "Unexpected support-vector dimension")
    require(all(x in (0, 2, 5) for row in rows for x in row),
            "Unexpected support-vector weight")
    return rows


def certificate(r: int, trees: list[list[list[int]]]) -> dict:
    require(len(trees) > 0, "Certificate requires at least one tree")
    matrix_sets = [independent_rows(r, tree) for tree in trees]
    edge_count = r * (r - 1) // 2
    max_sq = -1
    best_indices = None
    count = 0
    checksum = 0
    for indices in product(*(range(len(rows)) for rows in matrix_sets)):
        selected = [matrix_sets[t][idx] for t, idx in enumerate(indices)]
        squared = sum(sum(row[e] for row in selected) ** 2
                      for e in range(edge_count))
        checksum += squared
        count += 1
        if squared > max_sq:
            max_sq = squared
            best_indices = indices
    q = len(trees)
    coefficient_squared = Fraction(2 * max_sq, 25 * q * q * r * r)
    return {
        "groups": r,
        "trees": q,
        "operation_counts": [len(rows) for rows in matrix_sets],
        "cartesian_operation_tuples": count,
        "maximum_sum_squared_norm": max_sq,
        "maximum_average_squared_norm": str(Fraction(max_sq, q * q)),
        "coefficient_squared_exact": str(coefficient_squared),
        "coefficient_display": sqrt(float(coefficient_squared)),
        "first_maximizing_operation_tuple": best_indices,
        "sum_of_all_squared_norms": checksum,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidates", type=Path)
    parser.add_argument("--key", action="append")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    results = {
        "control_r8_two_tree": certificate(8, R8_TREES),
        "headline_r9_three_tree": certificate(9, R9_TREES),
        "headline_r13_three_tree": certificate(13, R13_TREES),
    }
    r8 = results["control_r8_two_tree"]
    require(r8["maximum_sum_squared_norm"] == 1276,
            "Independent r=8 certificate did not match 1276")
    require(r8["cartesian_operation_tuples"] == 324,
            "Independent r=8 enumeration did not have 324 pairs")
    require(r8["coefficient_squared_exact"] == "319/800",
            "Independent r=8 normalized coefficient disagrees")
    for key, expected_q, expected_count, expected_b_squared in [
        ("headline_r9_three_tree", 3304, 9261, "6608/18225"),
        ("headline_r13_three_tree", 7074, 35937, "1572/4225"),
    ]:
        result = results[key]
        require(result["maximum_sum_squared_norm"] == expected_q,
                key + ": integer norm maximum disagrees")
        require(result["cartesian_operation_tuples"] == expected_count,
                key + ": operation tuple count disagrees")
        require(result["coefficient_squared_exact"] == expected_b_squared,
                key + ": normalized coefficient disagrees")
    if args.candidates:
        data = json.loads(args.candidates.read_text(encoding="utf-8"))
        for key in args.key or ["(9, 3)", "(13, 3)"]:
            entry = data[key]
            result = certificate(entry["r"], entry["trees"])
            results["external_" + key] = result
    encoded = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")


if __name__ == "__main__":
    main()
