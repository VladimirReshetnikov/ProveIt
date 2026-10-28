#!/usr/bin/env python3
"""Exact adaptive contraction-tree selector and finite support certificate.

This implements plan construction and exact integer cost comparison, not a
SAT solver or a fast matrix multiplication backend. All list cardinalities
must be positive; an allocation with an empty list contributes zero and is
skipped before invoking the selector. Python standard library only.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations, product
import json
from math import prod
from pathlib import Path

DATA = Path(__file__).resolve().parents[1] / "data" / "portfolios.json"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_portfolios():
    return json.loads(DATA.read_text(encoding="utf-8"))["portfolios"]


def operations(r, blocks):
    """Return all matrix operations as three disjoint vertex classes."""
    require(len(blocks) == 3 and all(blocks), "Three nonempty blocks required")
    require(sorted(v for b in blocks for v in b) == list(range(r)),
            "Blocks must partition the group labels")
    universe = set(range(r))
    result = []

    def build(block):
        if len(block) <= 1:
            return
        middle = len(block) // 2
        left, right = block[:middle], block[middle:]
        build(left)
        build(right)
        result.append((tuple(left), tuple(right), tuple(sorted(universe-set(block)))))

    for block in blocks:
        build(block)
    result.append(tuple(tuple(b) for b in blocks))
    require(len(result) == r-2, "Wrong merge/triangle operation count")
    return result


def support_masks(r, blocks):
    edge_order = list(combinations(range(r), 2))
    result = []
    for classes in operations(r, blocks):
        vertex_class = {}
        for label, vertices in enumerate(classes):
            for v in vertices:
                vertex_class[v] = label
        for discount in combinations(range(3), 2):
            row = []
            for x, y in edge_order:
                pair = tuple(sorted((vertex_class[x], vertex_class[y])))
                row.append(0 if pair[0] == pair[1] else 2 if pair == discount else 5)
            result.append(tuple(row))
    require(len(result) == 3*(r-2), "Wrong support mask count")
    return result


def certify(r, trees):
    menus = [support_masks(r, tree) for tree in trees]
    dimension = r*(r-1)//2
    maximum = -1
    total = 0
    witness = None
    count = 0
    for indices in product(*(range(len(rows)) for rows in menus)):
        rows = [menus[j][i] for j, i in enumerate(indices)]
        value = sum(sum(v[e] for v in rows)**2 for e in range(dimension))
        if value > maximum:
            maximum, witness = value, indices
        total += value
        count += 1
    q = len(trees)
    return {
        "groups": r, "plan_count": q,
        "masks_per_plan": [len(x) for x in menus],
        "tuples_checked": count, "Q": maximum,
        "b_squared": str(Fraction(2*maximum, 25*q*q*r*r)),
        "first_maximum_tuple": witness, "squared_norm_sum": total,
    }


def select_plan(r, directed_dimensions, trees=None):
    """Select a certified plan using exact integer fifth powers of costs."""
    if trees is None:
        entries = [p for p in load_portfolios() if p["groups"] == r]
        require(len(entries) == 1, "No unique certified portfolio for this group count")
        trees = entries[0]["trees"]
    for g in range(r):
        for h in range(r):
            if g != h:
                require((g, h) in directed_dimensions, "Missing directed pair dimension")
                value = directed_dimensions[g, h]
                require(isinstance(value, int) and not isinstance(value, bool) and value > 0,
                        "All exact list cardinalities must be positive integers")
    dimensions = [directed_dimensions[g, h]*directed_dimensions[h, g]
                  for g, h in combinations(range(r), 2)]
    scores = []
    for tree in trees:
        scores.append(max(prod(d**v for d, v in zip(dimensions, row))
                          for row in support_masks(r, tree)))
    selected = min(range(len(trees)), key=lambda j: (scores[j], j))
    return {"groups": r, "selected_plan_index": selected,
            "maximum_operation_cost_power5": scores[selected],
            "all_plan_costs_power5": scores, "blocks": trees[selected]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimensions", type=Path,
                        help='JSON object with groups and dimensions [[g,h,size],...]')
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.dimensions:
        data = json.loads(args.dimensions.read_text(encoding="utf-8"))
        dims = {(g, h): size for g, h, size in data["dimensions"]}
        result = select_plan(data["groups"], dims)
    else:
        result = {"status": "PASS", "certificates": []}
        for entry in load_portfolios():
            cert = certify(entry["groups"], entry["trees"])
            require(cert["Q"] == entry["expected_Q"], "Support certificate maximum disagrees")
            require(cert["b_squared"] == entry["b_squared"], "Normalized squared coefficient disagrees")
            result["certificates"].append(cert)
    encoded = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")


if __name__ == "__main__":
    main()
