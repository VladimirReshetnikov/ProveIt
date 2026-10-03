#!/usr/bin/env python3
"""Finite regression checks for the accompanying research manuscript.

These checks test first-disagreement combinatorics and finite labelled
orders. They do not verify cardinal arithmetic, transfinite topology,
Borel complexity, or statements about proper classes.
"""
from __future__ import annotations

import argparse
import itertools
import json
from collections import defaultdict
from pathlib import Path

COUNTS: dict[str, int] = defaultdict(int)


def check(condition: bool, category: str) -> None:
    COUNTS[category] += 1
    if not condition:
        raise AssertionError(f"Failed {category}, assertion {COUNTS[category]}")


def bits(value: int, depth: int) -> tuple[int, ...]:
    return tuple((value >> (depth - n - 1)) & 1 for n in range(depth))


def release_checks(max_depth: int = 4) -> dict[str, int]:
    configurations = 0
    for depth in range(max_depth + 1):
        size = 1 << depth
        words = [bits(z, depth) for z in range(size)]
        masks: list[list[int]] = [[0] * depth for _ in range(size)]
        for z in range(size):
            for a in range(size):
                for n in range(depth):
                    if words[a][n] != words[z][n]:
                        masks[z][n] |= 1 << a
                        break
        # All subsets A of all depth-d binary branches, and all input z.
        for a_mask in range(1 << size):
            for z in range(size):
                configurations += 1
                released = 0
                for n in range(depth):
                    current = a_mask & masks[z][n]
                    check(not (released & current), "release_disjointness")
                    released |= current
                check(released == (a_mask & ~(1 << z)), "release_exact_union")
        # Stage n uses only the first n+1 input bits.
        for n in range(depth):
            seen: dict[tuple[int, ...], int] = {}
            for z, word in enumerate(words):
                prefix = word[: n + 1]
                if prefix in seen:
                    check(seen[prefix] == masks[z][n], "release_prefix_dependence")
                else:
                    seen[prefix] = masks[z][n]
    return {"max_depth": max_depth, "subset_branch_configurations": configurations}


def marker_checks(max_depth: int = 9) -> dict[str, int]:
    pairs = 0
    for depth in range(max_depth + 1):
        words = [bits(z, depth) for z in range(1 << depth)]
        encoded = [tuple(v for n, bit in enumerate(word)
                         for v in (2*n + bit, 2*n + 1 - bit))
                   for word in words]
        for i, j in itertools.combinations(range(len(words)), 2):
            pairs += 1
            check((words[i] < words[j]) == (encoded[i] < encoded[j]),
                  "marker_order_preservation")
            n = next(k for k in range(depth) if words[i][k] != words[j][k])
            m = next(k for k in range(2*depth) if encoded[i][k] != encoded[j][k])
            check(m == 2*n, "marker_first_disagreement")
    return {"max_depth": max_depth, "pairs": pairs}


def rank_map(p: tuple[int, ...]) -> dict[int, int]:
    return {x: i for i, x in enumerate(p)}


def raw_compare(p: tuple[int, ...], q: tuple[int, ...]) -> int:
    """Use equal predecessor sets AND agreement of induced relations."""
    rp, rq = rank_map(p), rank_map(q)
    common: set[int] = set()
    for x in p:
        left = {y for y in p if rp[y] < rp[x]}
        right = {y for y in q if rq[y] < rq[x]}
        if left == right and all((rp[y] < rp[z]) == (rq[y] < rq[z])
                                 for y in left for z in left):
            common.add(x)
    if len(common) == len(p):
        return 0
    a = next(x for x in p if x not in common)
    b = next(x for x in q if x not in common)
    check(a != b, "raw_distinct_next_labels")
    return (a > b) - (a < b)


def order_checks(max_size: int = 5) -> dict[str, int]:
    pairs = 0
    for n in range(max_size + 1):
        perms = list(itertools.permutations(range(n)))
        for p in perms:
            for q in perms:
                pairs += 1
                check(raw_compare(p, q) == ((p > q) - (p < q)),
                      "raw_vs_enumeration_lex")
    # Relation-code order can reverse enumeration order.
    p, q = (0, 1, 2), (1, 0, 2)
    coords = [(0, 1)] + [c for c in itertools.product(range(3), repeat=2)
                         if c != (0, 1)]
    rp, rq = rank_map(p), rank_map(q)
    cp = tuple(int(rp[a] < rp[b]) for a, b in coords)
    cq = tuple(int(rq[a] < rq[b]) for a, b in coords)
    check(p < q and cp > cq, "relation_code_reversal_example")
    return {"max_size": max_size, "ordered_pairs": pairs}


def cylinder_checks(max_size: int = 7) -> dict[str, int]:
    cylinders = 0
    for n in range(max_size + 1):
        positions: dict[tuple[int, ...], list[int]] = defaultdict(list)
        for index, p in enumerate(itertools.permutations(range(n))):
            for length in range(n + 1):
                positions[p[:length]].append(index)
        for locs in positions.values():
            cylinders += 1
            check(locs[-1] - locs[0] + 1 == len(locs), "prefix_cylinder_convexity")
    return {"max_size": max_size, "cylinders": cylinders}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("data/finite_checks.json"))
    args = parser.parse_args()
    report = {
        "status": "PASS",
        "scope": "Finite combinatorial regression checks only; not a transfinite proof.",
        "release": release_checks(),
        "markers": marker_checks(),
        "class_comparison_finite_model": order_checks(),
        "cylinders": cylinder_checks(),
        "assertions_by_category": dict(sorted(COUNTS.items())),
        "total_assertions": sum(COUNTS.values()),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
