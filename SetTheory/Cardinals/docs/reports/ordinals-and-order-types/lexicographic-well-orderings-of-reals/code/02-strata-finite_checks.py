#!/usr/bin/env python3
"""Exact finite checks accompanying the lexicographic well-ordering article.

Python 3.10+; standard library only. No finite test in this file verifies an
infinitary theorem. Run: python finite_checks.py --output finite_checks.json
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from itertools import combinations, permutations, product
import json
from math import factorial
from pathlib import Path
from typing import Iterable

COUNTS: Counter[str] = Counter()


def check(condition: bool, category: str, witness: object = None) -> None:
    """Unlike assert, this remains active under python -O."""
    if not condition:
        raise AssertionError(f"{category}: failed on {witness!r}")
    COUNTS[category] += 1


def pair_swap(bits: tuple[int, ...]) -> tuple[int, ...]:
    if any(bit not in (0, 1) for bit in bits):
        raise ValueError("Expected binary digits")
    return tuple(v for i, bit in enumerate(bits)
                 for v in ((2*i, 2*i+1) if bit == 0 else (2*i+1, 2*i)))


def predicted_adjacent(e: tuple[int, ...], f: tuple[int, ...]) -> bool:
    """The residual-set criterion, specialized to finite exhaustive words."""
    if len(e) != len(f) or set(e) != set(f) or not e < f:
        raise ValueError("Expected increasing permutations of the same set")
    delta = next(i for i in range(len(e)) if e[i] != f[i])
    unused = set(e[delta:])
    a, b = e[delta], f[delta]
    consecutive = not any(a < c < b for c in unused)
    last_a = e[delta+1:] == tuple(sorted(unused - {a}, reverse=True))
    first_b = f[delta+1:] == tuple(sorted(unused - {b}))
    return consecutive and last_a and first_b


def check_pair_swaps() -> None:
    for n in range(11):
        images = [pair_swap(bits) for bits in product((0, 1), repeat=n)]
        for image in images:
            check(sorted(image) == list(range(2*n)), "pair_swap_exhaustion", (n, image))
        for e, f in zip(images, images[1:]):
            check(e < f, "pair_swap_order", (n, e, f))
        check(len(set(images)) == 2**n, "pair_swap_injectivity", n)


def check_cut_codes() -> None:
    for n in range(1, 8):
        for order in permutations(range(n)):
            rank = {x: i for i, x in enumerate(order)}
            codes = {
                x: tuple(int(rank[t] <= rank[x]) for t in range(n))
                for x in order
            }
            for x, y in combinations(order, 2):
                check(codes[x] < codes[y], "cut_code_order", (order, x, y))


def check_permutation_adjacency() -> None:
    for n in range(2, 7):
        words = list(permutations(range(n)))
        for i, e in enumerate(words):
            for j in range(i+1, len(words)):
                check(predicted_adjacent(e, words[j]) == (j == i+1),
                      "adjacency_all_pairs", (n, i, j))
    for n in range(2, 9):
        words = list(permutations(range(n)))
        for e, f in zip(words, words[1:]):
            check(predicted_adjacent(e, f), "adjacency_consecutive", (n, e, f))


def check_residual_cylinders() -> None:
    for n in range(8):
        positions: dict[tuple[int, ...], list[int]] = defaultdict(list)
        for index, word in enumerate(permutations(range(n))):
            for length in range(n+1):
                positions[word[:length]].append(index)
        for prefix, indexes in positions.items():
            check(len(indexes) == factorial(n-len(prefix)),
                  "cylinder_factorial_size", (n, prefix))
            check(indexes[-1] - indexes[0] + 1 == len(indexes),
                  "cylinder_convexity", (n, prefix))


def check_child_cuts() -> None:
    for depth in range(1, 7):
        for factor in range(1, 8):
            for prefix_length in range(depth):
                child_size = 2**(depth-prefix_length-1)*factor
                for prefix_rank in range(2**prefix_length):
                    start = prefix_rank * 2*child_size
                    lower = range(start, start+child_size)
                    upper = range(start+child_size, start+2*child_size)
                    for retained_size in range(2*child_size+1):
                        cutoff = start+retained_size
                        lower_inside = lower[-1] < cutoff
                        upper_outside = upper[0] >= cutoff
                        check(lower_inside or upper_outside,
                              "full_child_cut", (depth, factor, prefix_length,
                                                 prefix_rank, retained_size))


def check_concatenation() -> None:
    for n in range(1, 6):
        for m in range(1, 6):
            sources = list(product(permutations(range(n)), permutations(range(m))))
            images = [tuple(2*x for x in e) + tuple(2*y+1 for y in f)
                      for e, f in sources]
            ground = {2*x for x in range(n)} | {2*y+1 for y in range(m)}
            for image in images:
                check(set(image) == ground and len(image) == len(ground),
                      "concatenation_exhaustion", (n, m, image))
            for e, f in zip(images, images[1:]):
                check(e < f, "concatenation_order", (n, m, e, f))


def capacities(values: Iterable[int], category: str) -> None:
    for m in values:
        if m <= 0:
            raise ValueError("The finite factor must be positive")
        floor = m.bit_length()-1
        ceil = (m-1).bit_length()
        check(2**floor <= m < 2**(floor+1), category+"_floor", m)
        check(m <= 2**ceil and (ceil == 0 or 2**(ceil-1) < m),
              category+"_ceil", m)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("finite_checks.json"))
    args = parser.parse_args()
    check_pair_swaps()
    check_cut_codes()
    check_permutation_adjacency()
    check_residual_cylinders()
    check_child_cuts()
    check_concatenation()
    capacities(range(1, 10001), "finite_capacity")
    capacities((factorial(n) for n in range(51)), "factorial_capacity")
    report = {
        "status": "passed",
        "scope": "Exact finite tests only; no transfinite theorem is machine-verified.",
        "parameters": {
            "pair_swap_pair_counts": [0, 10],
            "cut_code_order_sizes": [1, 7],
            "adjacency_all_pairs_sizes": [2, 6],
            "adjacency_consecutive_sizes": [2, 8],
            "cylinder_ground_sizes": [0, 7],
            "full_child_cube_depths": [1, 6],
            "full_child_finite_factors": [1, 7],
            "concatenation_factor_sizes": [1, 5],
            "finite_capacity_factors": [1, 10000],
            "factorial_capacity_arguments": [0, 50],
        },
        "checks": dict(sorted(COUNTS.items())),
        "total_checks": sum(COUNTS.values()),
        "example_final_permutations": [list(p) for p in permutations(range(3))],
        "example_factorial_capacities": [
            {"n": n, "factorial": factorial(n),
             "floor_binary_digits": factorial(n).bit_length()-1,
             "ceil_binary_digits": (factorial(n)-1).bit_length()}
            for n in range(11)
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "total_checks": report["total_checks"],
                      "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
