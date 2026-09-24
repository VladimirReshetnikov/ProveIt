#!/usr/bin/env python3
"""Bounded sanity checks for the two padding constructions in the article.

These tests check finite containments and finite error-projection identities.
They do NOT prove infinitude, maximality, Turing/Medvedev reducibility, or novelty.
Only the Python standard library is required (Python 3.10 or newer).
"""
from __future__ import annotations

import argparse
import itertools
import random
from collections.abc import Iterator, Sequence

Point = tuple[int, int]


def subsets(items: Sequence) -> Iterator[set]:
    """Enumerate the subsets of a short finite sequence."""
    for mask in range(1 << len(items)):
        yield {item for i, item in enumerate(items) if mask & (1 << i)}


def first_coordinates(points: set[Point]) -> set[int]:
    return {x for x, _ in points}


def weak_padding(columns: list[set[int]], width: int) -> tuple[list[set[int]], list[set[Point]]]:
    intersection = set(range(width))
    intersections: list[set[int]] = []
    output: list[set[Point]] = []
    for n, column in enumerate(columns):
        intersection = intersection & column
        intersections.append(intersection)
        output.append({(x, y) for x in intersection for y in range(n, x + 1)})
    return intersections, output


def check_weak(columns: list[set[int]], points: set[Point], width: int) -> None:
    intersections, output = weak_padding(columns, width)
    projected = {x for x, y in points if y <= x}
    for n, (intersection, current) in enumerate(zip(intersections, output)):
        assert projected - intersection <= first_coordinates(points - current)
        if n + 1 < len(output):
            assert output[n + 1] <= current
            removed_layer = {(x, n) for x in intersection if n <= x}
            assert removed_layer <= current - output[n + 1]


def function_padding(columns: list[list[int]]) -> list[set[Point]]:
    return [
        {(x, y) for x, value in enumerate(column) for y in range(n, value)}
        for n, column in enumerate(columns)
    ]


def check_function(columns: list[list[int]], points: set[Point]) -> None:
    output = function_padding(columns)
    width = len(columns[0])
    h = [
        max([0] + [y + 1 for y in range(columns[0][x]) if (x, y) in points])
        for x in range(width)
    ]
    for n, (column, current) in enumerate(zip(columns, output)):
        error = {x for x in range(width) if h[x] > column[x]}
        assert error <= first_coordinates(points - current)
        if points & output[0] & current:
            assert max(h) > n
        if n + 1 < len(output):
            next_column = columns[n + 1]
            exceptional_rows = {x for x in range(width) if next_column[x] > column[x]}
            error_region = {
                (x, y) for x in exceptional_rows for y in range(next_column[x])
            }
            assert output[n + 1] - current <= error_region
            removed_layer = {(x, n) for x in range(width) if column[x] > n}
            assert removed_layer <= current - output[n + 1]


def run(seed: int, trials: int) -> dict[str, int]:
    counts = {"exhaustive_weak": 0, "exhaustive_function": 0,
              "random_weak": 0, "random_function": 0}
    width = 3
    possible_columns = list(subsets(list(range(width))))
    universe = [(x, y) for x in range(width) for y in range(width + 1)]
    for first in possible_columns:
        for second in possible_columns:
            for points in subsets(universe):
                check_weak([first, second], points, width)
                counts["exhaustive_weak"] += 1

    width = 2
    universe = [(x, y) for x in range(width) for y in range(4)]
    for values in itertools.product(range(3), repeat=2 * width):
        columns = [list(values[:width]), list(values[width:])]
        for points in subsets(universe):
            check_function(columns, points)
            counts["exhaustive_function"] += 1

    rng = random.Random(seed)
    for _ in range(trials):
        width, depth = rng.randint(2, 12), rng.randint(2, 7)
        columns = [{x for x in range(width) if rng.randrange(2)} for _ in range(depth)]
        # Include y > x, so the bounded projection is not confused with projection.
        points = {(x, y) for x in range(width) for y in range(width + 3)
                  if rng.randrange(3) == 0}
        check_weak(columns, points, width)
        counts["random_weak"] += 1

        functions = [[rng.randrange(20) for _ in range(width)] for _ in range(depth)]
        # No monotonicity restriction: test the exceptional-row identity too.
        points = {(x, y) for x in range(width) for y in range(23)
                  if rng.randrange(4) == 0}
        check_function(functions, points)
        counts["random_function"] += 1
    return counts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260917)
    parser.add_argument("--trials", type=int, default=2000)
    args = parser.parse_args()
    if args.trials < 0:
        parser.error("--trials must be nonnegative")
    print("Finite padding sanity checks")
    print(f"seed={args.seed}; randomized trials per construction={args.trials}")
    counts = run(args.seed, args.trials)
    for name, count in counts.items():
        print(f"PASS {name}: {count} instances")
    print(f"PASS total: {sum(counts.values())} instances")
    print("Not a proof of infinitude, maximality, reducibility, or novelty.")
    print("No Lean compilation is performed by this program.")


if __name__ == "__main__":
    main()
