#!/usr/bin/env python3
"""Exhaustive checks for finite simple graphs of maximum degree two.

No external dependencies. A graph is represented, up to isomorphism, by
(sorted path vertex counts, sorted cycle vertex counts).

Three algorithms are compared (the packing variants share a path solver):
  1. closure under elementary vertex/edge deletions and edge contractions;
  2. exhaustive allocation of cycles followed by exact path bin packing;
  3. greedy cycle allocation followed by the same exact path bin packing.
Neither algorithm computes a transfinite rank. See the accompanying paper.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
import sys
import time
from collections import Counter
from functools import lru_cache
from pathlib import Path
from typing import Iterator, Tuple

Graph = Tuple[Tuple[int, ...], Tuple[int, ...]]
EMPTY: Graph = ((), ())


def canonical(paths=(), cycles=()) -> Graph:
    """Canonicalize and validate a component description."""
    p, c = tuple(sorted(paths)), tuple(sorted(cycles))
    if any(not isinstance(n, int) or n < 1 for n in p):
        raise ValueError("Path vertex counts must be positive integers.")
    if any(not isinstance(n, int) or n < 3 for n in c):
        raise ValueError("Simple cycles must have at least three vertices.")
    return p, c


def vertices(g: Graph) -> int:
    return sum(g[0]) + sum(g[1])


def edges(g: Graph) -> int:
    return sum(n - 1 for n in g[0]) + sum(g[1])


def partitions(n: int, lower: int = 1) -> Iterator[Tuple[int, ...]]:
    if n == 0:
        yield ()
    else:
        for first in range(lower, n + 1):
            for rest in partitions(n - first, first):
                yield (first,) + rest


def all_graphs(max_vertices: int) -> list[Graph]:
    result = []
    for n in range(max_vertices + 1):
        for cycle_total in range(n + 1):
            for cycles in partitions(cycle_total, 3):
                for paths in partitions(n - cycle_total):
                    result.append((paths, cycles))
    return sorted(result, key=lambda g: (vertices(g), edges(g), g))


def immediate_minors(g: Graph) -> set[Graph]:
    """One elementary operation, with loops/parallel edges suppressed.

    For paths we include every vertex position and every edge position.
    All cycle positions are equivalent by rotation. In particular,
    contracting an edge of C_3 gives P_2, not a forbidden two-cycle.
    """
    paths, cycles = g
    result: set[Graph] = set()
    for i, n in enumerate(paths):
        other = paths[:i] + paths[i + 1:]
        # Delete a vertex: sizes on the two remaining sides sum to n-1.
        for left in range(n):
            pieces = tuple(t for t in (left, n - 1 - left) if t)
            result.add(canonical(other + pieces, cycles))
        # Delete an edge: the resulting sizes sum to n.
        for left in range(1, n):
            result.add(canonical(other + (left, n - left), cycles))
        # Contract an edge.
        if n >= 2:
            result.add(canonical(other + (n - 1,), cycles))
    for i, n in enumerate(cycles):
        other = cycles[:i] + cycles[i + 1:]
        result.add(canonical(paths + (n - 1,), other))  # vertex deletion
        result.add(canonical(paths + (n,), other))      # edge deletion
        if n == 3:
            result.add(canonical(paths + (2,), other))
        else:
            result.add(canonical(paths, other + (n - 1,)))
    assert all(vertices(h) + edges(h) < vertices(g) + edges(g) for h in result)
    return result


@lru_cache(maxsize=None)
def minor_closure(g: Graph) -> frozenset[Graph]:
    result = {g}
    for h in immediate_minors(g):
        result.update(minor_closure(h))
    return frozenset(result)


@lru_cache(maxsize=None)
def pack_paths(items: Tuple[int, ...], capacities: Tuple[int, ...]) -> bool:
    """Exact bin packing; items and capacities are descending and nonzero."""
    if not items:
        return True
    if not capacities or sum(items) > sum(capacities) or items[0] > capacities[0]:
        return False
    item = items[0]
    seen: set[int] = set()
    for i, cap in enumerate(capacities):
        if cap < item or cap in seen:
            continue
        seen.add(cap)
        new = list(capacities)
        new[i] -= item
        state = tuple(sorted((x for x in new if x), reverse=True))
        if pack_paths(items[1:], state):
            return True
    return False


@lru_cache(maxsize=None)
def allocate_cycles(target: Tuple[int, ...], available: Tuple[int, ...],
                    paths: Tuple[int, ...], path_bins: Tuple[int, ...]) -> bool:
    """Reserve entire source cycles for target cycles, then pack paths."""
    if len(target) > len(available):
        return False
    if not target:
        capacities = tuple(sorted(path_bins + available, reverse=True))
        return pack_paths(paths, capacities)
    need = target[0]
    seen: set[int] = set()
    for i, length in enumerate(available):
        if length < need or length in seen:
            continue
        seen.add(length)
        rest = available[:i] + available[i + 1:]
        if allocate_cycles(target[1:], rest, paths, path_bins):
            return True
    return False


def is_minor_packing(target: Graph, source: Graph) -> bool:
    if vertices(target) > vertices(source) or edges(target) > edges(source):
        return False
    return allocate_cycles(tuple(reversed(target[1])), tuple(reversed(source[1])),
                           tuple(reversed(target[0])), tuple(reversed(source[0])))


def is_minor_greedy(target: Graph, source: Graph) -> bool:
    """Largest target cycle first; reserve the smallest eligible source cycle.

    An exchange argument proves this leaves enough capacity whenever any
    reservation does. Path packing remains exact, not a greedy heuristic.
    """
    if vertices(target) > vertices(source) or edges(target) > edges(source):
        return False
    available = list(source[1])
    for need in reversed(target[1]):
        for i, capacity in enumerate(available):
            if capacity >= need:
                available.pop(i)
                break
        else:
            return False
    return pack_paths(tuple(reversed(target[0])),
                      tuple(sorted(source[0] + tuple(available), reverse=True)))


def ordinal_key(g: Graph) -> Tuple[Tuple[Tuple[int, int], int], ...]:
    """Exact comparison key for the CNF ordinal in the paper.

    Exponent (0,n-1) represents n-1 for a path P_n.
    Exponent (1,n-3) represents omega+(n-3) for a cycle C_n.
    A descending tuple of (exponent,coefficient) compares exactly as CNF.
    This encodes ordinals, never floating-point approximations.
    """
    counts: Counter[Tuple[int, int]] = Counter()
    counts.update((0, n - 1) for n in g[0])
    counts.update((1, n - 3) for n in g[1])
    return tuple(sorted(counts.items(), reverse=True))


def cycle_embedding(a: Tuple[int, ...], b: Tuple[int, ...]) -> bool:
    """Injection between two ascending multisets over a chain."""
    return len(a) <= len(b) and all(x <= y for x, y in zip(reversed(a), reversed(b)))


def regression_tests() -> dict[str, bool]:
    examples = {
        "a_path_splits": (canonical((2, 2)), canonical((4,)), True),
        "a_cycle_opens_and_splits": (canonical((3, 2)), canonical((), (5,)), True),
        "cycle_cannot_leave_an_isolate": (canonical((1,), (3,)), canonical((), (4,)), False),
        "total_capacity_not_sufficient": (canonical((3, 3)), canonical((4, 2)), False),
        "cycles_need_distinct_source_cycles": (canonical((), (3, 3)), canonical((), (6,)), False),
        "cycle_length_is_vertex_capacity": (canonical((6,)), canonical((), (5,)), False),
        "matching_choice_matters": (canonical((7,), (4,)), canonical((), (4, 7)), True),
        "triangle_contracts_to_edge": (canonical((2,)), canonical((), (3,)), True),
        "equal_cycle_count_does_not_feed_paths": (
            canonical((3,), (3,)), canonical((2,), (6,)), False),
    }
    outcomes = {}
    for name, (a, b, expected) in examples.items():
        x, y = is_minor_packing(a, b), a in minor_closure(b)
        assert is_minor_greedy(a, b) == expected
        assert x == y == expected, (name, a, b, x, y, expected)
        outcomes[name] = True
    return outcomes


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-vertices", type=int, default=12)
    parser.add_argument("--out", type=Path, default=Path("results"))
    args = parser.parse_args()
    if not 0 <= args.max_vertices <= 18:
        parser.error("Use a vertex limit between 0 and 18; exhaustive checks are quadratic.")
    args.out.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    regressions = regression_tests()
    graphs = all_graphs(args.max_vertices)
    assert len(set(graphs)) == len(graphs)
    assert len(set(map(ordinal_key, graphs))) == len(graphs)
    relation_count = strict_count = fixed_cycle_checks = 0
    height_checks = 0
    counts = Counter(vertices(g) for g in graphs)
    rank: dict[Graph, int] = {}
    for j, source in enumerate(graphs):
        closure = minor_closure(source)
        rank[source] = max((rank[h] + 1 for h in immediate_minors(source)), default=0)
        assert rank[source] == vertices(source) + edges(source)
        height_checks += 1
        for target in graphs:
            by_operations = target in closure
            by_packing = is_minor_packing(target, source)
            assert by_operations == by_packing, (target, source, by_operations, by_packing)
            assert by_operations == is_minor_greedy(target, source), ("greedy", target, source)
            if by_operations:
                relation_count += 1
                assert ordinal_key(target) <= ordinal_key(source)
                if target != source:
                    strict_count += 1
                    assert ordinal_key(target) < ordinal_key(source)
            if len(target[1]) == len(source[1]):
                product_test = (cycle_embedding(target[1], source[1])
                                and is_minor_packing((target[0], ()), (source[0], ())))
                assert by_operations == product_test, ("exact-cycle product", target, source)
                fixed_cycle_checks += 1
        if j and j % 500 == 0:
            print(f"Checked {j}/{len(graphs)} source graphs", flush=True)
    # Independent generating-function count: product (1-x^n)^-1 for paths,
    # and a second factor for n>=3 for cycles.
    coefficients = [1] + [0] * args.max_vertices
    for size in range(1, args.max_vertices + 1):
        for _ in range(1 + (size >= 3)):
            for n in range(size, args.max_vertices + 1):
                coefficients[n] += coefficients[n - size]
    assert coefficients == [counts[n] for n in range(args.max_vertices + 1)]
    report = {
        "status": "PASS",
        "python": platform.python_version(),
        "max_vertices": args.max_vertices,
        "isomorphism_classes": len(graphs),
        "ordered_pairs_compared": len(graphs) ** 2,
        "greedy_cycle_reservation_checks": len(graphs) ** 2,
        "minor_pairs_including_equality": relation_count,
        "strict_minor_pairs_with_strict_ordinal_decrease": strict_count,
        "equal_cycle_count_product_checks": fixed_cycle_checks,
        "finite_height_rank_checks": height_checks,
        "ordinal_keys_injective": True,
        "counts_by_vertices": dict(sorted(counts.items())),
        "regression_tests": regressions,
        "runtime_seconds": round(time.perf_counter() - start, 3),
        "limitations": "Finite tests validate algorithms and lemmas on the stated range, not transfinite ranks or historical novelty.",
    }
    (args.out / "verification.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    with (args.out / "counts.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["vertices", "isomorphism_classes", "cumulative_classes"])
        cumulative = 0
        for n in range(args.max_vertices + 1):
            cumulative += counts[n]
            writer.writerow([n, counts[n], cumulative])
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
