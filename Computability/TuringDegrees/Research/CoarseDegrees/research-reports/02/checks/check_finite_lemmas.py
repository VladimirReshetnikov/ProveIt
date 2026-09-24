#!/usr/bin/env python3
"""Exact finite checks supporting the accompanying conventional proof.

This program does not construct infinite generic sets, emulate a jump oracle,
or certify Turing reducibility/minimality.  It checks the finite combinatorics
that the paper uses.  Python 3.10+; standard library only.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path
from typing import Callable

Budget = Callable[[int], int]


def logarithmic_budget(n: int) -> int:
    if n < 0:
        raise ValueError("A prefix length must be nonnegative")
    return (n + 1).bit_length() - 1


def admissible(a: int, b: int, length: int, budget: Budget) -> bool:
    """Bit i is the i-th character, so strings are encoded little-endian."""
    if length < 0 or min(a, b) < 0 or max(a, b) >= 1 << length:
        return False
    difference = a ^ b
    return all((difference & ((1 << k) - 1)).bit_count() <= budget(k)
               for k in range(length + 1))


def append(prefix: int, length: int, tail: int) -> int:
    return prefix | (tail << length)


def condition_checks(max_length: int = 6) -> dict:
    counts = {}
    for name, budget in (("floor_log2_n_plus_1", logarithmic_budget),
                         ("floor_sqrt_n", math.isqrt)):
        pairs = valid = copies = cushions = 0
        for length in range(max_length + 1):
            for a in range(1 << length):
                for b in range(1 << length):
                    pairs += 1
                    if not admissible(a, b, length, budget):
                        continue
                    valid += 1
                    # Both coordinate projections remain unrestricted.
                    for tail_length in range(4):
                        for tail in range(1 << tail_length):
                            aa = append(a, length, tail)
                            bb = append(b, length, tail)
                            assert admissible(aa, bb, length + tail_length, budget)
                            copies += 1
                    d = (a ^ b).bit_count()
                    padded_length = length
                    while budget(padded_length) < d + 1:
                        padded_length += 1
                    assert admissible(a, b, padded_length, budget)
                    # Padding uses zeros. Compare every pair of tails at
                    # Hamming distance zero or one, not just adjacent tails.
                    for tail_length in range(5):
                        for u in range(1 << tail_length):
                            neighbors = [u] + [u ^ (1 << i)
                                               for i in range(tail_length)]
                            for v in neighbors:
                                aa = append(a, padded_length, u)
                                bb = append(b, padded_length, v)
                                assert admissible(aa, bb,
                                                  padded_length + tail_length,
                                                  budget)
                                cushions += 1
        counts[name] = {
            "maximum_base_length": max_length,
            "base_pairs_examined": pairs,
            "admissible_base_pairs": valid,
            "copy_extension_checks": copies,
            "one_bit_cushion_checks": cushions,
        }
    # All-prefix constraints cannot be replaced by an endpoint constraint.
    assert (0 ^ 3).bit_count() <= logarithmic_budget(3)
    assert not admissible(0, 3, 3, logarithmic_budget)
    # The one-bit slack really is needed in general.
    assert admissible(0, 5, 3, logarithmic_budget)
    assert not admissible(0, 5 | (1 << 3), 4, logarithmic_budget)
    return {"budgets": counts,
            "endpoint_only_counterexample": {"length": 3, "a": "000", "b": "110"},
            "unpadded_extra_bit_counterexample": {"a": "0000", "b": "1011"}}


def cube_edges(dimension: int) -> list[tuple[int, int]]:
    size = 1 << dimension
    return [(u, size + v) for u in range(size)
            for v in [u] + [u ^ (1 << i) for i in range(dimension)]]


def connected_components(vertex_count: int, edges: list[tuple[int, int]]) -> int:
    parents = list(range(vertex_count))

    def root(x: int) -> int:
        while parents[x] != x:
            parents[x] = parents[parents[x]]
            x = parents[x]
        return x

    for x, y in edges:
        rx, ry = root(x), root(y)
        if rx != ry:
            parents[rx] = ry
    return len({root(i) for i in range(vertex_count)})


def cube_checks() -> dict:
    connectivity = []
    for dimension in range(11):
        size = 1 << dimension
        edges = cube_edges(dimension)
        components = connected_components(2 * size, edges)
        assert components == 1
        connectivity.append({"dimension": dimension, "vertices": 2 * size,
                             "edges": len(edges), "components": components})
    label_counts = []
    for dimension in range(4):
        size = 1 << dimension
        edges = cube_edges(dimension)
        survivors = []
        for coloring in range(1 << (2 * size)):
            if all(((coloring >> x) & 1) == ((coloring >> y) & 1)
                   for x, y in edges):
                survivors.append(coloring)
        assert survivors == [0, (1 << (2 * size)) - 1]
        label_counts.append({"dimension": dimension,
                             "assignments_examined": 1 << (2 * size),
                             "satisfying_assignments": len(survivors)})
    # Without cross edges there are nonconstant solutions.
    assert connected_components(8, [(u, 4 + u) for u in range(4)]) == 4
    return {"connectivity": connectivity, "exhaustive_binary_labels": label_counts,
            "diagonal_edges_alone_components_dimension_2": 4}


def majority(values: tuple[int, ...]) -> int:
    if not values:
        return 0
    for value in set(values):
        if 2 * values.count(value) > len(values):
            return value
    return 0


def block_checks() -> dict:
    examined = applicable = 0
    for length in range(1, 9):
        for values in itertools.product(range(3), repeat=length):
            for true_value in range(3):
                examined += 1
                errors = sum(x != true_value for x in values)
                if 2 * errors < length:
                    assert majority(values) == true_value
                    applicable += 1
    return {"alphabet_size": 3, "maximum_block_length": 8,
            "cases_examined": examined, "strict_majority_cases": applicable}


def sparse_checks() -> dict:
    count = 0
    for oracle_length in range(1, 11):
        array_length = (1 << (oracle_length - 1)) + 1
        for oracle in range(1 << oracle_length):
            # D is an illustrative finite function computable from this oracle.
            original = [(oracle >> (i % oracle_length)) & 1
                        for i in range(array_length)]
            encoded = original.copy()
            for i in range(oracle_length):
                encoded[1 << i] = (oracle >> i) & 1
            assert all(encoded[1 << i] == ((oracle >> i) & 1)
                       for i in range(oracle_length))
            assert all(original[i] == encoded[i]
                       for i in range(array_length)
                       if i == 0 or i & (i - 1))
            count += 1
    for n in range(1, 10001):
        power_count = (n - 1).bit_length()
        assert power_count <= 1 + n.bit_length() - 1
    return {"finite_oracle_cases": count,
            "powers_of_two_count_bound_checked_through": 10000}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()
    results = {
        "status": "PASS",
        "scope": "Exact finite tests; not a verification of the infinite oracle construction.",
        "conditions": condition_checks(),
        "cube": cube_checks(),
        "majority_blocks": block_checks(),
        "sparse_coding": sparse_checks(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
