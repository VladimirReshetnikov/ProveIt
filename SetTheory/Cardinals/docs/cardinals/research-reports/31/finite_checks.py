#!/usr/bin/env python3
"""Finite checks for Prikry_Symmetry_and_Maximal_Rigidity.tex.

These are exhaustive finite action checks, not a formal verification of the
set-theoretic theorems. Requires Python 3.9+ and no third-party packages.
"""
from __future__ import annotations

from collections import Counter
from itertools import combinations, permutations, product
import json
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

Permutation = Tuple[int, ...]
Pattern = Tuple[int, ...]


def inverse(g: Permutation) -> Permutation:
    if sorted(g) != list(range(len(g))):
        raise ValueError("Input is not a permutation of an initial segment.")
    result = [0] * len(g)
    for i, j in enumerate(g):
        result[j] = i
    return tuple(result)


def code_points(points: Sequence[int], g: Permutation) -> List[set[int]]:
    """Finite analogue of a_i(c) = {m*c_n + g^(-n)(i) : n < omega}."""
    m = len(g)
    inv = inverse(g)
    offsets = list(range(m))
    result: List[set[int]] = [set() for _ in range(m)]
    for point in points:
        for i in range(m):
            result[i].add(m * point + offsets[i])
        offsets = [inv[j] for j in offsets]
    return result


def check_insertions() -> Dict[str, object]:
    checked_permutations = 0
    checked_insertions = 0
    points = [10 * (n + 1) for n in range(14)]
    for m in range(1, 7):
        for g in permutations(range(m)):
            inv = inverse(g)
            old = code_points(points, g)
            for k in (0, 1, 3, 9):
                alpha = points[k] - 1
                new_points = points[:k] + [alpha] + points[k:]
                new = code_points(new_points, g)
                cutoff = m * points[k]
                for i in range(m):
                    new_tail = {x for x in new[i] if x >= cutoff}
                    old_tail = {x for x in old[inv[i]] if x >= cutoff}
                    assert new_tail == old_tail, (m, g, k, i)
                checked_insertions += 1
            checked_permutations += 1
    return {
        "coordinate_sizes": [1, 2, 3, 4, 5, 6],
        "permutations": checked_permutations,
        "insertion_comparisons": checked_insertions,
        "result": "PASS",
    }


def parity(g: Permutation) -> int:
    return sum(g[i] > g[j] for i in range(len(g))
               for j in range(i + 1, len(g))) % 2


def check_five_labels() -> Dict[str, object]:
    common_fixed = set(range(5))
    fixed_counts = []
    for g in permutations(range(3)):
        action = g + (3 + parity(g), 3 + (1 ^ parity(g)))
        fixed = {i for i in range(5) if action[i] == i}
        assert fixed, (g, action)
        common_fixed.intersection_update(fixed)
        fixed_counts.append(len(fixed))
    assert not common_fixed
    return {
        "permutations": 6,
        "fixed_label_counts": fixed_counts,
        "common_fixed_labels": sorted(common_fixed),
        "result": "PASS",
    }


def check_pattern_orbits() -> Dict[str, object]:
    n_points = 4
    pairs = tuple(combinations(range(n_points), 2))
    pair_index = {pair: i for i, pair in enumerate(pairs)}
    tau = (1, 2, 3, 0)
    inv_tau = inverse(tau)
    patterns = set(product(*pairs))  # the winner of each unordered pair

    def act(pattern: Pattern) -> Pattern:
        values = []
        for pair in pairs:
            old_pair = tuple(sorted(inv_tau[i] for i in pair))
            old_winner = pattern[pair_index[old_pair]]
            values.append(tau[old_winner])
        return tuple(values)

    remaining = set(patterns)
    orbit_sizes: Counter[int] = Counter()
    while remaining:
        first = next(iter(remaining))
        orbit = {first}
        current = act(first)
        while current != first:
            assert current not in orbit
            orbit.add(current)
            current = act(current)
        assert orbit.issubset(patterns)
        remaining.difference_update(orbit)
        orbit_sizes[len(orbit)] += 1
    assert len(patterns) == 64
    assert orbit_sizes == Counter({4: 16})
    # Invariant nonempty subsets are unions of full orbits. Thus their minimum
    # size is four, which excludes the claimed sizes one and two.
    return {
        "parameters": {"n": 2, "r": 1, "h": 2, "ell": 2, "N": 4},
        "patterns": len(patterns),
        "orbit_size_counts": dict(sorted(orbit_sizes.items())),
        "invariant_nonempty_families_of_size_at_most_two": 0,
        "result": "PASS",
    }


def main() -> None:
    results = {
        "scope": "Finite action sanity checks; not a set-theoretic formalization.",
        "stem_insertion": check_insertions(),
        "five_label_action": check_five_labels(),
        "selector_pattern_orbits": check_pattern_orbits(),
    }
    output = Path(__file__).with_name("finite_check_results.json")
    output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
