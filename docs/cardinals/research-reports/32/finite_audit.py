#!/usr/bin/env python3
"""Finite sanity checks for the accompanying set-theory article.

These checks validate permutation identities and small exhaustive instances.
They do NOT verify forcing, HOD, large-cardinal assumptions, or general proofs.
Requires only Python 3.10+ and its standard library.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import Counter
from pathlib import Path
from typing import Iterable

Permutation = tuple[int, ...]


def power_at(perm: Permutation, exponent: int, element: int) -> int:
    """Apply an arbitrary integer power using the cycle through element."""
    cycle = [element]
    nxt = perm[element]
    while nxt != element:
        cycle.append(nxt)
        nxt = perm[nxt]
    return cycle[exponent % len(cycle)]


def phase_checks() -> int:
    count = 0
    for m in range(1, 7):
        for perm in itertools.permutations(range(m)):
            for stem_length in range(4):
                for tail_index in range(6):
                    for i in range(m):
                        lhs = power_at(perm, -(stem_length + 1 + tail_index), i)
                        rhs = power_at(
                            perm, -(stem_length + tail_index), power_at(perm, -1, i)
                        )
                        assert lhs == rhs, (perm, stem_length, tail_index, i)
                        count += 1
    return count


def exponent_checks() -> int:
    count = 0
    for k in range(1, 8):
        exponent = math.lcm(*range(1, k + 1))
        for perm in itertools.permutations(range(k)):
            for i in range(k):
                assert power_at(perm, exponent, i) == i
                count += 1
    return count


def block_cycle_checks() -> int:
    count = 0
    for n in range(2, 13):
        for k in range(1, 13):
            h = math.lcm(*range(1, k + 1))
            m = n * h
            orbit = [(j * h) % m for j in range(n)]
            assert len(set(orbit)) == n
            assert (orbit[-1] + h) % m == orbit[0]
            count += 1
    return count


def selector_orbits(n: int, r: int, k: int) -> dict[str, object]:
    """Enumerate all finite selectors and their full-cycle orbits.

    A nonempty invariant family of size <= k exists iff there is a selector
    orbit of length <= k. Every invariant family is a union of whole orbits.
    """
    if not (0 < r < n and k >= 1):
        raise ValueError("Require 0 < r < n and k >= 1")
    h = math.lcm(*range(1, k + 1))
    m = n * h
    domain = list(itertools.combinations(range(m), n))
    domain_index = {subset: i for i, subset in enumerate(domain)}
    options = [list(itertools.combinations(subset, r)) for subset in domain]
    total = math.prod(len(choices) for choices in options)
    if total > 100_000:
        raise ValueError(f"Exhaustive instance would be too large: {total}")
    selectors = list(itertools.product(*options))
    selector_index = {selector: i for i, selector in enumerate(selectors)}
    pi = tuple((i + 1) % m for i in range(m))
    inverse = tuple((i - 1) % m for i in range(m))

    def act(selector: tuple[tuple[int, ...], ...]) -> tuple[tuple[int, ...], ...]:
        result = []
        for subset in domain:
            preimage = tuple(sorted(inverse[i] for i in subset))
            selected = selector[domain_index[preimage]]
            result.append(tuple(sorted(pi[i] for i in selected)))
        return tuple(result)

    action = [selector_index[act(selector)] for selector in selectors]
    unvisited = set(range(total))
    lengths: list[int] = []
    while unvisited:
        start = min(unvisited)
        current = start
        orbit: list[int] = []
        while current not in orbit:
            orbit.append(current)
            current = action[current]
        assert current == start
        unvisited.difference_update(orbit)
        lengths.append(len(orbit))
    assert min(lengths) > k, (n, r, k, lengths)
    return {
        "n": n, "r": r, "family_size_bound": k, "m": m,
        "number_of_selectors": total,
        "orbit_length_multiplicities": dict(sorted(Counter(lengths).items())),
        "invariant_nonempty_family_of_size_at_most_k_exists": False,
    }


def s3_label_check() -> dict[str, object]:
    """Natural three points disjoint union sign-action two points."""
    actions = []
    for perm in itertools.permutations(range(3)):
        inversions = sum(perm[i] > perm[j] for i in range(3) for j in range(i + 1, 3))
        sign = inversions % 2
        action = perm + (3 + sign, 4 - sign)
        fixed = [i for i in range(5) if action[i] == i]
        assert fixed
        actions.append(set(fixed))
    assert not set.intersection(*actions)
    return {"every_element_has_fixed_label": True, "common_fixed_label_exists": False}


def main(argv: Iterable[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON output file")
    args = parser.parse_args(argv)
    result = {
        "scope": "Finite checks only; not a verification of the set-theoretic theorems.",
        "phase_identity_instances": phase_checks(),
        "lcm_exponent_instances": exponent_checks(),
        "block_cycle_instances": block_cycle_checks(),
        "selector_exhaustions": [
            selector_orbits(*case)
            for case in [(2, 1, 1), (2, 1, 2), (3, 1, 1), (3, 2, 1), (4, 2, 1)]
        ],
        "s3_example": s3_label_check(),
        "status": "All finite checks passed.",
    }
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
