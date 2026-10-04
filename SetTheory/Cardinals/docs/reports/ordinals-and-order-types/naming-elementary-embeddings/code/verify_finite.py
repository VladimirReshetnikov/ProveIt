#!/usr/bin/env python3
"""Exact finite regression checks for the accompanying manuscript.

This program does NOT verify any infinite-cardinal or set-theoretic theorem.
It checks component swaps and the finite-support real-marker construction.
Python 3.10+, standard library only.
"""
from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from itertools import combinations, permutations, product
import hashlib
import json
from pathlib import Path
import platform
import sys
from typing import Any

Permutation = tuple[int, ...]


class Checker:
    def __init__(self) -> None:
        self.assertions = 0

    def require(self, condition: bool, message: str) -> None:
        self.assertions += 1
        if not condition:
            raise AssertionError(message)


@dataclass(frozen=True)
class Atom:
    label: int


def lift(mapping: Permutation, obj: Any) -> Any:
    if isinstance(obj, Atom):
        return Atom(mapping[obj.label])
    if isinstance(obj, frozenset):
        return frozenset(lift(mapping, child) for child in obj)
    raise TypeError(f"Not a tagged hereditarily finite object: {obj!r}")


def kernel(obj: Any) -> frozenset[int]:
    if isinstance(obj, Atom):
        return frozenset((obj.label,))
    if isinstance(obj, frozenset):
        answer: set[int] = set()
        for child in obj:
            answer.update(kernel(child))
        return frozenset(answer)
    raise TypeError(f"Not a tagged hereditarily finite object: {obj!r}")


def inverse(mapping: Permutation) -> Permutation:
    answer = [0] * len(mapping)
    for source, target in enumerate(mapping):
        answer[target] = source
    return tuple(answer)


def components(maps: tuple[Permutation, ...]) -> list[tuple[int, ...]]:
    if not maps:
        raise ValueError("At least one named map is required")
    n = len(maps[0])
    if any(len(m) != n or sorted(m) != list(range(n)) for m in maps):
        raise ValueError("Maps must be permutations of the same finite domain")
    steps = maps + tuple(inverse(m) for m in maps)
    unseen = set(range(n))
    result: list[tuple[int, ...]] = []
    while unseen:
        root = min(unseen)
        part = {root}
        queue = deque([root])
        unseen.remove(root)
        while queue:
            a = queue.popleft()
            for step in steps:
                b = step[a]
                if b not in part:
                    part.add(b)
                    unseen.remove(b)
                    queue.append(b)
        result.append(tuple(sorted(part)))
    return result


def component_isomorphism(
    maps: tuple[Permutation, ...],
    left: tuple[int, ...],
    right: tuple[int, ...],
) -> dict[int, int] | None:
    if len(left) != len(right):
        return None
    steps = maps + tuple(inverse(m) for m in maps)
    for target_root in right:
        correspondence = {left[0]: target_root}
        queue = deque([left[0]])
        valid = True
        while queue and valid:
            source = queue.popleft()
            target = correspondence[source]
            for step in steps:
                a, b = step[source], step[target]
                if a in correspondence:
                    if correspondence[a] != b:
                        valid = False
                        break
                else:
                    correspondence[a] = b
                    queue.append(a)
        if (valid and set(correspondence) == set(left)
                and set(correspondence.values()) == set(right)):
            return correspondence
    return None


def check_tuple(maps: tuple[Permutation, ...], check: Checker) -> int:
    n = len(maps[0])
    parts = components(maps)
    check.require(sorted(a for part in parts for a in part) == list(range(n)),
                  "Components do not partition the atom set")
    swaps = 0
    for left, right in combinations(parts, 2):
        correspondence = component_isomorphism(maps, left, right)
        if correspondence is None:
            continue
        swap = list(range(n))
        for a, b in correspondence.items():
            swap[a], swap[b] = b, a
        pi = tuple(swap)
        swaps += 1
        check.require(sorted(pi) == list(range(n)), "Swap is not a permutation")
        check.require(all(pi[pi[a]] == a for a in range(n)),
                      "Swap is not involutive")
        outside = set(range(n)) - set(left) - set(right)
        check.require(all(pi[a] == a for a in outside),
                      "Swap moves a point outside the two components")
        for mapping in maps:
            check.require(all(pi[mapping[a]] == mapping[pi[a]] for a in range(n)),
                          "Component swap does not commute with a named map")
        root = left[0]
        witness = frozenset((Atom(root), frozenset((Atom(root),))))
        check.require(lift(pi, witness) != witness, "Fresh swap did not move witness")
        check.require(kernel(lift(pi, witness)) == frozenset(pi[a] for a in kernel(witness)),
                      "Kernel transport identity failed")
        for mapping in maps:
            check.require(lift(pi, lift(mapping, witness)) == lift(mapping, lift(pi, witness)),
                          "Recursive lifts did not commute")
    return swaps


def marker(bits: frozenset[int]) -> dict[int, int]:
    moved = {0: 1, 1: 0}
    for bit in bits:
        if bit < 0:
            raise ValueError("Marker bit positions must be nonnegative")
        a = 3 * (bit + 1)
        moved[a], moved[a + 1] = a + 1, a
    return moved


def run() -> dict[str, Any]:
    check = Checker()
    one_count = pair_count = swaps = 0
    for n in range(1, 8):
        for mapping in permutations(range(n)):
            one_count += 1
            swaps += check_tuple((mapping,), check)
    for n in range(1, 6):
        all_maps = list(permutations(range(n)))
        for first, second in product(all_maps, repeat=2):
            pair_count += 1
            swaps += check_tuple((first, second), check)

    bit_width = 6
    codes = [frozenset(i for i in range(bit_width) if mask & (1 << i))
             for mask in range(1 << bit_width)]
    moved_maps = [marker(code) for code in codes]
    for code, moved in zip(codes, moved_maps):
        check.require(min(moved) == 0, "Marker root is not zero")
        for a in range(-8, 3 * bit_width + 10):
            ga = moved.get(a, a)
            check.require(moved.get(ga, ga) == a, "Marker is not an involution")
        for bit in range(bit_width + 3):
            a = 3 * (bit + 1)
            check.require((moved.get(a, a) != a) == (bit in code),
                          "Marker decoder returned the wrong real bit")
    translation_cases = 0
    for i, moved in enumerate(moved_maps):
        for j, other in enumerate(moved_maps):
            for shift in range(-8, 9):
                translated = {a + shift: b + shift for a, b in moved.items()}
                translation_cases += 1
                check.require((translated == other) == (i == j and shift == 0),
                              "Distinct marker codes were translation-isomorphic")
    return {
        "status": "passed",
        "scope": "Exact finite regression tests only; not a proof of infinite theorems",
        "python_version": platform.python_version(),
        "one_permutation_structures_n_1_to_7": one_count,
        "two_permutation_structures_n_1_to_5": pair_count,
        "isomorphic_component_swaps_tested": swaps,
        "marker_codes_six_bits": len(codes),
        "marker_translation_cases": translation_cases,
        "checked_assertions": check.assertions,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write the JSON check report here")
    args = parser.parse_args()
    try:
        report = run()
        rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.output is not None:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(rendered, encoding="utf-8")
        print(rendered, end="")
        return 0
    except (AssertionError, OSError, ValueError, TypeError) as exc:
        print(f"Verification failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
