#!/usr/bin/env python3
"""Finite checks for local formulas in the accompanying research manuscript.

These are NOT tests of freshness, forcing, cofinality, saturation, or class
recursion. No finite word can be fresh over a universe containing finite words.
Only Python's standard library is required.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import Iterable, Sequence

SignWord = tuple[int, ...]  # -1 is minus, +1 is plus; 0 is only a missing sign.


def words(alphabet: Sequence[int], max_length: int) -> Iterable[tuple[int, ...]]:
    for length in range(max_length + 1):
        yield from itertools.product(alphabet, repeat=length)


def encode(values: Sequence[int]) -> SignWord:
    if any(not isinstance(value, int) or value < 0 for value in values):
        raise ValueError("The finite ordinal values must be nonnegative integers.")
    result: list[int] = []
    for value in values:
        result.extend([1] * value)
        result.append(-1)
    return tuple(result)


def decode(word: SignWord) -> tuple[int, ...]:
    result: list[int] = []
    run = 0
    for sign in word:
        if sign == 1:
            run += 1
        elif sign == -1:
            result.append(run)
            run = 0
        else:
            raise ValueError("Signs must be -1 or +1.")
    if run:
        raise ValueError("A complete nonempty code must end in a delimiter.")
    return tuple(result)


def sign_compare(left: SignWord, right: SignWord) -> int:
    """Lexicographic order with an absent sign between minus and plus."""
    for i in range(max(len(left), len(right))):
        a = left[i] if i < len(left) else 0
        b = right[i] if i < len(right) else 0
        if a != b:
            return (a > b) - (a < b)
    return 0


def check_code() -> dict[str, int]:
    seen: dict[SignWord, tuple[int, ...]] = {}
    prefix_checks = 0
    for values in words(tuple(range(4)), 6):
        coded = encode(values)
        assert decode(coded) == values, (values, coded)
        assert len(coded) == sum(value + 1 for value in values)
        assert coded not in seen, (values, seen.get(coded))
        seen[coded] = values
        for k in range(len(values) + 1):
            initial = encode(values[:k])
            assert coded[:len(initial)] == initial
            if k < len(values):
                assert len(initial) < len(coded)
            prefix_checks += 1
    for invalid in ((1,), (-1, 1), (1, 0, -1)):
        try:
            decode(invalid)
        except ValueError:
            pass
        else:
            raise AssertionError(f"Invalid code accepted: {invalid!r}")
    return {"round_trips_and_distinct_codes": len(seen),
            "prefix_checks": prefix_checks, "invalid_inputs_rejected": 3}


def check_cones() -> dict[str, int]:
    tested = 0
    candidates = list(words((-1, 1), 7))
    for s in words((-1, 1), 5):
        left = [s[:i] for i, sign in enumerate(s) if sign == 1]
        right = [s[:i] for i, sign in enumerate(s) if sign == -1]
        for x in candidates:
            satisfies = (all(sign_compare(a, x) < 0 for a in left)
                         and all(sign_compare(x, b) < 0 for b in right))
            extends = len(x) >= len(s) and x[:len(s)] == s
            assert satisfies == extends, (s, x, left, right)
            tested += 1
    return {"canonical_cone_equivalences": tested}


def check_boolean_profiles() -> dict[str, int]:
    pair_checks = 0
    profile_checks = 0
    for n in range(9):
        universe = frozenset(range(n))
        subsets = [frozenset(i for i in range(n) if mask & (1 << i))
                   for mask in range(1 << n)]
        profiles = [frozenset({-1}) | s for s in subsets]
        assert len(set(profiles)) == len(subsets)
        profile_checks += len(subsets)
        for s in subsets:
            for t in subsets:
                kept_s = universe - s
                kept_t = universe - t
                assert (kept_s <= kept_t) == (t <= s)
                if s != t:
                    i = min(s ^ t)
                    assert (i in (frozenset({-1}) | s)) != (
                        i in (frozenset({-1}) | t))
                pair_checks += 1
    return {"distinct_profile_checks": profile_checks,
            "reversed_inclusion_and_separation_pairs": pair_checks}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path("verification_results.json"))
    args = parser.parse_args()
    result = {
        "status": "all finite checks passed",
        "scope": "finite coding, sign comparison, and coordinate bookkeeping only",
        "not_checked": ["freshness", "forcing", "cardinal preservation",
                        "outer cofinality", "saturation", "class recursion",
                        "mathematical novelty"],
        "delimiter_code": check_code(),
        "sign_cones": check_cones(),
        "boolean_profiles": check_boolean_profiles(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
