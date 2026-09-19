#!/usr/bin/env python3
"""Finite checks for the cyclic selection obstruction.

These tests concern finite cyclic permutations only. They do not construct a
model of set theory or formally verify the large-cardinal arguments.
Python 3.10+; standard library only.
"""
from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations
import json
from math import gcd, lcm
from pathlib import Path


def shift(mask: int, n: int, step: int = 1) -> int:
    """Rotate an n-bit characteristic vector."""
    step %= n
    return ((mask << step) | (mask >> (n - step))) & ((1 << n) - 1)


def period(mask: int, n: int) -> int:
    return next(d for d in range(1, n + 1) if shift(mask, n, d) == mask)


def check_subset_periods(max_n: int = 14) -> dict:
    tested = 0
    sharp_cases = 0
    for n in range(2, max_n + 1):
        for mask in range(1, (1 << n) - 1):
            r = mask.bit_count()
            d = period(mask, n)
            assert (r * d) % n == 0, (n, r, d, mask)
            tested += 1
        for r in range(1, n):
            g = gcd(n, r)
            d = n // g
            e = r // g
            mask = sum(1 << (i + k * d) for i in range(e) for k in range(g))
            assert mask.bit_count() == r
            assert period(mask, n) == d
            sharp_cases += 1
    return {"max_cycle_size": max_n, "nontrivial_subsets_checked": tested,
            "sharp_period_constructions_checked": sharp_cases}


def pair_selector_orbits(n: int) -> dict:
    """Enumerate all binary selectors on the unordered pairs of an n-set.

    A selector is a tournament orientation. The action is conjugation by the
    cyclic permutation i -> i+1. Histograms count orbits, not functions.
    """
    pairs = list(combinations(range(n), 2))
    index = {p: i for i, p in enumerate(pairs)}
    moved = []
    for a, b in pairs:
        aa, bb = (a + 1) % n, (b + 1) % n
        target = tuple(sorted((aa, bb)))
        moved.append((index[target], int(aa > bb)))

    def conjugate(code: int) -> int:
        output = 0
        for i, (target, flip) in enumerate(moved):
            bit = ((code >> i) & 1) ^ flip
            output |= bit << target
        return output

    seen: set[int] = set()
    histogram: Counter[int] = Counter()
    for code in range(1 << len(pairs)):
        if code in seen:
            continue
        orbit = []
        current = code
        while current not in seen:
            seen.add(current)
            orbit.append(current)
            current = conjugate(current)
        assert current == code, "A permutation orbit must close at its start."
        assert n % len(orbit) == 0
        histogram[len(orbit)] += 1
    total = 1 << len(pairs)
    assert sum(size * count for size, count in histogram.items()) == total
    return {"cycle_size": n, "selectors": total,
            "orbit_histogram": dict(sorted(histogram.items()))}


def check_amplification(max_m: int = 12, max_n: int = 12) -> dict:
    """Check the finite exponent construction without enumerating huge sets."""
    tested = 0
    for m in range(1, max_m + 1):
        exponent = lcm(*range(1, m + 1))
        assert all(exponent % d == 0 for d in range(1, m + 1))
        for n in range(2, max_n + 1):
            cycle = n * exponent
            # The selected n points are 0,L,...,(n-1)L. Translation by L
            # acts transitively on them and has order exactly n.
            orbit = [(k * exponent) % cycle for k in range(n)]
            assert len(set(orbit)) == n
            assert (orbit[-1] + exponent) % cycle == orbit[0]
            tested += 1
    return {"max_family_size": max_m, "max_selection_arity": max_n,
            "amplification_cases_checked": tested}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("finite_checks.json"))
    args = parser.parse_args()
    result = {
        "scope": "Finite arithmetic and permutation checks; not a formal set-theory proof.",
        "subset_periods": check_subset_periods(),
        "binary_selector_orbits": [pair_selector_orbits(n) for n in range(2, 7)],
        "cycle_amplification": check_amplification(),
        "status": "All assertions passed."
    }
    text = json.dumps(result, indent=2) + "\n"
    args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
