#!/usr/bin/env python3
"""Finite regression checks accompanying Beyond the First Gap.

These tests concern finite sign combinatorics and index-set identities only.
They do NOT verify freshness, forcing, cofinalities, saturation, class arguments,
or the transfinite theorems in the manuscript. Python 3.10+, standard library.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

Sign = tuple[int, ...]
COUNTS: dict[str, int] = {}


def check(condition: bool, group: str, detail: str = "") -> None:
    """Count an assertion after testing it; do not disable checks with python -O."""
    if not condition:
        raise AssertionError(f"{group}: {detail}")
    COUNTS[group] = COUNTS.get(group, 0) + 1


def signs(max_length: int) -> list[Sign]:
    if max_length < 0:
        raise ValueError("max_length must be nonnegative")
    return [s for n in range(max_length + 1)
            for s in itertools.product((-1, 1), repeat=n)]


def compare(x: Sign, y: Sign) -> int:
    """Surreal sign order: minus < undefined < plus at the first difference."""
    for i in range(max(len(x), len(y))):
        a = x[i] if i < len(x) else 0
        b = y[i] if i < len(y) else 0
        if a != b:
            return 1 if a > b else -1
    return 0


def extends(x: Sign, s: Sign) -> bool:
    return len(x) >= len(s) and x[:len(s)] == s


def check_sign_cones() -> None:
    for s in signs(7):
        left = [s[:i] for i, value in enumerate(s) if value == 1]
        right = [s[:i] for i, value in enumerate(s) if value == -1]
        for x in signs(9):
            separates = (all(compare(l, x) < 0 for l in left)
                         and all(compare(x, r) < 0 for r in right))
            check(separates == extends(x, s), "separator_cone", repr((s, x)))
            # This models only the comparison condition used for an old element:
            # it cannot extend a fresh sign. No finite test models freshness.
            if not extends(x, s):
                if compare(x, s) < 0:
                    check(any(compare(x, l) <= 0 for l in left),
                          "canonical_prefix_bounds_left", repr((s, x)))
                else:
                    check(any(compare(r, x) <= 0 for r in right),
                          "canonical_prefix_bounds_right", repr((s, x)))


def encode(values: tuple[int, ...], width: int) -> Sign:
    if width < 2 or any(value < 0 or value >= width for value in values):
        raise ValueError("width must be at least 2 and values must fit the block")
    return tuple(1 if j == value else -1
                 for value in values for j in range(width))


def decode(encoded: Sign, width: int) -> tuple[int, ...]:
    if width < 2 or len(encoded) % width != 0:
        raise ValueError("expected a whole number of blocks of width >= 2")
    result = []
    for start in range(0, len(encoded), width):
        block = encoded[start:start + width]
        if block.count(1) != 1 or any(v not in (-1, 1) for v in block):
            raise ValueError("each block must contain exactly one plus")
        result.append(block.index(1))
    return tuple(result)


def check_blocks() -> None:
    for width in range(2, 6):
        for length in range(5):
            for values in itertools.product(range(width), repeat=length):
                encoded = encode(values, width)
                check(decode(encoded, width) == values, "block_roundtrip")
                for stop in range(len(encoded) + 1):
                    needed = (stop + width - 1) // width
                    short_code = encode(values[:needed], width)[:stop]
                    check(short_code == encoded[:stop], "block_prefix_dependence")
                    changed_tail = values[:needed] + tuple(
                        (v + 1) % width for v in values[needed:])
                    check(encode(changed_tail, width)[:stop] == encoded[:stop],
                          "block_tail_independence")
    for malformed in ((-1, -1), (1, 1), (0, 1), (1,)):
        try:
            decode(malformed, 2)
        except ValueError:
            check(True, "decoder_rejects_invalid")
        else:
            check(False, "decoder_rejects_invalid", repr(malformed))


def subsets(n: int) -> Iterable[frozenset[int]]:
    for mask in range(1 << n):
        yield frozenset(i for i in range(n) if mask & (1 << i))


def check_boolean_cubes() -> None:
    for n in range(1, 11):
        universe = frozenset(range(n))
        seen: set[frozenset[int]] = set()
        same_minimum = 0
        for retained in subsets(n):
            missing = universe - retained
            check(universe - missing == retained, "finite_index_recovery")
            check(missing not in seen, "finite_spectrum_injectivity")
            seen.add(missing)
            if 0 not in retained:
                check(min(missing) == 0, "finite_same_minimum")
                same_minimum += 1
        check(same_minimum == 2 ** (n - 1), "finite_family_count")
        if n <= 7:
            for a in subsets(n):
                for b in subsets(n):
                    check((a <= b) == ((universe - b) <= (universe - a)),
                          "finite_reverse_inclusion")


@dataclass(frozen=True)
class PeriodicSet:
    """An exact eventually periodic subset of the natural numbers.

    head is the part below cutoff. Thereafter membership at n is determined by
    (n-cutoff) mod period. This represents an index set, not a forcing model.
    """
    cutoff: int
    head: frozenset[int]
    period: int
    residues: frozenset[int]

    def __post_init__(self) -> None:
        if self.cutoff < 0 or self.period <= 0:
            raise ValueError("invalid cutoff or period")
        if any(n < 0 or n >= self.cutoff for n in self.head):
            raise ValueError("head lies outside its finite domain")
        if any(r < 0 or r >= self.period for r in self.residues):
            raise ValueError("residues lie outside their period")

    def contains(self, n: int) -> bool:
        if n < 0:
            raise ValueError("indices must be nonnegative")
        return (n in self.head if n < self.cutoff
                else (n - self.cutoff) % self.period in self.residues)

    @property
    def infinite(self) -> bool:
        return bool(self.residues)

    def complement(self) -> PeriodicSet:
        return PeriodicSet(self.cutoff,
                           frozenset(range(self.cutoff)) - self.head,
                           self.period,
                           frozenset(range(self.period)) - self.residues)

    def is_subset_of(self, other: PeriodicSet) -> bool:
        # Beyond the larger cutoff, both patterns repeat with this common period.
        stop = max(self.cutoff, other.cutoff) + math.lcm(self.period, other.period)
        return all(not self.contains(n) or other.contains(n) for n in range(stop))


def check_infinite_marker_identities() -> None:
    examples = [PeriodicSet(c, h, p, r)
                for c in range(4) for h in subsets(c)
                for p in range(1, 5) for r in subsets(p)]
    for retained in examples:
        missing = retained.complement()
        # The symbolic output of the theorem has coordinate n iff n is missing,
        # and a separate lambda-plus marker iff the missing set is infinite.
        marker = missing.infinite
        check(marker == (len(missing.residues) > 0), "infinite_marker_formula")
        for n in range(64):
            check(retained.contains(n) == (not missing.contains(n)),
                  "periodic_index_recovery")
        check(missing.complement() == retained, "periodic_complement_involution")
    # Exact inclusion tests for a smaller family; periodicity makes this finite
    # reduction exact for these represented index sets, not for arbitrary sets.
    small = [e for e in examples if e.cutoff <= 2 and e.period <= 2]
    for a in small:
        for b in small:
            ma, mb = a.complement(), b.complement()
            check(a.is_subset_of(b) == mb.is_subset_of(ma),
                  "periodic_reverse_inclusion")
            if mb.is_subset_of(ma):
                check(not mb.infinite or ma.infinite, "marker_inclusion")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("finite_checks.json"))
    args = parser.parse_args()
    check_sign_cones()
    check_blocks()
    check_boolean_cubes()
    check_infinite_marker_identities()
    report = {
        "status": "all finite regression checks passed",
        "total_assertions": sum(COUNTS.values()),
        "assertions_by_group": COUNTS,
        "bounds": {
            "sign_lengths": "s <= 7; comparison x <= 9",
            "block_widths": [2, 3, 4, 5],
            "block_word_length_max": 4,
            "finite_cube_dimensions": "1 through 10; inclusion through 7",
            "periodic_sets": "cutoffs 0..3; periods 1..4",
        },
        "scope": "Finite sign/coding identities and index-set manipulations only.",
        "not_verified": [
            "freshness over inner models", "forcing", "cardinal preservation",
            "cofinality claims", "pcf input", "saturation", "class recursion",
            "the correctness of the transfinite theorems",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
