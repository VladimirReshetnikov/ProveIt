#!/usr/bin/env python3
"""Finite checks of the coding conventions in Beyond Ord.

These checks do NOT establish class well-foundedness, set-interval
condensation, truth existence, or an axiom bound. Every interval of a
finite order is a set, so finite truncation partitions must not be
mistaken for a simulation of genuine class condensation.

Run: python3 finite_checks.py --output verification_results.json
Requires Python 3.10+ and only the standard library.
"""
from __future__ import annotations

import argparse
import itertools
import json
from collections import defaultdict
from pathlib import Path
from typing import Iterable

Digits = tuple[int, ...]  # increasing exponent order: least significant first


def sign(value: int) -> int:
    return (value > 0) - (value < 0)


def validate(p: Digits, base: int) -> None:
    if base < 2 or any(not isinstance(a, int) or a < 0 or a >= base for a in p):
        raise ValueError("The base must be >= 2 and every digit must be in range.")


def rank(p: Digits, base: int) -> int:
    validate(p, base)
    value = 0
    for coefficient in reversed(p):
        value = value * base + coefficient
    return value


def unrank(value: int, base: int, width: int) -> Digits:
    if base < 2 or width < 0 or not 0 <= value < base**width:
        raise ValueError("Invalid positional rank, base, or width.")
    output = []
    for _ in range(width):
        value, digit = divmod(value, base)
        output.append(digit)
    return tuple(output)


def compare(p: Digits, q: Digits) -> int:
    """Greatest-differing-exponent comparison, including missing zeros."""
    for i in range(max(len(p), len(q)) - 1, -1, -1):
        a = p[i] if i < len(p) else 0
        b = q[i] if i < len(q) else 0
        if a != b:
            return sign(a - b)
    return 0


def all_digits(base: int, width: int) -> Iterable[Digits]:
    return itertools.product(range(base), repeat=width)


def run_checks() -> dict[str, object]:
    counts: dict[str, int] = defaultdict(int)

    def check(name: str, condition: bool) -> None:
        if not condition:
            raise AssertionError(f"Check failed in {name}")
        counts[name] += 1

    # Exhaustive order comparisons in modest finite powers.
    for base, max_width in [(2, 6), (3, 4), (4, 4)]:
        for width in range(max_width + 1):
            points = list(all_digits(base, width))
            values = {p: rank(p, base) for p in points}
            for p in points:
                check("rank_round_trip", unrank(values[p], base, width) == p)
                # Trailing zeros do not change the represented finite support.
                check("zero_extension", compare(p, p + (0, 0)) == 0)
                for q in points:
                    check("greatest_difference_order",
                          compare(p, q) == sign(values[p] - values[q]))

    # A^(B+C) = A^B * A^C: the C portion is the significant coordinate.
    for base in (2, 3, 4):
        for b in range(4):
            for c in range(4):
                width = b + c
                for p in all_digits(base, width):
                    low, high = p[:b], p[b:]
                    pair_rank = rank(high, base) * base**b + rank(low, base)
                    check("exponent_sum_split", pair_rank == rank(p, base))
                    check("exponent_sum_inverse", low + high == p)

    # (A^B)^C = A^(B*C): flatten each coefficient polynomial into a C-block.
    for base in (2, 3, 4):
        for b in range(4):
            for c in range(4):
                if b * c > 6:
                    continue
                number = base ** (b * c)
                for value in range(number):
                    if b == 0:
                        nested = (0,) * c  # one-point coefficient order
                    else:
                        nested = unrank(value, base**b, c)
                    flat = tuple(d for coefficient in nested
                                 for d in unrank(coefficient, base, b))
                    check("nested_power_flatten", rank(flat, base) == value)
                    recovered = tuple(rank(flat[j*b:(j+1)*b], base)
                                      for j in range(c))
                    check("nested_power_inverse", recovered == nested)

    # Truncation partitions and their canonical least representatives.
    # These are NOT set-interval condensation of a finite order.
    for base in (2, 3, 4):
        for width in range(6):
            points = list(all_digits(base, width))
            for cutoff in range(width + 1):
                fibers: dict[Digits, list[int]] = defaultdict(list)
                for p in points:
                    low, high = p[:cutoff], p[cutoff:]
                    representative = (0,) * cutoff + high
                    value = rank(p, base)
                    check("truncation_quotient_rank",
                          rank(high, base) == value // base**cutoff)
                    check("truncation_fiber_rank",
                          rank(low, base) == value % base**cutoff)
                    check("truncation_minimum", compare(representative, p) <= 0)
                    fibers[high].append(value)
                for high, values in fibers.items():
                    start = rank(high, base) * base**cutoff
                    expected = list(range(start, start + base**cutoff))
                    check("truncation_convex_fiber", sorted(values) == expected)

    check("orientation_counterexample", compare((1, 0), (0, 1)) == -1)
    return {
        "status": "passed",
        "scope": "Finite coding conventions only; not a proof of the class theorems.",
        "total_assertions": sum(counts.values()),
        "assertions_by_category": dict(sorted(counts.items())),
        "tested_bases": [2, 3, 4],
        "max_exponent_width": 6,
        "dependencies": "Python standard library only",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Optionally write the deterministic JSON result here.")
    args = parser.parse_args()
    result = run_checks()
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    print(payload, end="")


if __name__ == "__main__":
    main()
