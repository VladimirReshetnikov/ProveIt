#!/usr/bin/env python3
"""Exact finite checks for the countable ordinal multiplexer.

This program specializes ordinal inputs to ordinary nonnegative integers,
so all exponent-band arithmetic is rational. It does NOT implement surreal
arithmetic, infinite sums, transfinite ordinals, satisfaction, HOD, or forcing.
The accompanying mathematical proofs establish the infinite statements.

Usage: python3 code/verify_code.py --output data/verification.json
"""
from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction
from pathlib import Path
from typing import Sequence


def require_natural(value: int, name: str) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def band(n: int) -> tuple[Fraction, Fraction]:
    require_natural(n, "n")
    return Fraction(1, 2 ** (n + 1)), Fraction(3, 2 ** (n + 2))


def encode_exponent(n: int, a: int) -> Fraction:
    require_natural(n, "n")
    require_natural(a, "a")
    return Fraction(1, 2 ** (n + 1)) + Fraction(a, (a + 1) * 2 ** (n + 2))


def decode_exponent(n: int, exponent: Fraction) -> Fraction:
    lower, upper = band(n)
    if not lower <= exponent < upper:
        raise ValueError("exponent is outside the specified half-open band")
    v = 2 ** (n + 2) * (exponent - lower)
    return v / (1 - v)


def check_sequence(values: Sequence[int]) -> None:
    exponents = [encode_exponent(n, a) for n, a in enumerate(values)]
    for n, (a, exponent) in enumerate(zip(values, exponents)):
        lower, upper = band(n)
        assert lower <= exponent < upper
        assert 0 < exponent < 1
        assert decode_exponent(n, exponent) == a
    assert all(x > y for x, y in zip(exponents, exponents[1:]))
    assert len(set(exponents)) == len(exponents)


def run_checks(seed: int = 20261004) -> dict[str, object]:
    rng = random.Random(seed)
    deterministic = [
        [], [0], [0] * 100, list(range(200)), list(reversed(range(200))),
        [10**40, 0, 7, 7, 1, 10**80, 0],
    ]
    for values in deterministic:
        check_sequence(values)
    inverse_checks = sum(len(s) for s in deterministic)
    for _ in range(200):
        values = [rng.randrange(10**30) for _ in range(100)]
        check_sequence(values)
        inverse_checks += len(values)
    for n in range(1000):
        lower, upper = band(n)
        next_lower, next_upper = band(n + 1)
        assert next_lower < next_upper < lower < upper
    # Explicit finite prefix printed in the manuscript.
    expected = [Fraction(1, 2), Fraction(5, 16), Fraction(1, 6), Fraction(11, 128)]
    assert [encode_exponent(n, n) for n in range(4)] == expected
    # Invalid values and the excluded upper endpoint must be rejected.
    rejected = 0
    for n, value in [(-1, 0), (0, -1), (True, 0)]:
        try:
            encode_exponent(n, value)
        except ValueError:
            rejected += 1
        else:
            raise AssertionError("invalid natural input accepted")
    try:
        decode_exponent(2, band(2)[1])
    except ValueError:
        rejected += 1
    else:
        raise AssertionError("excluded upper band endpoint accepted")
    return {
        "status": "all checks passed",
        "seed": seed,
        "exact_inverse_checks": inverse_checks,
        "sequence_order_checks": len(deterministic) + 200,
        "adjacent_band_checks": 1000,
        "invalid_input_checks": rejected,
        "printed_example": [
            {"n": n, "a": n, "exponent": str(e), "decoded": str(decode_exponent(n, e))}
            for n, e in enumerate(expected)
        ],
        "scope": "finite rational arithmetic only; no transfinite or definability verification",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional path for a JSON results file")
    args = parser.parse_args()
    results = run_checks()
    payload = json.dumps(results, indent=2) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    print(payload, end="")


if __name__ == "__main__":
    main()
