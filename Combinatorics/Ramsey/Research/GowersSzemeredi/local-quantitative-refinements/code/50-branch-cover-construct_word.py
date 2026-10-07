#!/usr/bin/env python3
"""Exact conditional-expectation construction of an AP-balanced word.

Runtime is polynomial in the field size, not its bit length. The general
counterexample's field is intentionally NOT instantiated. This implementation
is for small examples and validation of the construction method.
"""
from __future__ import annotations
import argparse
import json
import math
from fractions import Fraction
from pathlib import Path
from verify import ap_masks


def construct(p: int, R: int, L: int, epsilon: Fraction) -> dict:
    if not 2 <= R <= p or not 0 < epsilon < 1:
        raise ValueError("Require 2 <= R <= p and 0 < epsilon < 1")
    aps = ap_masks(p, L)
    lengths = [I.bit_count() for I in aps]
    powers = [R ** m for m in range(p + 1)]
    cdf = [[sum(math.comb(m, j) * (R - 1) ** (m - j) for j in range(k + 1))
            for k in range(m + 1)] for m in range(p + 1)]
    lower, upper = {}, {}
    for n in set(lengths):
        lo = n * (Fraction(1, R) - epsilon)
        hi = n * (Fraction(1, R) + epsilon)
        lower[n] = math.ceil(lo) - 1
        upper[n] = math.floor(hi) + 1

    def cumulative(m: int, k: int) -> int:
        return 0 if k < 0 else powers[m] if k >= m else cdf[m][k]

    def score(assigned: int, color_masks: list[int]) -> int:
        total = 0
        for I, n in zip(aps, lengths):
            m = n - (I & assigned).bit_count()
            for color in color_masks:
                c = (I & color).bit_count()
                bad = cumulative(m, lower[n] - c)
                bad += powers[m] - cumulative(m, upper[n] - c - 1)
                total += bad * powers[p - m]
        return total

    colors = [0] * R
    initial = score(0, colors)
    if initial >= powers[p]:
        raise ValueError("Initial expected bad-event count is not below one; increase L or epsilon")
    previous = initial
    word = []
    for x in range(p):
        assigned = (1 << (x + 1)) - 1
        options = []
        for j in range(R):
            colors[j] |= 1 << x
            options.append(score(assigned, colors))
            colors[j] ^= 1 << x
        chosen = min(range(R), key=lambda j: (options[j], j))
        assert options[chosen] <= previous
        colors[chosen] |= 1 << x
        word.append(chosen)
        previous = options[chosen]
    assert previous == 0
    max_error = max(abs(Fraction((I & col).bit_count(), n) - Fraction(1, R))
                    for I, n in zip(aps, lengths) for col in colors)
    assert max_error <= epsilon
    return {"status": "PASS", "method": "exact conditional expectation",
            "p": p, "R": R, "L": L, "epsilon": str(epsilon),
            "distinct_AP_sets": len(aps),
            "initial_expected_bad_events": str(Fraction(initial, powers[p])),
            "final_bad_events": 0, "maximum_error": str(max_error), "word": word}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--p", type=int, default=31)
    parser.add_argument("--R", type=int, default=2)
    parser.add_argument("--L", type=int, default=20)
    parser.add_argument("--epsilon", type=Fraction, default=Fraction(2, 5))
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "data" / "construction.json")
    args = parser.parse_args()
    result = construct(args.p, args.R, args.L, args.epsilon)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
