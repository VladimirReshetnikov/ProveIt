#!/usr/bin/env python3
"""Independent integer-only comparisons for the two-leaf minimality cases.

This is separate from enumerate_reporters.py: all comparisons in the inner
loop are cross-products of integers, with a Fraction constructed only for
the final maximum.  Nonempty proper sum-level tests and all surjective
two-valued selectors are enumerated.  Run, for example:

    python code/enumerate_two_leaf_integer.py --block-size 6
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path


EXPECTED = {
    4: (13050, Fraction(-1, 12)),
    5: (117242, Fraction(-595, 8576)),
    6: (992250, Fraction(-1293, 33152)),
}


def enumerate_two(n: int) -> dict:
    total = 1 << n
    values = [2 * j - n for j in range(n + 1)]
    counts = [comb(n, j) for j in range(n + 1)]
    events = []
    for mask in range(1, (1 << (n + 1)) - 1):
        indices = [j for j in range(n + 1) if (mask >> j) & 1]
        mass = sum(counts[j] for j in indices)
        first = sum(counts[j] * values[j] for j in indices)
        second = sum(counts[j] * values[j] ** 2 for j in indices)
        events.append((mask, mass, first, second))

    best_num = None
    best_den = None
    best_parameters = None
    examined = 0
    positive = 0
    for event_a, event_b in combinations(events, 2):
        mask_a, a, a1, a2 = event_a
        mask_b, b, b1, b2 = event_b
        va = a2 * a - a1 * a1
        vb = b2 * b - b1 * b1
        a_sq, b_sq = a * a, b * b
        a_cu, b_cu = a_sq * a, b_sq * b
        s_num = va * b_sq + vb * a_sq
        for selector, p, q, r in events:
            # The selector mask gives exactly the sums choosing leaf zero.
            k_num = p * b + (total - p) * a - a * b
            r1_num = q * a * b * (b - a) - p * a1 * b_sq
            r1_num -= (total - p) * b1 * a_sq
            h_num = r * a_sq * b_cu - 2 * q * a1 * a * b_cu
            h_num += p * (2 * a1 * a1 - a2 * a) * b_cu
            h_num += (total * n - r) * a_cu * b_sq
            h_num += 2 * q * b1 * a_cu * b
            h_num += (total - p) * (2 * b1 * b1 - b2 * b) * a_cu
            gap_num = r1_num * r1_num - k_num * h_num
            gap_num -= k_num * k_num * s_num
            gap_den = total * total * a_sq * b_sq * k_num
            assert gap_den > 0
            examined += 1
            positive += gap_num > 0
            if best_num is None or gap_num * best_den > best_num * gap_den:
                best_num, best_den = gap_num, gap_den
                best_parameters = (mask_a, mask_b, selector)

    assert best_num is not None and best_den is not None
    maximum = Fraction(best_num, best_den)
    if n in EXPECTED:
        expected_count, expected_maximum = EXPECTED[n]
        assert examined == expected_count
        assert maximum == expected_maximum
        assert positive == 0
    return {
        "description": "Independent cross-multiplied integer verification of a two-leaf reporter case",
        "block_size": n,
        "leaves": 2,
        "exact_configurations": examined,
        "positive_configurations": positive,
        "maximum_advantage": str(maximum),
        "one_maximizer_event_masks_and_selector_zero_mask": best_parameters,
        "all_assertions_passed": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--block-size", type=int, default=6, choices=(4, 5, 6))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = enumerate_two(args.block_size)
    output = json.dumps(result, indent=2) + "\n"
    if args.output is None:
        print(output, end="")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output, encoding="utf-8")
        print(f"PASS: independent integer enumeration, n={args.block_size}; {args.output}")


if __name__ == "__main__":
    main()
