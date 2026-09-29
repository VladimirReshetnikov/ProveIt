#!/usr/bin/env python3
"""Finite checks for article.tex (not a verification of its infinite theorems).

Standard library only. Run:
    python3 checks/check_finite.py --output checks/results.json

No noncomputable oracle, infinite density, or Turing nonreducibility is simulated.
All counts and inequalities are checked exactly with integer/rational arithmetic.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import random
from fractions import Fraction
from pathlib import Path
from typing import Any


def v2(n: int) -> int:
    if n <= 0:
        raise ValueError("v2 is defined here only for positive integers")
    return (n & -n).bit_length() - 1


def column(n: int, k: int) -> int:
    if n < 0 or k < 0:
        raise ValueError("Column and within-column indices must be nonnegative")
    return (1 << n) * (2 * k + 1) - 1


def next_label(k: int, stage: int) -> int:
    """Least block m >= stage with v2(m+1) = k."""
    if k < 0 or stage < 0:
        raise ValueError("Inputs must be nonnegative")
    first, step = (1 << k) - 1, 1 << (k + 1)
    q = max(0, (stage - first + step - 1) // step)
    return first + q * step


def run_checks() -> dict[str, Any]:
    results: list[dict[str, Any]] = []

    # 1. Column partition, inverse map, exact tail counts.
    count = 0
    max_prefix = 4096
    indices = [v2(k + 1) for k in range(max_prefix)]
    for m, n in enumerate(indices):
        k = ((m + 1) // (1 << n) - 1) // 2
        assert column(n, k) == m
        count += 1
    for s in range(14):
        running = 0
        for m in range(max_prefix + 1):
            if m:
                running += indices[m - 1] >= s
            assert running == m // (1 << s)
            assert running * (1 << s) <= m
            count += 1
    results.append({"name": "column_partition_and_tail", "cases": count,
                    "max_prefix": max_prefix, "max_tail_level": 13})

    # 2. Odd and even prefix lengths in the joined space.
    count = 0
    for s in range(12):
        running = 0
        for m in range(8193):
            if m:
                position = m - 1
                running += v2(position // 2 + 1) >= s
            predicted = ((m + 1) // 2) // (1 << s) + (m // 2) // (1 << s)
            assert running == predicted
            assert running * (1 << s) <= m
            count += 1
    results.append({"name": "joined_tail_including_odd_prefixes", "cases": count,
                    "max_prefix": 8192, "max_tail_level": 11})

    # 3. Factorial-block majority bound, exhaustive over the number of ones.
    # Counts characterize all binary blocks, so no long bit strings are allocated.
    count = wrong_cases = 0
    for m in range(7):
        start, end = math.factorial(m + 1), math.factorial(m + 2)
        length = end - start
        bound = Fraction(m + 1, 2 * (m + 2))
        assert Fraction(length, 2 * end) == bound
        for true_bit in (0, 1):
            for ones in range(length + 1):
                majority = int(2 * ones > length)  # ties choose zero
                errors = ones if true_bit == 0 else length - ones
                if majority != true_bit:
                    assert 2 * errors >= length
                    assert Fraction(errors, end) >= bound
                    wrong_cases += 1
                count += 1
    results.append({"name": "factorial_majority_endpoint_bound", "cases": count,
                    "wrong_majority_cases": wrong_cases, "block_indices": [0, 6],
                    "largest_block_length": math.factorial(8) - math.factorial(7)})

    # 4. Repetition schedule and the finite combinatorial recovery mechanism.
    # This is a block-majority abstraction, not an infinite-oracle computation.
    count = 0
    corrupted_blocks = {0, 2, 5}
    for k in range(13):
        true_bit = (k * k + k // 2 + 1) % 2
        for stage in range(1001):
            m = next_label(k, stage)
            assert m >= stage and v2(m + 1) == k
            assert m - (1 << (k + 1)) < stage
            decoded = 1 - true_bit if m in corrupted_blocks else true_bit
            if stage > max(corrupted_blocks):
                assert decoded == true_bit
            count += 1
    results.append({"name": "repeated_label_recovery_finite_model", "cases": count,
                    "labels": [0, 12], "stages": [0, 1000],
                    "corrupted_blocks": sorted(corrupted_blocks)})

    # 5. Exhaustive finite endpoint estimate for column pullbacks.
    count = 0
    length = 12
    for mask in range(1 << length):
        for n in range(4):
            for t in range(1, length + 1):
                end = column(n, t - 1) + 1
                if end > length:
                    break
                local_errors = sum((mask >> column(n, k)) & 1 for k in range(t))
                global_errors = (mask & ((1 << end) - 1)).bit_count()
                assert local_errors <= global_errors
                assert Fraction(local_errors, t) <= Fraction(end, t) * Fraction(global_errors, end)
                count += 1
    results.append({"name": "column_pullback_finite_endpoint", "cases": count,
                    "all_error_masks_of_length": length})

    # 6. Density bookkeeping from a finite exceptional prefix plus a tail.
    rng = random.Random(20260928)
    count = 0
    for _ in range(120):
        s = rng.randrange(1, 11)
        prefix = rng.randrange(0, 200)
        cumulative = 0
        for m in range(1, 2049):
            k = m - 1
            allowed = k < prefix or v2(k + 1) >= s
            error = allowed and bool(rng.getrandbits(1))
            cumulative += error
            assert cumulative <= min(prefix, m) + m // (1 << s)
            # The proof's weaker but convenient M/m + 2^-s bound.
            assert cumulative * (1 << s) <= prefix * (1 << s) + m
            count += 1
    results.append({"name": "protected_region_finite_prefix_bound", "cases": count,
                    "samples": 120, "prefix_length": 2048, "seed": 20260928})

    # 7. Independence is essential: exhaust all small partial-output tables.
    # None = no convergence; finite admissible subsets are selected independently.
    count = applicable = 0
    tables = list(itertools.product((None, 0, 1), repeat=3))
    for left_table in tables:
        for right_table in tables:
            for left_mask in range(1, 8):
                left = [x for i, x in enumerate(left_table)
                        if left_mask & (1 << i) and x is not None]
                for right_mask in range(1, 8):
                    right = [x for i, x in enumerate(right_table)
                             if right_mask & (1 << i) and x is not None]
                    split = any(a != b for a in left for b in right)
                    if left and right and not split:
                        assert len(set(left + right)) == 1
                        assert all(left[0] == b for b in right)
                        applicable += 1
                    count += 1
    results.append({"name": "cross_disagreement_finite_independent_model", "cases": count,
                    "nonempty_no_split_cases": applicable,
                    "note": "Checks only the finite output-value logic, not computability or totality."})

    # 8. Carrier from constant rows differs from R(B) only at local argument zero.
    count = 0
    bits = [rng.randrange(2) for _ in range(16)]
    for position in range(32768):
        n = v2(position + 1)
        local = ((position + 1) // (1 << n) - 1) // 2
        carrier_value = 0 if local == 0 else bits[n]
        dyadic_value = bits[n]
        if carrier_value != dyadic_value:
            assert position == (1 << n) - 1
        count += 1
    results.append({"name": "presentation_sensitivity_exceptional_positions", "cases": count,
                    "max_prefix": 32768})

    return {"status": "passed", "scope": "finite identities and finite models only",
            "infinite_theorems_formally_verified": False,
            "test_groups": len(results), "total_cases": sum(r["cases"] for r in results),
            "results": results}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()
    results = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
