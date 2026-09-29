#!/usr/bin/env python3
"""Finite checks for the coding identities in article.tex.

These tests check finite arithmetic and sample constructions only. They do not
verify any theorem about infinite oracles, Baire category, Turing degrees, or
jumps. Python 3.10+; no third-party dependencies.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path
from typing import Sequence


def v2(n: int) -> int:
    if n <= 0:
        raise ValueError("v2 requires a positive integer")
    return (n & -n).bit_length() - 1


def position(i: int, m: int) -> int:
    if i < 0 or m < 0:
        raise ValueError("column indices must be nonnegative")
    return (1 << i) * (2 * m + 1) - 1


def inverse_position(n: int) -> tuple[int, int]:
    if n < 0:
        raise ValueError("positions must be nonnegative")
    i = v2(n + 1)
    return i, (((n + 1) >> i) - 1) // 2


def prefix_distance(a: Sequence[int], b: Sequence[int]) -> Fraction:
    if len(a) != len(b):
        raise ValueError("finite strings must have the same length")
    errors = 0
    maximum = Fraction(0)
    for length, (x, y) in enumerate(zip(a, b), start=1):
        errors += x != y
        maximum = max(maximum, Fraction(errors, length))
    return maximum


def bit(i: int, n: int) -> int:
    """A reproducible, computable sample family, not a noncomputable oracle."""
    return ((i * 7) ^ (n * 13) ^ (n >> 2)).bit_count() % 2


def robust_bit(i: int, m: int) -> int:
    """E(A_i)(m) = J(R(A_i))(m) for the sample family above."""
    if m == 0:
        return 0
    block = m.bit_length() - 1
    return bit(i, v2(block + 1))


def run_checks(max_n: int) -> dict:
    if max_n < 64:
        raise ValueError("max_n must be at least 64")
    results: dict = {}

    # Running counts are formed by actual membership, then compared to the
    # closed-form floor formula at every endpoint.
    max_k = max_n.bit_length() + 2
    tails = [0] * (max_k + 1)
    comparisons = 0
    for n in range(max_n):
        i, m = inverse_position(n)
        assert position(i, m) == n
        for k in range(min(i, max_k) + 1):
            tails[k] += 1
        for k in range(max_k + 1):
            assert tails[k] == (n + 1) // (1 << k)
            comparisons += 1
    results["column_partition_and_tail_counts"] = {
        "positions_checked": max_n,
        "tail_equalities_checked": comparisons,
        "status": "passed",
    }

    # Exhaustive finite block-majority checks, including ties.
    words_checked = wrong_majorities = sharp_cases = 0
    for k in range(4):
        length = 1 << k
        for word in itertools.product((0, 1), repeat=length):
            majority = int(sum(word) * 2 > length)
            for target in (0, 1):
                words_checked += 1
                errors = sum(x != target for x in word)
                if majority != target:
                    wrong_majorities += 1
                    assert errors * 2 >= length
                    assert Fraction(errors, 2 * length) >= Fraction(1, 4)
                    sharp_cases += Fraction(errors, 2 * length) == Fraction(1, 4)
    assert sharp_cases > 0
    results["majority_threshold"] = {
        "word_target_pairs": words_checked,
        "wrong_majorities": wrong_majorities,
        "cases_attaining_one_quarter": sharp_cases,
        "status": "passed",
    }

    triangles = 0
    for length in range(1, 5):
        words = list(itertools.product((0, 1), repeat=length))
        distances = {(a, b): prefix_distance(a, b) for a in words for b in words}
        for a in words:
            assert distances[a, a] == 0
            for b in words:
                assert distances[a, b] == distances[b, a]
                assert (distances[a, b] == 0) == (a == b)
                for c in words:
                    assert distances[a, c] <= distances[a, b] + distances[b, c]
                    triangles += 1
    results["prefix_metric"] = {
        "exhaustive_triangle_checks": triangles,
        "maximum_string_length": 4,
        "status": "passed",
    }

    rng = random.Random(20260928)
    patch_checks = 2000
    for _ in range(patch_checks):
        length = rng.randrange(1, 65)
        end = rng.randrange(length + 1)
        center = [rng.randrange(2) for _ in range(length)]
        prefix = [rng.randrange(2) for _ in range(end)]
        patched = prefix + center[end:]
        finite_max = prefix_distance(prefix, center[:end])
        assert prefix_distance(patched, center) == finite_max
    # Non-vacuous instances of the local-decoder geometry: close Y and an
    # accepted prefix produce a patch remaining in the outer ball.
    local_checks = 0
    for length in (64, 96, 128):
        for _ in range(100):
            center = [rng.randrange(2) for _ in range(length)]
            oracle = center.copy()
            oracle[rng.randrange(length // 2, length)] ^= 1
            end = rng.randrange(length // 2 + 1, length + 1)
            prefix = oracle[:end]
            prefix[rng.randrange(length // 4, end)] ^= 1
            radius = Fraction(1, 2)
            assert prefix_distance(oracle, center) < radius / 4
            assert prefix_distance(prefix, oracle[:end]) < radius / 2
            patch = prefix + center[end:]
            assert prefix_distance(patch, center) < radius
            local_checks += 1
    results["patch_and_decoder_geometry"] = {
        "patch_equalities": patch_checks,
        "nonvacuous_local_ball_checks": local_checks,
        "status": "passed",
    }

    index_checks = 0
    for n in range(16):
        for s in range(512):
            p = position(n, s)
            assert p >= s
            assert v2(p + 1) == n
            index_checks += 1
    results["whole_real_recovery_indices"] = {
        "index_pairs_checked": index_checks,
        "status": "passed",
    }

    # Simulate equation (6.3): every row becomes wholly correct after its own
    # threshold. Check the exact finite head + tail bound, not just densities.
    thresholds = lambda i: 3 * (i + 1) ** 2 + 1
    head_bounds = [sum(thresholds(i) - 1 for i in range(k)) for k in range(max_k + 1)]
    errors = 0
    bound_checks = 0
    density_samples = []
    sample_ends = {2**k for k in range(6, max_n.bit_length())} | {max_n}
    for n in range(max_n):
        i, m = inverse_position(n)
        target = robust_bit(i, m)
        if m == 0:
            output = 0
        else:
            coordinate = v2(m.bit_length())
            approximate_row_bit = bit(i, coordinate)
            if m < thresholds(i):
                approximate_row_bit ^= 1
            output = approximate_row_bit
        if m >= thresholds(i):
            assert output == target
        errors += output != target
        N = n + 1
        for k in range(max_k + 1):
            assert errors <= head_bounds[k] + N // (1 << k)
            bound_checks += 1
        if N in sample_ends:
            density_samples.append({"N": N, "errors": errors,
                                    "error_fraction": str(Fraction(errors, N))})
    results["row_assembly"] = {
        "positions_checked": max_n,
        "finite_head_tail_bound_checks": bound_checks,
        "sample_densities": density_samples,
        "status": "passed",
    }

    # All inputs A_i in this example are constant computable reals. The sample
    # choice H is computable; only the finite support identity is being tested.
    exception_count = 0
    for n in range(max_n):
        i, m = inverse_position(n)
        h_i = i.bit_count() % 2
        target_r = h_i
        coded_x = h_i if m > 0 else 0
        if target_r != coded_x:
            exception_count += 1
            assert n == (1 << i) - 1
        assert exception_count <= (n + 1).bit_length()
    results["constant_row_presentation"] = {
        "positions_checked": max_n,
        "actual_sample_exceptions": exception_count,
        "status": "passed",
    }

    return {
        "status": "all finite checks passed",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "seed_for_random_checks": 20260928,
        "max_n": max_n,
        "scope": "Finite arithmetic identities and sample coding geometry only.",
        "not_verified": ["infinitary convergence", "Baire category", "Turing reducibility",
                         "jump inversion", "full mathematical theorems", "global novelty"],
        "checks": results,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=32768)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()
    if args.max_n < 64:
        parser.error("--max-n must be at least 64")
    result = run_checks(args.max_n)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(result["status"])
    for name, check in result["checks"].items():
        print(f"  {name}: {check['status']}")
    print(f"Results: {args.output}")


if __name__ == "__main__":
    main()
