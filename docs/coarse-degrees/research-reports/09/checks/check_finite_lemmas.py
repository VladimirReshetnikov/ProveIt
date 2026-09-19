#!/usr/bin/env python3
"""Finite arithmetic checks for coarse_degree_attack.tex.

These checks do NOT establish any assertion about infinite oracles, Turing
reducibility, category, perfect sets, asymptotic limits, or mathematical novelty.
No third-party Python packages are required. Compatible with Python 3.9+.
"""
from __future__ import annotations

import argparse
import itertools
import json
import platform
from fractions import Fraction
from pathlib import Path
from typing import Dict, Sequence, Tuple

Bits = Tuple[int, ...]


def require(condition: bool, message: str) -> None:
    """Keep checks active even when Python is invoked with -O."""
    if not condition:
        raise AssertionError(message)


def words(length: int):
    return itertools.product((0, 1), repeat=length)


def distance(a: Sequence[int], b: Sequence[int]) -> Fraction:
    if len(a) != len(b):
        raise ValueError("Finite distance requires equal lengths.")
    mismatches = 0
    bound = Fraction(0)
    for n, (x, y) in enumerate(zip(a, b), start=1):
        mismatches += x != y
        bound = max(bound, Fraction(mismatches, n))
    return bound


def valuation2(n: int) -> int:
    if n <= 0:
        raise ValueError("valuation2 requires a positive integer.")
    return (n & -n).bit_length() - 1


def check_metrics() -> Dict[str, int]:
    triangle_count = 0
    patch_count = 0
    local_patch_count = 0
    # Exhaustive finite metric axioms for lengths through five.
    for length in range(6):
        ws = list(words(length))
        ds = {(a, b): distance(a, b) for a in ws for b in ws}
        for a, b, c in itertools.product(ws, repeat=3):
            require(ds[a, c] <= ds[a, b] + ds[b, c], "Triangle inequality")
            require(ds[a, b] == ds[b, a], "Symmetry")
            require((ds[a, b] == 0) == (a == b), "Separation")
            triangle_count += 1
    # The patched tail agrees exactly, so the supremum occurs by |sigma|.
    for length in range(8):
        for z in words(length):
            for cut in range(length + 1):
                for sigma in words(cut):
                    patched = sigma + z[cut:]
                    require(distance(patched, z) == distance(sigma, z[:cut]),
                            "Prefix-patching identity")
                    patch_count += 1
    # Numerical inequality used when the computable center is outside C_X.
    for length in range(5):
        ws = list(words(length))
        for y, center in itertools.product(ws, repeat=2):
            center_error = distance(y, center)
            for cut in range(length + 1):
                for sigma in words(cut):
                    patched = sigma + y[cut:]
                    require(distance(patched, y)
                            <= distance(sigma, center[:cut]) + center_error,
                            "Local recovery patch estimate")
                    local_patch_count += 1
    return {"metric_triples": triangle_count,
            "prefix_patch_cases": patch_count,
            "local_recovery_patch_cases": local_patch_count}


def check_columns() -> Dict[str, int]:
    column_counts = tail_counts = 0
    for n in range(4097):
        histogram = [0] * 13
        for m in range(n):
            e = valuation2(m + 1)
            if e < len(histogram):
                histogram[e] += 1
        for e in range(13):
            expected = (n + (1 << e)) // (1 << (e + 1))
            require(histogram[e] == expected, "Positive-density column count")
            column_counts += 1
        for k in range(13):
            require(sum(histogram[k:]) == n // (1 << k), "Tail column count")
            tail_counts += 1
    approx_cases = 0
    for length in range(11):
        for x in words(length):
            for k in range(6):
                c = tuple(bit if valuation2(i + 1) < k else 0
                          for i, bit in enumerate(x))
                error = sum(a != b for a, b in zip(x, c))
                require(error <= length // (1 << k), "Column truncation error")
                approx_cases += 1
    return {"column_count_cases": column_counts,
            "tail_count_cases": tail_counts,
            "truncation_error_cases": approx_cases}


def check_guarded_diagonal() -> Dict[str, int]:
    # -1 means permanently undefined in this finite model, NOT merely slow.
    # Each table stands for one possible partial binary program on a prefix.
    guarded_cases = stage_cases = 0
    for length in range(8):
        for table in itertools.product((-1, 0, 1), repeat=length):
            first_bad = next((i for i, b in enumerate(table) if b == -1), length)
            for e in range(4):
                x = tuple(int(valuation2(n + 1) == e
                              and all(table[m] >= 0 for m in range(n + 1))
                              and table[n] == 0)
                          for n in range(length))
                require(all(not x[n] for n in range(first_bad, length)),
                        "A permanently bad prefix blocks the rest of a column")
                if first_bad == length:
                    require(all(x[n] == 1 - table[n] for n in range(length)
                                if valuation2(n + 1) == e),
                            "Total table is complemented on its column")
                guarded_cases += 1
            # A finite delayed convergence model checks c.e. monotonicity.
            previous = (0,) * length
            for stage in range(length + 2):
                current = tuple(int(table[n] == 0 and all(
                    table[m] >= 0 and m + 1 <= stage for m in range(n + 1)))
                                for n in range(length))
                require(all(a <= b for a, b in zip(previous, current)),
                        "The guarded enumeration must be monotone")
                previous = current
                stage_cases += 1
    return {"guarded_column_cases": guarded_cases,
            "monotone_stage_cases": stage_cases}


def check_majority() -> Dict[str, int]:
    cases = 0
    for length in (1, 2, 4, 8, 16):
        for bit in (0, 1):
            for observed in words(length):
                errors = sum(value != bit for value in observed)
                if errors * 2 < length:
                    majority = int(sum(observed) * 2 > length)
                    require(majority == bit, "Strict majority decoder")
                    cases += 1
    return {"majority_decoding_cases": cases}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()
    counters: Dict[str, int] = {}
    for test in (check_metrics, check_columns, check_guarded_diagonal, check_majority):
        counters.update(test())
    result = {
        "status": "PASS",
        "python_version": platform.python_version(),
        "arithmetic": "Exact integers and fractions; exhaustive stated finite ranges",
        "counters": counters,
        "total_checked_cases": sum(counters.values()),
        "scope": "Finite arithmetic and finite-stage models only",
        "not_verified": ["infinite density limits", "Turing reducibility",
                         "Baire-category arguments", "perfect-set fusion",
                         "Lean kernel proofs", "novelty"]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
