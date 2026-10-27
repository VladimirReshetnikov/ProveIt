#!/usr/bin/env python3
"""Finite checks for a scoped explicit-boundary-table barrier.

This is not a SAT solver and does not test an asymptotic SAT lower bound.
Only Python's standard library is used; no input files are read.
"""

from __future__ import annotations

import argparse
import json
from math import ceil


def optimal_peak_boundary(r: int) -> tuple[int, list[int]]:
    """Minimize the peak boundary in a binary full-table contraction tree."""
    best = [0] * (r + 1)
    split = [0] * (r + 1)
    best[1] = 2 * (r - 1)
    for k in range(2, r + 1):
        value, left = min(
            (max(best[a], best[k - a]), a)
            for a in range(1, k // 2 + 1)
        )
        best[k] = max(2 * k * (r - k), value)
        split[k] = left
    return best[r], split


def predicted_peak_boundary(r: int) -> int:
    k = (r + 2) // 3
    return 2 * k * (r - k)


def exact_subset_counts(weights: list[int]) -> list[int]:
    """Counts binary subsets by exact total weight (0/1 choices only)."""
    counts = [1]
    for weight in weights:
        updated = counts + [0] * weight
        for old_weight, multiplicity in enumerate(counts):
            updated[old_weight + weight] += multiplicity
        counts = updated
    return counts


def check_uniform_exact_budget(r: int, colors: int, modes: int, shift: int) -> dict:
    base_weights = [shift + 4 * q - 2 * q.bit_count() for q in range(modes)]
    weights = base_weights * colors
    if not all(w > 0 for w in weights):
        raise ValueError("Weights must be positive")
    counts = exact_subset_counts(weights)
    total = 1 << len(weights)
    B = sum(weights)
    if len(counts) != B + 1 or sum(counts) != total:
        raise AssertionError("Subset counts failed to conserve all choices")
    b_star = max(range(len(counts)), key=counts.__getitem__)
    Q = counts[b_star]
    if Q * (B + 1) < total:
        raise AssertionError("Pigeonhole lower bound failed")
    P = r * (r - 1) * B + 1
    actual_budget = r * (r - 1) * b_star
    if not actual_budget < P:
        raise AssertionError("Uniform exact-weight allocation is not feasible")
    return {
        "r": r,
        "colors": colors,
        "modes_per_color": modes,
        "shift": shift,
        "base_weights": base_weights,
        "binary_choices": len(weights),
        "all_subset_count": total,
        "maximum_subset_weight": B,
        "chosen_exact_weight": b_star,
        "exact_list_cardinality": Q,
        "strict_global_budget": P,
        "uniform_array_weight": actual_budget,
        "minimum_peak_boundary_indices": predicted_peak_boundary(r),
        "mandatory_table_cells": Q ** predicted_peak_boundary(r),
    }


def run_checks(max_r: int) -> dict:
    width_results = []
    for r in range(3, max_r + 1):
        actual, _ = optimal_peak_boundary(r)
        predicted = predicted_peak_boundary(r)
        if actual != predicted:
            raise AssertionError((r, actual, predicted))
        if 9 * predicted < 4 * r * r:
            raise AssertionError("Quadratic lower bound failed")
        width_results.append({"r": r, "optimal_peak": actual})
    fixtures = [
        check_uniform_exact_budget(r, c, J, A)
        for r, c, J, A in [(3, 1, 4, 1), (4, 2, 8, 3), (8, 3, 10, 4), (9, 2, 12, 5)]
    ]
    return {
        "status": "PASS",
        "scope": "finite checks of an explicit-table architecture barrier; no SAT lower bound",
        "checked_r_range": [3, max_r],
        "checked_r_count": len(width_results),
        "width_samples": [x for x in width_results if x["r"] <= 12 or x["r"] == max_r],
        "exact_budget_fixtures": fixtures,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-r", type=int, default=150)
    parser.add_argument("--output")
    args = parser.parse_args()
    if args.max_r < 3:
        parser.error("--max-r must be at least 3")
    result = run_checks(args.max_r)
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as stream:
            stream.write(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
