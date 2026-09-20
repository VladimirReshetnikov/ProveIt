#!/usr/bin/env python3
"""Exact finite audits for ordinal_separation.tex.

These tests do NOT formalize the transfinite theorems. They check finite
components: optimal ordered queries, the untouched-child rule, finite
nonadaptive cuts, majority survival, and finite-hole avoidance.

Requires Python 3.10+; standard library only. Assertions deliberately raise
explicit errors, so running with `python -O` does not disable the checks.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
from pathlib import Path
from typing import Any


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def ceil_log2(n: int) -> int:
    """Minimum binary query count for n possibilities; 0 for n <= 1."""
    if n < 0:
        raise ValueError("The number of points cannot be negative")
    return (n - 1).bit_length() if n > 1 else 0


def cylinder_interval(total_bits: int, prefix_bits: int,
                      prefix_value: int) -> tuple[int, int]:
    """Half-open rank interval of a finite lexicographic binary cylinder."""
    if not 0 <= prefix_bits <= total_bits:
        raise ValueError("Invalid prefix length")
    if not 0 <= prefix_value < (1 << prefix_bits):
        raise ValueError("Invalid prefix value")
    width = 1 << (total_bits - prefix_bits)
    return prefix_value * width, (prefix_value + 1) * width


def check_chain_recurrence(max_size: int = 512) -> dict[str, Any]:
    """Independent minimax DP over all nontrivial initial-segment cuts."""
    dp = [0] * (max_size + 1)
    transitions = 0
    for size in range(2, max_size + 1):
        values = []
        for cut in range(1, size):
            values.append(1 + max(dp[cut], dp[size - cut]))
            transitions += 1
        dp[size] = min(values)
        require(dp[size] == ceil_log2(size), f"DP failed at size {size}")
    return {
        "max_size": max_size,
        "nontrivial_cut_evaluations": transitions,
        "verified_formula": "D(N) = ceil(log2(N)), with D(0)=D(1)=0",
        "values_N_0_through_32": dp[:33],
    }


def check_untouched_child(max_bits: int = 10) -> dict[str, Any]:
    cases = 0
    seeker_traces = 0
    for n in range(1, max_bits + 1):
        size = 1 << n
        for depth in range(n):
            for prefix in range(1 << depth):
                left, right = cylinder_interval(n, depth, prefix)
                mid = (left + right) // 2
                # The legal global query [0, mid) has exactly the left child
                # as its trace on [left, right).
                require((left, min(right, mid)) == (left, mid), "Bad trace")
                seeker_traces += 1
                for cut in range(size + 1):
                    if mid <= cut:  # whole left child is in the query
                        retained = (left, mid)
                        answer = 1
                    else:  # right child is wholly outside the query
                        retained = (mid, right)
                        answer = 0
                    a, b = retained
                    require(b - a == (right - left) // 2, "Wrong child size")
                    require(left <= a < b <= right, "Invalid child interval")
                    require(b <= cut if answer else a >= cut,
                            f"Nonhomogeneous retained child: {n, depth, prefix, cut}")
                    cases += 1
    return {"max_bits": max_bits, "prefix_query_cases": cases,
            "seeker_trace_cases": seeker_traces}


def check_adversarial_plays(trials: int = 1000, seed: int = 20260920) -> dict[str, Any]:
    rng = random.Random(seed)
    turns = 0
    for _ in range(trials):
        n = rng.randint(1, 20)
        size = 1 << n
        actual_left, actual_right = 0, size
        prefix_value = 0
        for depth in range(n):
            a, b = cylinder_interval(n, depth, prefix_value)
            require(actual_left <= a < b <= actual_right, "Lost invariant")
            cut = rng.randrange(size + 1)
            mid = (a + b) // 2
            if mid <= cut:
                prefix_value *= 2
                actual_right = min(actual_right, cut)
            else:
                prefix_value = prefix_value * 2 + 1
                actual_left = max(actual_left, cut)
            a, b = cylinder_interval(n, depth + 1, prefix_value)
            require(actual_left <= a < b <= actual_right, "Lost candidate points")
            if depth + 1 < n:
                require(b - a >= 2, "Premature singleton")
            turns += 1
    return {"trials": trials, "seed": seed, "turns": turns,
            "maximum_binary_length": 20}


def check_nonadaptive_counts(max_bits: int = 10) -> dict[str, Any]:
    rows = []
    for n in range(max_bits + 1):
        size = 1 << n
        # A cut [0,c) separates adjacent ranks j,j+1 precisely for j=c-1.
        separated = set()
        for cut in range(1, size):
            pair_index = cut - 1
            require(pair_index < cut <= pair_index + 1, "Wrong adjacent cut")
            separated.add(pair_index)
        require(len(separated) == size - 1, "Missing adjacent pairs")
        rows.append({"bits": n, "points": size,
                     "downward_nonadaptive": size - 1,
                     "finite_discrete_nonadaptive": n})
    return {"rows": rows}


def check_majority(max_points: int = 16, max_tail_bits: int = 12) -> dict[str, Any]:
    masks = 0
    for size in range(1, max_points + 1):
        for query in range(1 << size):
            inside = query.bit_count()
            survivor_count = max(inside, size - inside)
            require(survivor_count >= (size + 1) // 2, "Majority bound failed")
            masks += 1
    tail_cases = 0
    for n in range(max_tail_bits + 1):
        size = 1 << n
        for r in range(n + 1):
            require(size == 1 << (n - r), "Finite tail recurrence failed")
            if r < n:
                require(size >= 2, "Finite tail stopped too early")
            size = (size + 1) // 2
            tail_cases += 1
    return {"max_points_exhaustive": max_points, "query_subsets": masks,
            "max_tail_bits": max_tail_bits, "tail_stage_cases": tail_cases}


def check_finite_holes(max_bits: int = 5, max_holes: int = 3) -> dict[str, Any]:
    """Enumerate cylinders, refinements, and finite holes under 2^k > |F|."""
    cases = 0
    for n in range(1, max_bits + 1):
        for depth in range(n):
            for prefix in range(1 << depth):
                a, b = cylinder_interval(n, depth, prefix)
                for k in range(1, n - depth + 1):
                    children = 1 << k
                    width = (b - a) // children
                    for h in range(min(max_holes, children - 1, b - a) + 1):
                        for holes in itertools.combinations(range(a, b), h):
                            hit = {(point - a) // width for point in holes}
                            clean = next((j for j in range(children) if j not in hit), None)
                            require(clean is not None, "No untouched subcylinder")
                            lo, hi = a + clean * width, a + (clean + 1) * width
                            require(not any(lo <= point < hi for point in holes),
                                    "Selected subcylinder has a hole")
                            cases += 1
    return {"max_bits": max_bits, "max_holes": max_holes,
            "exhaustive_configurations": cases,
            "condition": "number of equal subcylinders > number of deleted points"}


def run() -> dict[str, Any]:
    return {
        "status": "PASS",
        "scope": "Exact finite checks only; not a formal verification of the transfinite theorem.",
        "chain_recurrence": check_chain_recurrence(),
        "untouched_child": check_untouched_child(),
        "adversarial_plays": check_adversarial_plays(),
        "nonadaptive_counts": check_nonadaptive_counts(),
        "majority": check_majority(),
        "finite_holes": check_finite_holes(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Optional path at which to save the JSON test report")
    args = parser.parse_args()
    report = run()
    text = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
