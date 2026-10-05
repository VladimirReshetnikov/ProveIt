#!/usr/bin/env python3
"""Deterministic finite checks for the Fabius uniform-factor Hall theorem.

Run from the package root::

    python code/verify_hall.py --output data/hall_verification.json

Without --output, the receipt is written to ../data/hall_verification.json
relative to this script's directory. All diameter calculations use exact
fractions. The small independent matching check searches all possible used-
source subsets reached by allowed injections; it does not use the greedy
matching or prefix inequalities. Larger cases enumerate every deletion set.

These checks corroborate finite instances of the written theorem. They do
not prove the arbitrary-size Hall theorem, infinite convolutions, positivity
of a density, parameter derivatives, or the sharp Wasserstein contact law.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations_with_replacement
import json
from pathlib import Path


ARTIFACT_MARKER = "fabius-factor-contact:hall-verification:v1"


def ensure(condition: bool, message: str) -> None:
    """Keep the verification active even when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def greedy_matching(targets: tuple[int, ...], available: list[int]):
    """Match sorted targets to the smallest available source levels."""
    if len(available) < len(targets):
        return None
    matching = available[: len(targets)]
    if all(k <= d for k, d in zip(matching, targets)):
        return matching
    return None


def exhaustive_injection_exists(targets: tuple[int, ...], available: list[int]):
    """Independent exhaustive feasibility search over possible injections."""
    used_states = {0}
    for d in targets:
        next_states = set()
        for used in used_states:
            for k in available:
                bit = 1 << k
                if k <= d and not (used & bit):
                    next_states.add(used | bit)
        used_states = next_states
        if not used_states:
            return False
    return bool(used_states)


def prefix_feasible(targets: tuple[int, ...], available: list[int]) -> bool:
    return all(
        sum(k <= d for k in available) >= i + 1
        for i, d in enumerate(targets)
    )


def hall_exponent(targets: tuple[int, ...]) -> int:
    """For at least two targets; Python index i is article index i+1."""
    return min(d + 1 - i for i, d in enumerate(targets) if i >= 1)


def run(max_level: int, brute_max_level: int, bases: tuple[int, ...]) -> dict:
    stats = {
        "all_profiles": 0,
        "unmodified_exhaustive_injection_cases": 0,
        "factorable_profiles_with_at_least_two_targets": 0,
        "deletion_cases": 0,
        "deletion_exhaustive_injection_cases": 0,
        "critical_prefix_checks": 0,
        "one_target_prefix_checks": 0,
        "positive_profiles": 0,
        "exact_diameter_checks": 0,
    }
    per_level = []

    for N in range(max_level + 1):
        before = stats.copy()
        full = list(range(N + 1))
        # Include singleton profiles and profiles with one target too many.
        for s in range(1, N + 3):
            for targets in combinations_with_replacement(range(N + 1), s):
                if targets[-1] != N:
                    continue
                stats["all_profiles"] += 1
                expected = all(d >= i for i, d in enumerate(targets))
                matched = greedy_matching(targets, full) is not None
                context = f"N={N}, targets={targets}"
                ensure(matched == expected, f"unmodified Hall: {context}")
                ensure(
                    prefix_feasible(targets, full) == expected,
                    f"unmodified prefixes: {context}",
                )
                if N <= brute_max_level:
                    ensure(
                        exhaustive_injection_exists(targets, full) == expected,
                        f"independent unmodified injection search: {context}",
                    )
                    stats["unmodified_exhaustive_injection_cases"] += 1

                if not expected or s < 2:
                    continue
                stats["factorable_profiles_with_at_least_two_targets"] += 1
                e = hall_exponent(targets)
                ensure(1 <= e <= N, f"exponent range: {context}")
                n = N + 1 - s
                ensure(n >= e - 1, f"remaining-factor count: {context}")

                minimum_failure = N + 1
                for deletion_mask in range(1 << N):
                    # Bit k-1 deletes moving source k; source 0 stays fixed.
                    available = [0] + [
                        k for k in range(1, N + 1)
                        if not (deletion_mask >> (k - 1) & 1)
                    ]
                    actual = greedy_matching(targets, available) is not None
                    prefixes = prefix_feasible(targets, available)
                    ensure(actual == prefixes, f"deleted Hall: {context}")
                    if not actual:
                        minimum_failure = min(
                            minimum_failure, deletion_mask.bit_count()
                        )
                    stats["deletion_cases"] += 1
                    if N <= brute_max_level:
                        ensure(
                            exhaustive_injection_exists(targets, available)
                            == prefixes,
                            f"independent deleted injection search: {context}",
                        )
                        stats["deletion_exhaustive_injection_cases"] += 1
                ensure(minimum_failure == e, f"minimal deletion: {context}")

                # The first e moving indices are a deterministic failure set.
                critical = min(
                    range(1, s), key=lambda i: targets[i] + 1 - i
                )
                ensure(e <= targets[critical], f"witness fits prefix: {context}")
                witness_available = [0] + list(range(e + 1, N + 1))
                ensure(
                    greedy_matching(targets, witness_available) is None,
                    f"canonical deletion witness: {context}",
                )
                stats["critical_prefix_checks"] += 1

                # m(r)=1 can never create a Hall failure: 0 is still there.
                for r in range(N + 1):
                    m = sum(d <= r for d in targets)
                    if m == 1:
                        surviving = [0] + list(range(r + 1, N + 1))
                        ensure(
                            sum(k <= r for k in surviving) >= m,
                            f"undeletable singleton prefix: {context}",
                        )
                        stats["one_target_prefix_checks"] += 1

                if e < 2:
                    continue
                if targets[0] >= 1:
                    assigned = list(range(1, s + 1))
                    reserved = 0
                else:
                    assigned = [0] + list(range(2, s + 1))
                    reserved = 1
                ensure(len(set(assigned)) == s, f"reserved injection: {context}")
                ensure(
                    all(0 <= k <= N and k <= d for k, d in zip(assigned, targets)),
                    f"reserved allowed edges: {context}",
                )
                ensure(reserved not in assigned, f"reserved source: {context}")
                stats["positive_profiles"] += 1
                for B in bases:
                    widths = [Fraction(1, B**k) for k in range(N + 1)]
                    diameter = sum(
                        (widths[k] - Fraction(1, B**d)
                         for k, d in zip(assigned, targets)),
                        Fraction(),
                    )
                    continuous_width = sum(
                        (w for k, w in enumerate(widths) if k not in assigned),
                        Fraction(),
                    )
                    ensure(
                        0 <= diameter < widths[reserved] <= continuous_width,
                        f"strict exact diameter: B={B}, {context}",
                    )
                    stats["exact_diameter_checks"] += 1

        per_level.append({
            "max_target_level": N,
            **{key: stats[key] - before[key] for key in stats},
        })

    return {
        "artifact_marker": ARTIFACT_MARKER,
        "status": "passed",
        "parameters": {
            "maximum_source_level": max_level,
            "independent_injection_maximum_level": brute_max_level,
            "bases_for_exact_diameter_checks": list(bases),
            "target_sizes_for_level_N": "1 through N+2",
            "source_0_is_undeletable": True,
            "sorted_target_multisets_have_maximum_N": True,
        },
        "counts": stats,
        "counts_by_maximum_target_level": per_level,
        "verified_finite_assertions": [
            "Exact injection criterion d_i >= i-1, including tied targets.",
            "Greedy success is equivalent to every prefix capacity inequality.",
            "Minimum moving-source deletion causing failure equals e.",
            "Deleting moving sources 1 through e is a failure witness.",
            "A prefix with exactly one target retains its source-0 capacity.",
            "The number of residual uniforms is at least e-1.",
            "For e>=2 the deterministic assignment leaves the designated reserve.",
            "Exact digit diameter is strictly less than the reserved width.",
        ],
        "limitations": [
            "Finite corroboration; the arbitrary-size assertions require the written proof.",
            "No numerical approximation is used in a diameter comparison.",
            "Does not verify infinite convolution, analytic jets, or Wasserstein contact.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-level", type=int, default=7)
    parser.add_argument("--brute-max-level", type=int, default=4)
    parser.add_argument("--bases", type=int, nargs="+", default=[2, 3, 4, 5])
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().parent.parent / "data" / "hall_verification.json",
        help="Receipt path; default is ../data/hall_verification.json beside the code folder.",
    )
    args = parser.parse_args()
    if args.max_level < 0 or args.brute_max_level < 0:
        parser.error("Level bounds must be nonnegative.")
    if any(B < 2 for B in args.bases):
        parser.error("Each base must be an integer at least 2.")
    result = run(args.max_level, args.brute_max_level, tuple(args.bases))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "artifact_marker": ARTIFACT_MARKER,
        "status": result["status"],
        "counts": result["counts"],
        "receipt": str(args.output),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
