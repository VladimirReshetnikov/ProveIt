#!/usr/bin/env python3
"""Exact enumeration for the narrowly specified binomial reporter family.

The leaf tests are nonempty proper unions of complete sum levels of n
uniform signs.  Test families are unordered and have distinct members;
selectors onto those members are surjective.  The accompanying mathematical
proof explains why empty/full, duplicate, and unused tests cannot supply a
smaller positive reporter.  This program does not enumerate arbitrary
Boolean-cube observations or tests that split a sum level.

Every comparison is made with fractions.Fraction.  No numerical optimizer,
random search, floating-point rounding, or unproved pruning is used.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from itertools import combinations, product
from math import comb, prod
from pathlib import Path


F = Fraction
CASES = ((4, 2), (4, 3), (5, 2), (6, 2))
EXPECTED = {
    (4, 2): (13050, F(-1, 12)),
    (4, 3): (609000, F(-35, 17152)),
    (5, 2): (117242, F(-595, 8576)),
    (6, 2): (992250, F(-1293, 33152)),
}


def leaf_events(n: int) -> tuple[tuple[int, ...], tuple[F, ...], list[dict]]:
    values = tuple(2 * j - n for j in range(n + 1))
    probabilities = tuple(F(comb(n, j), 1 << n) for j in range(n + 1))
    events = []
    for mask in range(1, (1 << (n + 1)) - 1):
        indices = tuple(j for j in range(n + 1) if (mask >> j) & 1)
        probability = sum(probabilities[j] for j in indices)
        mean = sum(probabilities[j] * values[j] for j in indices) / probability
        variance = sum(probabilities[j] * (values[j] - mean) ** 2 for j in indices) / probability
        weights = tuple(probability_j / probability for probability_j in probabilities)
        # Combine H_2 minus the selected-variance term before enumeration.
        first_terms = tuple(weight * (value - mean) for weight, value in zip(weights, values))
        second_terms = tuple(
            weight * ((value - mean) ** 2 - variance)
            for weight, value in zip(weights, values)
        )
        events.append({
            "mask": mask,
            "values": tuple(values[j] for j in indices),
            "probability": probability,
            "mean": mean,
            "variance": variance,
            "weights": weights,
            "first_terms": first_terms,
            "second_terms": second_terms,
        })
    return values, probabilities, events


def enumerate_case(n: int, m: int) -> dict:
    """Enumerate every reduced configuration for one n,m pair."""
    values, probabilities, events = leaf_events(n)
    selectors = tuple(
        selector
        for selector in product(range(m), repeat=n + 1)
        if len(set(selector)) == m
    )
    examined = 0
    positive = 0
    best_gap = None
    best_parameters = None
    for family_indices in combinations(range(len(events)), m):
        family = tuple(events[i] for i in family_indices)
        q = prod(event["probability"] for event in family)
        variance_sum = sum(event["variance"] for event in family)
        for selector in selectors:
            r0 = sum(family[i]["weights"][j] for j, i in enumerate(selector))
            r1 = sum(family[i]["first_terms"][j] for j, i in enumerate(selector))
            h2_minus_selected_variance = sum(
                family[i]["second_terms"][j] for j, i in enumerate(selector)
            )
            kappa = r0 - 1
            assert kappa > 0
            gap = q * (r1 * r1 / kappa - h2_minus_selected_variance - kappa * variance_sum)
            examined += 1
            positive += gap > 0
            if best_gap is None or gap > best_gap:
                best_gap = gap
                best_parameters = {
                    "event_masks": [event["mask"] for event in family],
                    "events": [event["values"] for event in family],
                    "event_probabilities": [str(event["probability"]) for event in family],
                    "event_means": [str(event["mean"]) for event in family],
                    "event_variances": [str(event["variance"]) for event in family],
                    "selector_leaf_indices": selector,
                    "Q": str(q),
                    "K": str(kappa),
                    "R1": str(r1),
                    "S": str(variance_sum),
                    "H2_minus_selected_variance": str(h2_minus_selected_variance),
                    "optimal_predictor": str(sum(event["mean"] for event in family) + r1 / kappa),
                }
    assert best_gap is not None
    assert examined == comb(len(events), m) * len(selectors)
    if (n, m) in EXPECTED:
        expected_count, expected_gap = EXPECTED[n, m]
        assert examined == expected_count
        assert best_gap == expected_gap
        assert positive == 0
    return {
        "block_size": n,
        "leaves": m,
        "total_bits": n * (m + 1),
        "degree_cap": n * m,
        "sum_values": values,
        "sum_probabilities": [str(probability) for probability in probabilities],
        "nonempty_proper_leaf_tests": len(events),
        "distinct_unordered_test_families": comb(len(events), m),
        "surjective_selectors_per_family": len(selectors),
        "exact_configurations": examined,
        "positive_configurations": positive,
        "maximum_advantage": str(best_gap),
        "one_maximizer": best_parameters,
    }


def enumerate_all() -> dict:
    results = []
    for n, m in CASES:
        result = enumerate_case(n, m)
        results.append(result)
        print(
            f"PASS n={n}, m={m}: {result['exact_configurations']:,} configurations; "
            f"maximum advantage {result['maximum_advantage']}; no positive case.",
            flush=True,
        )
    total = sum(result["exact_configurations"] for result in results)
    assert total == 1731542
    return {
        "description": "Exact minimality certificate for binomial sum-level reporters below twenty bits",
        "scope": "iid unweighted n-bit sums; leaf tests are unions of complete sum levels; refined reporter",
        "arithmetic": "fractions.Fraction throughout",
        "reductions": [
            "empty and full tests cannot have a positive advantage",
            "unused leaves and duplicate tests can be deleted from a positive reporter",
            "a minimum reporter has distinct tests and a surjective selector",
            "one-leaf reporters cannot beat their degree cap",
            "block sizes at most three are excluded by the codimension theorem",
        ],
        "cases": results,
        "total_exact_configurations": total,
        "positive_configurations": 0,
        "all_assertions_passed": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--block-size", type=int, help="enumerate one block size instead of all four cases")
    parser.add_argument("--leaves", type=int, help="leaf count for one case")
    parser.add_argument("--output", type=Path, help="JSON output path")
    args = parser.parse_args()
    if (args.block_size is None) != (args.leaves is None):
        parser.error("--block-size and --leaves must be provided together")
    result = enumerate_all() if args.block_size is None else enumerate_case(args.block_size, args.leaves)
    if args.output is None:
        print(json.dumps(result, indent=2))
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
        print(f"Certificate: {args.output}")


if __name__ == "__main__":
    main()
