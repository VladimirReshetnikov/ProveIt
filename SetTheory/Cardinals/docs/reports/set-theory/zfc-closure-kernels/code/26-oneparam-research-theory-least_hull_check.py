#!/usr/bin/env python3
"""Exhaustive finite check of least positive hull identities.

This tests ordinary directed-graph identities, not models of EPSC or a TM.
No external packages are required. Run with Python assertions enabled.
"""

import argparse
import json
from pathlib import Path


def images(n, graph):
    """Return image[X] for each vertex subset X, encoded as a bit mask."""
    rows = [(graph >> (n * x)) & ((1 << n) - 1) for x in range(n)]
    result = [0] * (1 << n)
    for mask in range(1, 1 << n):
        low = mask & -mask
        x = low.bit_length() - 1
        result[mask] = result[mask ^ low] | rows[x]
    return result


def positive_hull(image, seed):
    current = 0
    while True:
        following = image[seed | current]
        if following == current:
            return current
        assert current & ~following == 0
        current = following


def verify(max_vertices):
    counts = {
        "graph_seed_cases": 0,
        "prefixed_candidate_checks": 0,
        "invariant_checks": 0,
        "edge_monotonicity_checks": 0,
    }
    for n in range(1, max_vertices + 1):
        full = (1 << n) - 1
        for graph in range(1 << (n * n)):
            image = images(n, graph)
            range_r = image[full]
            for seed in range(1 << n):
                counts["graph_seed_cases"] += 1
                least = full
                least_supported = full
                prefixed_count = 0
                supported_count = 0
                for candidate in range(1 << n):
                    counts["prefixed_candidate_checks"] += 1
                    if image[seed | candidate] & ~candidate == 0:
                        prefixed_count += 1
                        least &= candidate
                        if candidate & ~range_r == 0:
                            supported_count += 1
                            least_supported &= candidate
                assert prefixed_count > 0
                assert supported_count > 0
                reach = positive_hull(image, seed)
                assert least == least_supported == reach
                assert image[seed | least] == least
                assert least & ~range_r == 0

                for invariant in range(1 << n):
                    counts["invariant_checks"] += 1
                    if (image[seed] | image[invariant]) & ~invariant == 0:
                        assert least & ~invariant == 0

                for edge in range(n * n):
                    counts["edge_monotonicity_checks"] += 1
                    bigger_image = images(n, graph | (1 << edge))
                    assert least & ~positive_hull(bigger_image, seed) == 0

    # Seed 0 emits 1; vertex 2 is a disconnected self-loop. The supported
    # fixed point {1,2} exists, but the least positive hull is exactly {1}.
    image = images(3, (1 << 1) | (1 << 8))
    assert positive_hull(image, 1) == 2
    assert image[1 | 6] == 6

    # Positive hulls need not include seeds with no incoming transition.
    assert positive_hull(images(1, 0), 1) == 0

    # A one-object reflexive raw structure has no empty input. Every possible
    # R has a least represented pre-fixpoint, but false R has no supported hull.
    raw_object_members = 1
    raw_empty_inputs = 0
    for graph in (0, 1):
        image = images(1, graph)
        assert image[raw_empty_inputs | raw_object_members] & ~raw_object_members == 0
    assert raw_object_members & ~images(1, 0)[1] != 0

    return {
        "status": "PASS",
        "max_vertices": max_vertices,
        "counts": counts,
        "all_graphs_all_seed_sets": True,
        "claims_tested": [
            "intersection_of_all_prefixed_points_equals_positive_reachability",
            "intersection_of_supported_prefixed_points_has_same_least_hull",
            "least_hull_is_an_active_support_fixed_point",
            "inductive_invariants_contain_least_hull",
            "adding_an_edge_cannot_shrink_least_hull",
        ],
        "scope": "Finite directed-graph semantic tests only; no EPSC model or TM certification.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-vertices", type=int, default=3)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run without -O: assertions implement the checks")
    if not 1 <= args.max_vertices <= 4:
        raise ValueError("Use 1 through 4 vertices; 3 is the default exhaustive run")
    result = verify(args.max_vertices)
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
