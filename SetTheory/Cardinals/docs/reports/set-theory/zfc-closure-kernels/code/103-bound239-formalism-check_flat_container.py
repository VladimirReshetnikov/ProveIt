#!/usr/bin/env python3
"""Finite regression of the arithmetic CP-flat witnesses in theory_filters.tex.

This tests exact bit identities, not all GIC formulas or consistency.
Only standard-library Python is required. No input or output file is modified.
"""

import argparse
import json


def members(value):
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value ^= low


def submasks(value):
    part = value
    while True:
        yield part
        if part == 0:
            return
        part = (part - 1) & value


def check(limit):
    assert isinstance(limit, int) and limit >= 0
    root_cases = transitive_edges = subset_cases = rejected_bounds = 0
    for root in range(limit + 1):
        container = (1 << (root + 1)) - 1
        assert tuple(members(container)) == tuple(range(root + 1))
        assert (container >> root) & 1
        root_cases += 1
        for x in members(container):
            for u in members(x):
                assert u < x <= root
                assert (container >> u) & 1
                transitive_edges += 1
            for subset in submasks(x):
                assert subset & ~x == 0
                assert subset <= x <= root
                assert (container >> subset) & 1
                subset_cases += 1
        # x = root is a member of the chosen container. Any old CP power
        # bound W must contain x because x is a subset of itself.
        for bound in members(container):
            assert bound <= root < (1 << root)
            assert ((bound >> root) & 1) == 0
            rejected_bounds += 1
    return {
        "status": "PASS",
        "root_range_inclusive": [0, limit],
        "root_witnesses": root_cases,
        "transitivity_edges": transitive_edges,
        "subset_membership_cases": subset_cases,
        "rejected_original_CP_bounds_for_root_member": rejected_bounds,
        "scope": "Exact finite Ackermann-code identities only; no model or consistency proof is inferred from this finite run.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-root", type=int, default=255)
    args = parser.parse_args()
    if args.max_root < 0:
        parser.error("--max-root must be nonnegative")
    print(json.dumps(check(args.max_root), indent=2))
