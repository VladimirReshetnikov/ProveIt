#!/usr/bin/env python3
"""Independent exhaustive finite checks for high_moment_packing.py.

Usage: python3 verify_high_moment_packing.py --output packing_verification.json

The independent oracle enumerates all vertex labelings and evaluates loads
directly.  It does not use the ordered-edge-tuple moment expansion.  The tests
also check edge-coloring matchings, exact second-moment formulas, and potential
nonincrease for every label assigned by the construction.  They establish
finite algebraic implementation checks, not the asymptotic theorem.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from itertools import product
from pathlib import Path

from high_moment_packing import (
    conditional_potential, degrees, deterministic_pack, loads,
    matching_partition, potential_from_loads, proved_potential_bound,
    second_moment_formula, vertices,
)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def direct_average(edges, r, k, fixed):
    """Independent expectation over complete labelings extending fixed."""
    free = [vertex for vertex in vertices(edges) if vertex not in fixed]
    total = Fraction(0)
    cases = 0
    for labels_tuple in product(range(r), repeat=len(free)):
        assignment = dict(fixed)
        assignment.update(zip(free, labels_tuple))
        total += potential_from_loads(loads(edges, r, assignment), len(edges), r, k)
        cases += 1
    return total / cases, cases


def fraction_json(value):
    return {"numerator": value.numerator, "denominator": value.denominator}


def verify_case(name, edges, r, k):
    nodes = vertices(edges)
    partition = matching_partition(edges)
    require(sorted(index for block in partition for index in block)
            == list(range(len(edges))), name + ": coloring omitted or duplicated an edge")
    for block in partition:
        left = [edges[index][0] for index in block]
        right = [edges[index][1] for index in block]
        require(len(left) == len(set(left)) and len(right) == len(set(right)),
                name + ": a color class is not a matching")
    delta = max(degrees(edges).values(), default=0)
    require(not edges or len(partition) <= 2 * delta - 1,
            name + ": too many matching classes")

    exact, enumerated = direct_average(edges, r, k, {})
    expanded = conditional_potential(edges, r, k, {})
    require(exact == expanded, name + ": unconditional moments disagree")
    bound = proved_potential_bound(edges, r, k)
    require(exact <= bound, name + ": proved moment bound violated")

    variance_direct, variance_cases = direct_average(edges, r, 1, {})
    require(variance_direct == second_moment_formula(edges, r),
            name + ": exact edge-pair variance formula failed")

    # Exhaust every assignment to the first at most two vertices.  This checks
    # genuine conditional distributions, including impossible edge-label events.
    prefix = nodes[:min(2, len(nodes))]
    conditional_checks = 0
    conditional_labelings = 0
    for labels_tuple in product(range(r), repeat=len(prefix)):
        fixed = dict(zip(prefix, labels_tuple))
        direct, cases = direct_average(edges, r, k, fixed)
        formula = conditional_potential(edges, r, k, fixed)
        require(direct == formula, name + ": conditional moments disagree")
        conditional_checks += 1
        conditional_labelings += cases

    packed = deterministic_pack(edges, r, k)
    require(packed["initial_potential"] == exact,
            name + ": construction began at the wrong expectation")
    require(packed["final_potential"] <= exact,
            name + ": construction exceeded its initial expectation")
    for step in packed["trace"]:
        require(sum(step["alternatives"], Fraction(0)) / r == step["before"],
                name + ": averaging identity failed in recorded trace")
        require(step["after"] <= step["before"],
                name + ": potential increased in recorded trace")
    mu = Fraction(len(edges), r * r)
    maximum_moment = max((abs(Fraction(value) - mu) ** (2 * k)
                          for value in packed["loads"]), default=Fraction(0))
    require(maximum_moment <= exact <= bound,
            name + ": final uniform-load consequence failed")

    return {"name": name, "edges": edges, "label_count": r,
            "moment_half": k, "vertices": len(nodes), "maximum_degree": delta,
            "matching_classes": len(partition), "root_labelings": enumerated,
            "variance_labelings": variance_cases,
            "conditional_checks": conditional_checks,
            "conditional_labelings": conditional_labelings,
            "labels_assigned": len(packed["trace"]),
            "initial_potential": fraction_json(exact),
            "final_potential": fraction_json(packed["final_potential"]),
            "proved_upper_bound": fraction_json(bound),
            "loads": packed["loads"], "status": "PASS"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("packing_verification.json"))
    args = parser.parse_args()
    fixtures = [
        ("empty", [], 2, 2),
        ("single_edge", [(0, 0)], 2, 1),
        ("three_parallel_edges", [(0, 0), (0, 0), (0, 0)], 2, 2),
        ("three_edge_path_sixth_moment", [(0, 0), (1, 0), (1, 1)], 2, 3),
        ("parallel_and_shared_endpoints", [(0, 0), (0, 0), (0, 1), (1, 1), (2, 0)], 2, 2),
        ("complete_2_by_3", [(left, right) for left in range(2) for right in range(3)], 2, 2),
        ("three_label_star", [(0, right) for right in range(4)], 3, 1),
        ("three_label_irregular_multigraph", [(0, 0), (0, 1), (0, 1), (1, 1), (1, 2), (2, 0), (2, 2)], 3, 1),
    ]
    results = [verify_case(*fixture) for fixture in fixtures]
    output = {
        "status": "PASS", "implementation": "exact rational conditional expectation",
        "test_scope": "finite exhaustive algebraic checks; not an asymptotic runtime benchmark",
        "fixture_count": len(results),
        "complete_labelings_for_root_moments": sum(row["root_labelings"] for row in results),
        "conditional_distributions_checked": sum(row["conditional_checks"] for row in results),
        "individual_label_assignments_checked": sum(row["labels_assigned"] for row in results),
        "fixtures": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in output.items() if key != "fixtures"}, indent=2))


if __name__ == "__main__":
    main()
