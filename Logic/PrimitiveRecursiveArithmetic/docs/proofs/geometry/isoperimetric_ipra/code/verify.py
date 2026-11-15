#!/usr/bin/env python3
"""Reproducible exact checks; these are diagnostics, not formal proof."""

import json
import random
import sys
from pathlib import Path
from fractions import Fraction as Q

from finite_core import (
    polygon, pi_lower, dyadic, sqrt_down, signed_area, upper_lengths,
    edges, norm_sq_edge, check_instance, refined_polygon,
    machin_pi_interval, fraction_json
)


def main():
    pi_lo, pi_hi = machin_pi_interval(32)
    pi_records = []
    for k in range(25):
        lo = pi_lower(k)
        hi = lo + dyadic(k)
        assert lo <= pi_lo and pi_hi <= hi
        pi_records.append({"k": k, "lower": fraction_json(lo),
                           "error_bound": fraction_json(dyadic(k))})

    sqrt_cases = 0
    for a in range(30):
        for b in range(1, 10):
            for t in range(8):
                x = Q(a, b)
                y = sqrt_down(x, t)
                assert y*y <= x < (y + dyadic(t))**2
                sqrt_cases += 1

    cases = [
        ("point", [(0, 0)]),
        ("zero_edges", [(3, -2)] * 5),
        ("segment_and_back", [(0, 0), (3, 4)]),
        ("unit_square", [(0, 0), (1, 0), (1, 1), (0, 1)]),
        ("345_triangle", [(0, 0), (3, 0), (0, 4)]),
        ("bow_tie", [(0, 0), (2, 2), (0, 2), (2, 0)]),
        ("repeated_vertices", [(0, 0), (1, 0), (1, 0), (0, 1)]),
        ("clockwise_square", [(0, 0), (0, 1), (1, 1), (1, 0)]),
        ("large_translation", [(10**30, -10**30), (10**30+1, -10**30),
                               (10**30+1, -10**30+1),
                               (10**30, -10**30+1)]),
    ]
    rng = random.Random(20261114)
    for i in range(160):
        m = rng.randrange(1, 10)
        vertices = [(Q(rng.randrange(-12, 13), rng.randrange(1, 7)),
                     Q(rng.randrange(-12, 13), rng.randrange(1, 7)))
                    for _ in range(m)]
        cases.append(("rational_%03d" % i, vertices))

    count = 0
    max_mesh = 0
    for name, raw in cases:
        p = polygon(raw)
        u = upper_lengths(p, 16)
        for k in (0, 1, 2, 4, 8):
            witness, _, _ = check_instance(p, u, k)
            count += 1
            max_mesh = max(max_mesh, witness.get("N", 0))

    # Check the actual expanded shoelace/energy identities, including padding.
    expanded = []
    for name, raw in cases[2:8]:
        p = polygon(raw)
        u = upper_lengths(p, 10)
        witness, left, right = check_instance(p, u, 0)
        q = refined_polygon(p, witness, cap=100000)
        assert signed_area(q) == signed_area(p)
        actual_energy = sum((norm_sq_edge(a, b) for a, b in edges(q)), Q(0))
        assert actual_energy == witness["energy"]
        expanded.append({"case": name, "vertices": len(q),
                         "padding": witness["repeated_vertices"]})

    result = {
        "status": "passed",
        "arithmetic": "Python arbitrary-precision integers and fractions only",
        "logical_status": (
            "Finite-instance and implementation checks, not a machine-checked "
            "universal theorem and not an iPRA derivation."
        ),
        "pi_interval_checks": len(pi_records),
        "sqrt_interval_checks": sqrt_cases,
        "polygon_instances": count,
        "expanded_refinements": expanded,
        "largest_symbolic_refinement": max_mesh,
        "pi_enclosures": pi_records,
        "lean_status": "uncompiled blueprint; Lean/Lake unavailable in this environment",
    }
    target = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(
        __file__).resolve().parents[1] / "verification" / "exact_checks.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "pi_enclosures"},
                     indent=2))


if __name__ == "__main__":
    main()
