#!/usr/bin/env python3
"""Exact finite upper-branch construction and its previously run checks.

All calculations use fractions.Fraction.  The tests exercise the explicit
finite sampler from the report.  They are reference computations, not a
formal proof or an iPRA proof checker.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
import json
from pathlib import Path


def dyadic(p: int) -> Q:
    assert p >= 0
    return Q(1, 2**p)


def sqrt_midpoint(radicand: Q, p: int) -> Q:
    """Use exactly p+4 rational bisections of [2,4], then its midpoint."""
    assert p >= 0 and 6 <= radicand <= 10
    lower, upper = Q(2), Q(4)
    for _ in range(p + 4):
        midpoint = (lower + upper) / 2
        if midpoint * midpoint <= radicand:
            lower = midpoint
        else:
            upper = midpoint
    midpoint = (lower + upper) / 2
    assert abs(midpoint * midpoint - radicand) <= dyadic(p + 1)
    return midpoint


def upper_action(i: int, z: Q, p: int) -> Q:
    """E_i(z,p) from the rational bisection contract in the report."""
    assert i >= 0 and 6 <= z <= 8
    radicand = 16 - z - Q(2, i + 1)
    return 4 + sqrt_midpoint(radicand, p)


def upper_coordinate(i: int, k: int) -> Q:
    """Y(i,k), computed by k+3 backward applications with work p=k+4."""
    assert i >= 0 and k >= 0
    horizon = i + k + 3
    precision = k + 4
    z = Q(7)
    for j in range(horizon - 1, i - 1, -1):
        z = upper_action(j, z, precision)
    return z


def verify() -> dict:
    """Repeat the same 1,200 comparisons and 120 residuals already checked."""
    comparisons = 0
    residuals = 0
    samples = []
    for i in range(12):
        for k in range(10):
            y = upper_coordinate(i, k)
            assert 6 <= y <= 8
            residual = abs(
                y - Q(1, 4 * (i + 1)) - y * y / 8
                - upper_coordinate(i + 1, k) / 8
            )
            residual_bound = dyadic(k + 6)
            assert residual <= residual_bound
            residuals += 1
            for ell in range(10):
                assert abs(y - upper_coordinate(i, ell)) <= dyadic(min(k, ell) + 2)
                comparisons += 1
            samples.append({
                "coordinate": i,
                "precision": k,
                "value": str(y),
                "equation_residual": str(residual),
                "residual_bound": str(residual_bound),
                "horizon": i + k + 3,
                "work_precision": k + 4,
                "backward_applications": k + 3,
                "bisections_per_application": k + 8,
            })

    return {
        "status": "all exact finite checks passed",
        "logical_status": "reference computation, not a formal or iPRA proof checker",
        "regular_name_comparisons": comparisons,
        "equation_residual_checks": residuals,
        "coordinate_indices": {"first": 0, "last": 11},
        "precision_indices": {"first": 0, "last": 9},
        "sample_at_i0_k8": str(upper_coordinate(0, 8)),
        "samples": samples,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).with_name("upper_branch_checks.json"),
        help="Destination for the exact JSON record.",
    )
    args = parser.parse_args()
    result = verify()
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"])
    print(f"{result['regular_name_comparisons']} regular-name comparisons; "
          f"{result['equation_residual_checks']} equation residuals.")
    print(f"Exact record: {args.output}")
