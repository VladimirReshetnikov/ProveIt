#!/usr/bin/env python3
"""Exact arithmetic supporting the polynomial Appell mesh theorem.

Only Python integers/Fraction are used.  General separation, Riesz
preservation, and zero saturation are analytic theorems in the article.
The finite Laguerre and gamma-moment examples here are formula checks,
not a finite substitute for those all-degree proofs.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from math import comb, factorial, prod
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def ceil_fraction(q):
    return -((-q.numerator) // q.denominator)


def harmonic(n):
    return sum((F(1, j) for j in range(1, n + 1)), F(0))


def apply_factor(coefficients, c):
    """Ascending coefficients of (1+c*d/dx)p, exactly."""
    n = len(coefficients) - 1
    return [coefficients[j] + c * (j + 1) * coefficients[j + 1]
            for j in range(n)] + [coefficients[n]]


def thresholds(n):
    h = harmonic(n - 1)
    old_delta = F(1, (3 * n) ** (n - 2))
    new_delta = F(1, 10 * n * n)
    hybrid_delta = max(old_delta, new_delta)
    old_k = 576 * n * n * (3 * n) ** (2 * n - 4)
    new_square = (16 + 240 * n * n * h) ** 2
    hybrid_square = (16 + 24 * h / hybrid_delta) ** 2
    new_k = ceil_fraction(new_square)
    hybrid_k = ceil_fraction(hybrid_square)
    require(new_k - 1 < new_square <= new_k,
            "New threshold is not the least integer above its square")
    require(hybrid_k - 1 < hybrid_square <= hybrid_k,
            "Hybrid threshold is not the least integer above its square")
    require(F(24 * n, 1) ** 2 / old_delta ** 2 == old_k,
            "Incoming threshold formula disagrees")
    return {
        "n": n, "H_n_minus_1": str(h),
        "incoming_mesh_bound": str(old_delta),
        "polynomial_mesh_bound": str(new_delta),
        "hybrid_mesh_bound": str(hybrid_delta),
        "incoming_threshold": str(old_k),
        "polynomial_threshold": str(new_k),
        "hybrid_threshold": str(hybrid_k),
        "polynomial_threshold_square": str(new_square),
        "hybrid_threshold_square": str(hybrid_square),
    }


def verify():
    # q_max <= 1 is equivalent to this polynomial being positive.
    # At n=u+3: 4*n^2-8*n-6 = 4*u^2+16*u+6.
    shifted = [4 * 9 - 8 * 3 - 6, 4 * 6 - 8, 4]
    require(shifted == [6, 16, 4] and min(shifted) > 0,
            "Laguerre potential comparison failed")
    require(F(7, 4) ** 2 > 3, "sqrt(3) comparison failed")
    remote = F(3, 15) - F(45, 2 * 15 ** 2)
    require(remote == F(1, 10), "Remote block constant failed")
    require(60 * F(1, 60) == 1, "Growing-range constant failed")

    laguerre_examples = []
    for n in range(2, 21):
        p = [F(0)] * n + [F(1)]
        for _ in range(3 * n):
            p = apply_factor(p, F(1))
        reference = [F(factorial(n) * comb(3 * n, n - r), factorial(r))
                     for r in range(n + 1)]
        require(p == reference, f"Laguerre coefficient check failed at n={n}")
        laguerre_examples.append(n)

    moment_examples = []
    for m in (1, 2, 3, 5, 10, 20, 50):
        k = 16 * m * m
        positive = lambda r: prod((1 + F(j, k) for j in range(1, r + 1)),
                                  start=F(1))
        negative = lambda r: prod((1 / (1 - F(j, k)) for j in range(r)),
                                  start=F(1))
        pm, nm = positive(m), negative(m)
        p2m, n2m = positive(2 * m), negative(2 * m)
        upper_square = p2m + n2m - 2 * pm - 2 * nm + 2
        require(pm >= 1 and nm >= 1, "Moment positivity failed")
        require(p2m <= F(4, 3) and n2m <= F(4, 3),
                "Finite moment upper bound failed")
        require(0 <= upper_square <= F(2, 3),
                "Finite logarithmic-moment comparison failed")
        moment_examples.append({"m": m, "k": k,
                                "Cauchy_Schwarz_upper_square": str(upper_square)})

    return {
        "arithmetic": "Python standard-library integers and fractions.Fraction",
        "status": "All exact arithmetic checks passed",
        "scope": ("Exact constants and integer ceilings, plus explicitly finite "
                  "Laguerre/gamma-moment examples. The all-degree mesh and zero "
                  "theorems are proved analytically in Section 4."),
        "universal_algebraic_checks": {
            "potential_denominator_minus_numerator_at_n_equals_u_plus_3":
                shifted,
            "remote_block_gap_times_n_squared": str(remote),
            "sqrt3_upper_bound": "7/4",
            "growing_range_boundary_alpha_squared": "1/60",
        },
        "finite_Laguerre_coefficient_check_indices": laguerre_examples,
        "finite_gamma_moment_checks": moment_examples,
        "thresholds": [thresholds(n) for n in range(2, 61)],
        "source_of_incoming_bound": (
            "proveit_polylogarithms_research_2026-10-10 (1).zip/"
            "polylogarithms_uniform_continuation/sections/04_lerch.tex"),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true",
                        help="Regenerate instead of comparing the shipped data.")
    args = parser.parse_args()
    record = verify()
    path = BASE / "data" / "mesh_arithmetic_certificate.json"
    if args.write:
        path.write_text(json.dumps(record, indent=2) + "\n")
    else:
        require(json.loads(path.read_text()) == record,
                "Shipped mesh arithmetic record does not match the replay")
    print("Exact mesh arithmetic and 59 integer thresholds verified.")


if __name__ == "__main__":
    main()
