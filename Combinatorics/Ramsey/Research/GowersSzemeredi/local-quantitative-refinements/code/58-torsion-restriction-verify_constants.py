#!/usr/bin/env python3
"""Exact integer certificates for the all-modulus exponent-54 corollary.

Run: python code/verify_constants.py
Dependencies: Python standard library only.

The kernel cos^(2q)(pi t), with coefficients 4^(-q) binom(2q,q+t), is
already used in source 04, Section 4 (R8--R9), of the consolidated ProveIt
Ramsey report. This script checks the new q=25, m=16 parameter certificate
and the arithmetic needed to obtain the two conclusions with exponent 54.

Integer arithmetic is exact. The final symbolic parameter comparisons use
0 < t=alpha*eta <= 1 and 0 < eta <= 1, as proved in the article; they are
not inferred from numerical sampling.
"""
from fractions import Fraction
from math import comb
from pathlib import Path
import json


def main():
    m, q = 16, 25
    coefficients = {n: comb(2*q, q+n) for n in range(-q, q+1)}
    numerator_p = sum(c**m for c in coefficients.values())
    numerator_q = sum(c**m for n, c in coefficients.items() if n % 2 == 0)
    denominator = 4**(q*m)
    moment2_numerator = comb(4*q, 2*q)
    moment2_denominator = 4**(2*q)

    checks = {
        "P_ge_2_to_minus_50": numerator_p >= 2**750,
        "P_over_Q_ge_481_over_250": 250*numerator_p >= 481*numerator_q,
        "ratio_to_power_53_ge_2_to_50": 481**53 >= 2**50 * 250**53,
        "ratio_to_power_50_ge_2_to_47": 481**50 >= 2**47 * 250**50,
        "R2_le_2_to_minus_3": moment2_numerator <= 2**97,
        "denominator_is_2_to_800": denominator == 2**800,
        "R2_denominator_is_2_to_100": moment2_denominator == 2**100,
    }
    assert all(checks.values())

    torsion_bound = 2*q
    collision_bound = comb(m, 2)
    size_prefactor = 4*(torsion_bound + collision_bound)
    assert (torsion_bound, collision_bound, size_prefactor) == (50, 120, 680)

    # b >= 680*2^97*t^(-51) is implied by b >= 2^108*t^(-54):
    # their ratio is (85/256)*t^3 <= 85/256 < 1.
    size_ratio = Fraction(size_prefactor*2**97, 2**108)
    assert size_ratio == Fraction(85, 256) < 1
    # The certified retained coefficient is 2^(-105)*alpha^54*eta^53.
    # Its ratio to (alpha*eta/4)^54 is 8/eta >= 8.
    retention_ratio_coefficient = Fraction(2**108, 2**105)
    assert retention_ratio_coefficient == 8

    result = {
        "arithmetic": "Python integers and fractions.Fraction only",
        "tuple_order_m": m,
        "cosine_degree_q": q,
        "P_numerator": str(numerator_p),
        "Q2_numerator": str(numerator_q),
        "common_denominator": "2^800",
        "R2_numerator": str(moment2_numerator),
        "R2_denominator": "2^100",
        "checks": checks,
        "all_checks_passed": all(checks.values()),
        "cyclic_torsion_upper_bound": torsion_bound,
        "collision_pair_upper_bound": collision_bound,
        "sufficient_size_coefficient": size_prefactor,
        "size_comparison": {
            "domain": "0 < t=alpha*eta <= 1",
            "sufficient_bound": "680 * 2^97 * t^(-51)",
            "stated_bound": "(4/t)^54 = 2^108 * t^(-54)",
            "ratio_sufficient_to_stated": "(85/256) * t^3",
            "ratio_upper_bound": str(size_ratio)
        },
        "retention_comparison": {
            "domain": "0 < alpha <= 1 and 0 < eta <= 1",
            "certified_bound": "2^(-105) * alpha^54 * eta^53",
            "stated_bound": "(alpha*eta/4)^54",
            "ratio_certified_to_stated": "8/eta >= 8"
        },
        "scope": "Exact arithmetic certificates plus symbolic comparisons justified in the article; no general theorem is established by finite sampling.",
        "generated_by": "code/verify_constants.py"
    }
    path = Path(__file__).resolve().parents[1] / "data" / "exact_constants.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
