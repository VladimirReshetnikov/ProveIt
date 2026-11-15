#!/usr/bin/env python3
"""Exact integer bounds for the regular-height construction in the paper.

This calculates the proof's a priori resource bounds.  It does not run the
astronomically large search, evaluate zeta, certify a zero, or verify Lean.
Only Python's standard library and exact integer/rational arithmetic are used.
"""
from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction


def ceil_fraction(x: Fraction) -> int:
    return -(-x.numerator // x.denominator)


def ceil_log2_integer(n: int) -> int:
    assert n >= 1
    return (n - 1).bit_length()


def bounds(T: Fraction) -> dict[str, object]:
    if T < 8:
        raise ValueError("The theorem requires T >= 8.")
    A = ceil_fraction(T)
    M = 4 * (A + 10) ** 4
    k = ceil_log2_integer(16 * M)
    Q = 4 * k
    L_den = 2 ** 83 * M ** 20 * (18 * (Q + 2)) ** Q
    J = 12 * M * L_den
    M5 = 8 * (A + 14) ** 6
    b = ceil_log2_integer(M5)
    p = ceil_log2_integer(4 * L_den)
    D = 5 * (p + b + 4)
    p_eval = ceil_log2_integer(16 * L_den)
    # A uniform bound for all candidate U in (T,T+1); retain enormous powers
    # of two symbolically, so even their integer magnitudes need not be built.
    gamma_D = A + 3
    contour_R = A + 4
    gamma_power_two_exponent = 2 * (gamma_D + gamma_D ** 2)
    margin_base_den = 32 * L_den * gamma_D
    factorial_R = math.factorial(contour_R)
    derivative_B = (2 * (2 * contour_R + 1) * factorial_R
                    + contour_R * (contour_R + 1) ** 2 * factorial_R)
    horizontal_base = 24 * derivative_B * margin_base_den
    vertical_base = 8 * (A + 1) * derivative_B * margin_base_den
    # These are the exact rational inequalities used in the proof.
    assert Fraction(4, 3) ** 4 > 2
    assert Fraction(4, 5) ** 5 < Fraction(1, 2)
    assert Fraction(2, 3 * (Q + 2)) < Fraction(1, Q + 2)
    assert 2 ** k >= 16 * M
    assert k == 0 or 2 ** (k - 1) < 16 * M
    assert 2 ** p >= 4 * L_den
    assert Fraction(3, 2 * J) <= Fraction(1, 8 * M * L_den)
    return {
        "input_T": str(T),
        "ceiling_A": A,
        "zeta_sup_bound_M": M,
        "binary_majorant_k": k,
        "root_bound_Q": Q,
        "candidate_count": Q + 1,
        "candidate_height_formula": "T + (j+1)/(Q+2), j=0,...,Q",
        "bad_disk_radius": f"1/{3 * (Q + 2)}",
        "L_denominator_bit_length": L_den.bit_length(),
        "accepted_margin_formula": "L/4",
        "mesh_subdivision_count_bit_length": J.bit_length(),
        "samples_per_candidate_bit_length": (J + 1).bit_length(),
        "total_sample_bound_bit_length": ((Q + 1) * (J + 1)).bit_length(),
        "Taylor_value_accuracy_bits": p,
        "Taylor_polynomial_degree": D,
        "sample_value_accuracy_bits": p_eval,
        "full_contour_gamma_D": gamma_D,
        "full_contour_derivative_radius_R": contour_R,
        "full_contour_gamma_sup_bound_bits": (
            gamma_D.bit_length() + gamma_power_two_exponent),
        "full_contour_margin_denominator_bits": (
            margin_base_den.bit_length() + gamma_power_two_exponent),
        "full_contour_horizontal_subdivision_count_bits": (
            horizontal_base.bit_length() + gamma_power_two_exponent),
        "full_contour_vertical_subdivision_count_bits": (
            vertical_base.bit_length() + gamma_power_two_exponent),
        "full_contour_total_segment_count_bits": (
            (2 * (horizontal_base + vertical_base)).bit_length()
            + gamma_power_two_exponent),
        "full_contour_value_accuracy_bits": (
            ceil_log2_integer(16 * margin_base_den)
            + gamma_power_two_exponent),
        "status": "bounds only; the search was not executed",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("T", nargs="*", default=["8", "32", "100", "65536"])
    args = parser.parse_args()
    print(json.dumps([bounds(Fraction(t)) for t in args.T], indent=2))


if __name__ == "__main__":
    main()
