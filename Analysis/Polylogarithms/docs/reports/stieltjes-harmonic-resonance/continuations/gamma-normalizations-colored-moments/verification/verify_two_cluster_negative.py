#!/usr/bin/env python3
"""Reproduce the independent negative-argument two-cluster audit check.

Dependencies: Python 3 and mpmath.  Default working precision: 55 digits.
Run: python verify_two_cluster_negative.py

This checks r=1, s=2, x=1, B=4, C=0, so q=-4.  The ordinary
chord-subtracted beta integral is compared with polylogarithms evaluated
by their differential identities, with the positive-argument Landen
transform, and with the anchored mass primitive.  These floating-point
diagnostics supplement the analytic proof; they are not interval bounds.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=55)
    parser.add_argument(
        "--output",
        type=Path,
        default=(Path(__file__).resolve().parent.parent / 'evidence' / 'two_cluster_negative_checks.json'),
    )
    args = parser.parse_args()
    if args.dps < 30:
        parser.error("--dps must be at least 30")
    mp.mp.dps = args.dps

    q = mp.mpf(-4)
    log_one_minus_q = mp.log1p(-q)

    def chord_remainder(t):
        # F(t)=-log(1+4(1-t)); subtract (1-t)F(0)+tF(1).
        return -mp.log1p(-q * (1 - t)) + (1 - t) * log_one_minus_q

    face = 2 * mp.quad(
        lambda t: chord_remainder(t) * mp.log(t) / (t * (1 - t)),
        [0, mp.mpf(".25"), mp.mpf(".75"), 1],
    )

    # d/dz Li_{1,2}(z)=Li_2(z)/(1-z), with value zero at z=0.
    li12 = mp.quad(
        lambda v: q * mp.polylog(2, q * v) / (1 - q * v),
        [0, mp.mpf(".5"), 1],
    )
    li111 = -(log_one_minus_q**3) / 6
    p12 = li12 + li111
    dictionary_face = 2 * p12

    swapped_q = q / (q - 1)
    p21_swapped = mp.quad(
        lambda v: swapped_q * mp.polylog(2, swapped_q * v)
        / (1 - swapped_q * v),
        [0, mp.mpf(".5"), 1],
    )

    def r12(z):
        # R_{1,2}=Li_2+Li_{1,1}; Li_{1,1}=log(1-z)^2/2.
        return mp.polylog(2, z) + mp.log1p(-z) ** 2 / 2

    # The C-derivative moves both copies of C; orientation is B=4 to C=0.
    primitive = 2 * mp.quad(
        lambda current_c: r12((current_c - 4) / (1 + current_c))
        / (1 + current_c),
        [4, 2, 0],
    )

    tolerance = mp.power(10, 7 - args.dps)

    def comparison(name, left, right):
        residual = abs(left - right)
        return {
            "name": name,
            "left": mp.nstr(left, args.dps),
            "right": mp.nstr(right, args.dps),
            "absolute_residual": mp.nstr(residual, 12),
            "absolute_tolerance": mp.nstr(tolerance, 12),
            "passed": bool(residual < tolerance),
        }

    checks = [
        comparison("ordinary_beta_face_vs_negative_argument_dictionary", face,
                   dictionary_face),
        comparison("landen_transform_negative_to_positive_argument", p12,
                   p21_swapped),
        comparison("anchored_mass_primitive_vs_ordinary_beta_face", primitive,
                   face),
    ]
    result = {
        "script": Path(__file__).name,
        "mpmath_version": mp.__version__,
        "working_decimal_digits": args.dps,
        "parameters": {"r": 1, "s": 2, "x": 1, "B": 4, "C": 0,
                       "q": "-4", "swapped_q": "0.8"},
        "face": "I_3(U -> -log(1+U); 4,0,0)",
        "interpretation": (
            "Ordinary convergent quadrature on real branches, including q=-4 "
            "outside the defining power-series disk. Floating-point diagnostics, "
            "not certified interval enclosures or formal proof."
        ),
        "checks": checks,
        "all_passed": all(check["passed"] for check in checks),
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    if not result["all_passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
