#!/usr/bin/env python3
"""Verify the rational comparisons for the explicit Gaussian reporter.

No Gaussian probabilities or transcendental functions are approximated.
The article proves the analytic estimates to which these comparisons apply.
The tiny eta and epsilon are stored symbolically by their dyadic exponents;
this script never constructs an integer with billions of bits.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parents[1]
        / "data"
        / "constant_certificate.json",
    )
    args = parser.parse_args()
    checks = []

    def verify(name, left, relation, right, explanation):
        left, right = F(left), F(right)
        comparisons = {
            "<": left < right,
            "<=": left <= right,
            "=": left == right,
            ">": left > right,
            ">=": left >= right,
        }
        assert comparisons[relation], (name, left, relation, right)
        checks.append(
            {
                "name": name,
                "left": str(left),
                "relation": relation,
                "right": str(right),
                "explanation": explanation,
                "passed": True,
            }
        )

    s = 2**13
    m = s * s + 1
    r = 9
    c = F(1, 3)
    h = F(9, s**3)
    radius = F(9, s**2)
    mismatch = radius + h
    sum_variances_bound = m * h * h
    e_upper = F(8, 3) + F(5, 96)

    verify("e_upper_identity", e_upper, "=", F(87, 32),
           "Sum through 1/3! plus geometric factorial-tail bound 5/96.")
    verify("e_upper_11_over_4", e_upper, "<", F(11, 4),
           "Provides e<11/4 and hence also e<3.")
    verify("e_upper_three", e_upper, "<", 3,
           "Used to replace exp(-50) by 3^(-50).")
    verify("sinh_three_upper", F(11, 4)**3, "<", 21,
           "sinh(3)<e^3/2<21/2.")
    verify("exp_small_geometric_bound", 1 / (1 - F(1, 16)), "=", F(16, 15),
           "The article proves exp(x)<1/(1-x), for 0<x<1.")
    verify("density_exponent_margin",
           c*c/2 + mismatch*(r+c) + mismatch*mismatch/2,
           "<", F(1, 16),
           "Controls phi(t)/q_selected by exp(1/16+ct)/(2h).")
    verify("all_interval_endpoints", c + r + h, "<", 10,
           "Every interval is contained in [-10,10].")
    verify("fallback_interval_endpoint", c + h, "<", F(1, 2),
           "The fallback probability is at least 2h phi(1/2).")
    verify("width_below_one", h, "<", 1,
           "Used in the tail numerator comparison.")
    verify("variance_sum_below_one", sum_variances_bound, "<", 1,
           "Each interval conditional variance is at most h^2.")
    verify("tail_numerator_at_cutoff", (r + 1)**2 + 1, "<=", 2*r*r,
           "t^2-2t-2 is increasing for t>=9, so (t+1)^2+1<=2t^2.")

    central_prefactor = 3 * (mismatch*mismatch + sum_variances_bound) / h
    central_prefactor_closed = F(54, s) * (1 + F(1, s) + F(1, s*s))
    verify("central_prefactor_identity", central_prefactor, "=",
           central_prefactor_closed, "Exact simplification before the exponential bounds.")
    central_bound = central_prefactor * F(16, 15) * F(21, 2)
    verify("central_integral_bound", central_bound, "<", F(3, 40),
           "Uses exp(1/16)<16/15 and sinh(3)<21/2.")
    verify("tail_prefactor_relaxation", F(164, 9), "<", F(55, 3),
           "Gaussian integration by parts produces 164/(9h).")
    verify("tail_exponent_relaxation", F(323, 8), ">", 40,
           "Together with e>5/2 this bounds exp(-323/8) by (2/5)^40.")
    tail_bound = F(55, 3) / h * F(2, 5)**40
    verify("tail_integral_bound", tail_bound, "<", F(1, 1000),
           "Entirely rational upper bound for both Gaussian tails.")
    gain_bound = c*c - F(3, 40) - F(1, 1000)
    verify("gain_identity", gain_bound, "=", F(79, 2250),
           "S is nonnegative and may be omitted for this lower bound.")
    verify("positive_gain_margin", gain_bound, ">", F(1, 32),
           "Provides Gamma>1/32.")

    q0 = F(1, 2**38 * 3**49)
    verify("probability_lower_bound_identity", 2*h/F(3)/3**50, "=", q0,
           "Uses sqrt(2pi)<3 and e<3, without evaluating an interval mass.")
    verify("probability_integer_comparison", 3**49, "<", 2**78,
           "Equivalent to q0>2^(-116).")
    verify("probability_dyadic_comparison", q0, ">", F(1, 2**116),
           "Uniform lower bound for every Gaussian interval mass.")
    verify("leaf_count_bound", m, "<", 2**27,
           "Used in transfer and logarithmic dimension bounds.")
    verify("sqrt_six_bound_squared", 6, "<", 3**2,
           "Justifies sqrt(K)<3 with K=6.")
    verify("fourth_root_six_bound_fourth_power", 6, "<", 2**4,
           "Justifies K^(1/4)<2 with K=6.")
    verify("mean_coefficient_bound", 10+c, "<", 11,
           "The transfer coefficient C=B+|c| is less than 11.")

    a_upper = (
        3600*m*2**116
        + 2*m*2**116*(1152+600*m)
        + (6336+7600*m)*2**232
    )
    verify("transfer_constant_bound", a_upper, "<", 2**274,
           "Rational majorant of all three terms in the transfer constant A.")
    delta = F(1, 2**560)
    verify("transfer_error_margin", F(a_upper, 2**280), "<", F(1, 64),
           "A sqrt(delta)<1/64<Gamma/2.")
    verify("transfer_error_vs_gain", F(a_upper, 2**280), "<", gain_bound/2,
           "Checks the actual rational Gaussian gain bound as well.")
    verify("interval_product_accuracy", delta, "<", q0/(4*m),
           "Ensures Q_U>=Q_G/2 by a product estimate.")
    verify("berry_esseen_squared", F(6, 2**1123), "<", delta*delta,
           "The Berry--Esseen constant is below one; E|score|^3<=sqrt(6).")
    verify("moment_closure_factor", F(3, 2)*(2*m+1)*(m-3), ">=", 0,
           "6m^2-[3(m+1)^2+3(m+1)/2] is this nonnegative quantity.")

    eta_exponent = 116*m + 7
    exponent_lower_comparison = 116*m + 47
    epsilon_exponent = 8_000_000_000
    verify("power_exponent_denominator", 4600*m, "<", 2**40,
           "Combines log(1+x)>x/2 with log(mM)<1150.")
    verify("power_exponent_integer_identity", exponent_lower_comparison,
           "=", 7_784_628_387, "No giant dyadic number is allocated.")
    verify("power_exponent_comparison", exponent_lower_comparison,
           "<", epsilon_exponent,
           "Therefore the proved positive exponent exceeds 2^(-8,000,000,000).")
    verify("budget_dimension_comparison", 1123*m, ">", 2**36,
           "With log(2)>1/2, theta-1<2/(1123m)<2^(-35).")

    certificate = {
        "arithmetic": "Python integers and fractions.Fraction; all comparisons exact",
        "scope": "Rational comparisons underlying the analytic proof in the article",
        "parameters": {
            "s": s, "m": m, "R": r, "c": str(c), "h": str(h),
            "K": 6, "B": 10, "selector_intervals_per_cell": 3,
            "M": {"base": 2, "exponent": 1123},
            "delta": {"base": 2, "negative_exponent": 560},
            "eta_lower_bound": {"base": 2, "negative_exponent": eta_exponent},
            "epsilon": {"base": 2, "negative_exponent": epsilon_exponent},
        },
        "checks_passed": len(checks),
        "all_passed": True,
        "checks": checks,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(certificate, indent=2) + "\n")
    print(f"PASS: {len(checks)} exact rational comparisons")
    print(f"Certificate: {args.output}")


if __name__ == "__main__":
    main()
