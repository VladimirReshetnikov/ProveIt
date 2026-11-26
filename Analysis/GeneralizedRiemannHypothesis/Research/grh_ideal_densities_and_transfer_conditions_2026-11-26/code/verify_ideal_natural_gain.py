#!/usr/bin/env python3
"""Exact rational certificate for the ideal-density gain over Q(sqrt(-23)).

The all-number-field theorem and the avoidance argument are mathematical proofs
in ideal_natural_gain.tex. This program verifies only their displayed finite
certificate: the reductions of X^2-X+6 at 2 and 3, the rational T upper bounds,
the local gain, and the rational estimates for the two zeta values.

Run with ordinary Python 3 (not -O):
  python3 verify_ideal_natural_gain.py --output ideal_natural_gain_certificate.json
"""

from fractions import Fraction as Q
from math import prod
from pathlib import Path
import argparse
import json


def run():
    reductions = {}
    for p in (2, 3):
        roots = [a for a in range(p) if (a*a-a+6) % p == 0]
        assert roots == [0, 1]
        assert all((2*a-1) % p != 0 for a in roots)
        assert -23 % p != 0
        reductions[str(p)] = {"roots": roots, "simple": True}

    weights = [Q(1, 2), Q(1, 2), Q(1, 3), Q(1, 3)]
    upper_T = lambda w: 1+w*w+w**3+w**8/(1-w)
    t2, t3 = upper_T(Q(1, 2)), upper_T(Q(1, 3))
    assert t2 == Q(177, 128)
    assert t3 == Q(5023, 4374)
    bracket = prod(1+w for w in weights)-1-prod(upper_T(w) for w in weights)
    assert bracket == Q(16658080679, 34828517376)
    prefactor = prod((1-w)*w for w in weights)
    assert prefactor == Q(1, 324)
    selected_square_product = prod(1-w*w for w in weights)
    assert selected_square_product == Q(4, 9)
    outside_lower = Q(3, 5)**2 / selected_square_product
    assert outside_lower == Q(81, 100)
    gain_lower = outside_lower * prefactor * bracket
    assert gain_lower == Q(16658080679, 13931406950400)
    assert gain_lower > Q(11957, 10_000_000)

    zeta2_integral_upper = sum(Q(1, n*n) for n in range(1, 11))+Q(1, 10)
    zeta3_integral_upper = sum(Q(1, n**3) for n in range(1, 5))+Q(1, 32)
    assert zeta2_integral_upper == Q(2095337, 1270080) < Q(33, 20) < Q(5, 3)
    assert zeta3_integral_upper == Q(2089, 1728) < Q(121, 100)
    assert Q(33, 20)*Q(121, 100) == Q(3993, 2000) < 2

    return {
        "status": "PASS: finite exact rational certificate; all-fields proof is in the manuscript",
        "field": "Q(sqrt(-23))",
        "integral_generator": "omega=(1+sqrt(-23))/2",
        "minimal_polynomial": [1, -1, 6],
        "discriminant": -23,
        "prime_reductions": reductions,
        "selected_prime_ideal_norms": [2, 2, 3, 3],
        "ratio_scope": "proper integral ideals only",
        "T_upper_at_half": str(t2),
        "T_upper_at_third": str(t3),
        "bracket_lower": str(bracket),
        "prefactor": str(prefactor),
        "selected_square_product": str(selected_square_product),
        "outside_factor_strict_lower": str(outside_lower),
        "density_gain_strict_lower": str(gain_lower),
        "decimal_display_lower": "0.0011957",
        "zeta2_integral_upper": str(zeta2_integral_upper),
        "zeta3_integral_upper": str(zeta3_integral_upper),
        "zeta2_zeta3_strict_upper": "3993/2000 < 2",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    payload = json.dumps(result, indent=2)+"\n"
    if args.output:
        args.output.write_text(payload)
    print(payload, end="")
