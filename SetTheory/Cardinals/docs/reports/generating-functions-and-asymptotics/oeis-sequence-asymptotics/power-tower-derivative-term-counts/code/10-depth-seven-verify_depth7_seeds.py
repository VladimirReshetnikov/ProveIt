#!/usr/bin/env python3
"""Exact moment-seed and root-bound verifier for the depth-seven A290268 proof.

Uses only Python's standard library and exact integers/rationals.
"""
from __future__ import annotations

from fractions import Fraction as F
import sys
sys.set_int_max_str_digits(0)
from hashlib import sha256
import json
from pathlib import Path

D = 7
R = 4898
Q = 9825
T = F(21279, 500)  # 42.558, a rational upper bound for the largest residual root
PI_LO = F(103993, 33102)
PI_HI = F(104348, 33215)
P_LO = PI_LO * PI_LO
P_HI = PI_HI * PI_HI


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def pi7(z: F, p: F) -> F:
    """Pi_7(z) with p standing for pi^2."""
    return z**3 - 5 * p * z**2 + 3 * p**2 * z - p**3 / 7


def arctan_partial(reciprocal: int, term_count: int) -> F:
    """Alternating Taylor partial sum for arctan(1/reciprocal)."""
    x = F(1, reciprocal)
    return sum(
        ((-1) ** j) * x ** (2 * j + 1) / (2 * j + 1)
        for j in range(term_count)
    )


def machin_pi_interval() -> tuple[F, F]:
    """Certified interval from Machin's identity and alternating remainders.

    With N terms, the arctangent partial sum is a lower bound for even N and
    an upper bound for odd N.  We use

        pi/4 = 4 arctan(1/5) - arctan(1/239).
    """
    atan5_lower = arctan_partial(5, 12)
    atan5_upper = arctan_partial(5, 13)
    atan239_lower = arctan_partial(239, 2)
    atan239_upper = arctan_partial(239, 3)
    lower = 4 * (4 * atan5_lower - atan239_upper)
    upper = 4 * (4 * atan5_upper - atan239_lower)
    return lower, upper


def center_jet(depth: int, degree: int) -> list[int]:
    """Return coefficients through u^depth of the center jet V_degree(u)."""
    q = 2 * depth
    r = 4 * depth + 1
    a = [1] + [0] * depth
    for j in range(r):
        a = [
            (2 * depth - j) * a[i] + (a[i - 1] if i else 0)
            for i in range(depth + 1)
        ]
    if degree == 0:
        return a
    b = [2 * (a[i - 1] if i else 0) for i in range(depth + 1)]
    if degree == 1:
        return b
    for k in range(1, degree):
        c = [
            2 * (b[i - 1] if i else 0) + k * (k + r) * a[i]
            for i in range(depth + 1)
        ]
        a, b = b, c
    return b


def harmonic_pair(n: int) -> tuple[F, F]:
    h = F(0)
    h2 = F(0)
    for j in range(1, n + 1):
        h += F(1, j)
        h2 += F(1, j * j)
    return h, h2


def main() -> None:
    # Prove the rational pi interval internally.  Machin's identity follows
    # from the tangent addition formula; the inequalities are the standard
    # alternating-series remainder bounds.
    machin_lower, machin_upper = machin_pi_interval()
    require(machin_lower > PI_LO, "Machin lower bound does not prove PI_LO")
    require(machin_upper < PI_HI, "Machin upper bound does not prove PI_HI")
    require(PI_LO < PI_HI, "bad rational pi interval")

    # Pi_7(T) is positive at the worst admissible p, and Pi_7 is increasing
    # for z >= T.  Pi_7(T,p) decreases with p on our interval.
    value_at_upper_p = pi7(T, P_HI)
    dz_at_upper_p = 3 * T**2 - 10 * P_HI * T + 3 * P_HI**2
    dp_upper = -5 * T**2 + 6 * P_HI * T  # omits an additional negative term
    require(T > 3 * P_HI, "T does not lie beyond the last critical point")
    require(value_at_upper_p > 0, "residual root bound failed")
    require(dz_at_upper_p > 0, "tail monotonicity failed")
    require(dp_upper < 0, "monotonicity in p failed")

    target_rational = T - P_LO / 3
    target_ratio = target_rational / 2

    jet = center_jet(D, R)
    require(jet[1] > 0, "center linear coefficient is not positive")
    center_ratio = F(jet[3], jet[1])
    require(center_ratio > target_ratio, "center moment seed failed")

    hq, hq2 = harmonic_pair(Q)
    h14, h14_2 = harmonic_pair(2 * D)
    tail_rational = (hq - h14) ** 2 - hq2 - h14_2
    require(tail_rational > target_rational, "tail moment seed failed")

    # Show that the selected integer cutoffs are the first ones satisfying
    # these particular sufficient inequalities (not a claim of optimality of
    # the proof method itself).
    prev_jet = center_jet(D, R - 2)
    prev_center_ratio = F(prev_jet[3], prev_jet[1])
    hprev, hprev2 = harmonic_pair(Q - 1)
    prev_tail = (hprev - h14) ** 2 - hprev2 - h14_2
    require(prev_center_ratio <= target_ratio, "R is not minimal for this seed")
    require(prev_tail <= target_rational, "Q is not minimal for this seed")

    digest_payload = "\n".join(
        [
            str(jet[1]),
            str(jet[3]),
            str(tail_rational.numerator),
            str(tail_rational.denominator),
            str(value_at_upper_p.numerator),
            str(value_at_upper_p.denominator),
        ]
    ).encode()

    center_margin = center_ratio - target_ratio
    tail_margin = tail_rational - target_rational
    record = {
        "depth": D,
        "center_cutoff_R": R,
        "tail_cutoff_Q": Q,
        "root_upper_bound_T": str(T),
        "pi_lower_bound": str(PI_LO),
        "pi_upper_bound": str(PI_HI),
        "machin_lower_margin": str(machin_lower - PI_LO),
        "machin_upper_margin": str(PI_HI - machin_upper),
        "Pi7_T_at_pi_upper_squared_positive": True,
        "Pi7_T_value": str(value_at_upper_p),
        "center_ratio_decimal": float(center_ratio),
        "center_target_ratio": str(target_ratio),
        "center_margin_decimal": float(center_margin),
        "center_margin_numerator_bits": center_margin.numerator.bit_length(),
        "center_margin_denominator_bits": center_margin.denominator.bit_length(),
        "center_u1_bits": jet[1].bit_length(),
        "center_u3_bits": jet[3].bit_length(),
        "tail_rational_decimal": float(tail_rational),
        "tail_target_rational": str(target_rational),
        "tail_margin_decimal": float(tail_margin),
        "tail_margin_numerator_bits": tail_margin.numerator.bit_length(),
        "tail_margin_denominator_bits": tail_margin.denominator.bit_length(),
        "R_minus_2_fails_same_test": True,
        "Q_minus_1_fails_same_test": True,
        "seed_payload_sha256": sha256(digest_payload).hexdigest(),
        "status": "PASS",
    }
    out = Path(__file__).with_name("depth7_seed_certificate.json")
    out.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
