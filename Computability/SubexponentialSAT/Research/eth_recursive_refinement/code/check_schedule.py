#!/usr/bin/env python3
"""Exact finite checks for the additive-guard contraction schedule.

These check arithmetic identities and selected finite parameter instances.
They do not test an end-to-end SAT solver or prove an asymptotic theorem.
Only the displayed constant evaluations use floating point.
"""
from __future__ import annotations

from fractions import Fraction
import json
import math


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def ceil_log2(n: int) -> int:
    if n < 1:
        raise ValueError("positive integer required")
    return (n - 1).bit_length()


def schedule(lam: int, depth: int) -> tuple[int, int, int]:
    if lam < 2 or depth < 0:
        raise ValueError("lambda >= 2 and depth >= 0 required")
    g = ceil_log2(lam) ** 2
    u = lam // (260 * 9**depth)
    a = sum(lam // (260 * 9**j) for j in range(depth + 1)) + (depth + 1) * g
    return u, a, g


def leading_constant(gamma: Fraction) -> float:
    if gamma <= 0:
        raise ValueError("positive gamma required")
    return 9 * math.pi / (4 * math.log(2)) * math.sqrt(520 / float(gamma))


def main() -> None:
    require(54**25 < 2**144, "exact logarithm bound")
    A = Fraction(9, 2080)
    critical = Fraction(9, 10) + 4 * A * Fraction(144, 25)
    require(critical == Fraction(3249, 3250), "critical exponent certificate")
    require(Fraction(2, 54) < Fraction(1, 16), "provisional shrinkage")
    require(9 < 16, "positive provisional u exponent")
    require(Fraction(2, 54) * 3 == Fraction(1, 9), "path ratio")
    require(sum(Fraction(1, 9) ** d for d in range(20)) < Fraction(9, 8), "geometric bound")

    identities = 0
    for lam in range(2, 5000, 7):
        previous = 0
        for d in range(12):
            u, a, g = schedule(lam, d)
            require(a - u - previous == g, "additive guard identity")
            require(a <= A * lam + (d + 1) * g, "packet exponent upper bound")
            require(a >= u, "retained valuations fit packet")
            previous = a
            identities += 3

    instances = []
    for q in (12, 16, 20, 24, 32, 40, 64, 128, 256):
        lam = 2**q
        active_depths = []
        power16 = 1
        depth = 0
        while power16 < lam:
            u, a, g = schedule(lam, depth)
            # s in (2^(lambda-1), 2^lambda], M > s/lambda.
            # These are rational upper bounds on logarithms of the packing ratios.
            collision_log_bound = 3 + Fraction(576, 25) * a - Fraction(lam, 10) + q
            padding_log_bound = 1 + Fraction(313, 25) * a - lam + q
            degree_log_bound = 1 + a - Fraction(9, 10) * (lam - 1)
            active_depths.append({
                "depth": depth,
                "u_positive": u > 0,
                "collision_packing_pass": collision_log_bound <= 0,
                "padding_packing_pass": padding_log_bound <= 0,
                "packet_degree_pass": degree_log_bound <= 0,
            })
            if q >= 40:
                require(u > 0, "eventual retained level nonempty")
                require(collision_log_bound < 0, "selected eventual collision condition")
                require(padding_log_bound < 0, "selected eventual padding condition")
                require(degree_log_bound < 0, "selected eventual degree condition")
            power16 *= 16
            depth += 1
        instances.append({
            "lambda_is_2_to": q,
            "active_depths_checked": len(active_depths),
            "all_u_positive": all(x["u_positive"] for x in active_depths),
            "all_packing_pass": all(
                x["collision_packing_pass"] and x["padding_packing_pass"] and x["packet_degree_pass"]
                for x in active_depths
            ),
            "depth_results": active_depths,
        })

    result = {
        "status": "passed",
        "scope": "exact finite schedule arithmetic; not a SAT implementation or asymptotic proof",
        "exact_integer_certificate": {
            "left": str(54**25),
            "right": str(2**144),
            "inequality": "54^25 < 2^144",
            "critical_exponent_upper_bound": "3249/3250",
        },
        "schedule_identities_checked": identities,
        "leading_coefficients_float_evaluations": {
            str(gamma): leading_constant(gamma)
            for gamma in (Fraction(1), Fraction(2), Fraction(3), Fraction(64, 21))
        },
        "lower_degree_query_coefficient": {
            "degree_exponent": "51/100",
            "epsilon": "1/54",
            "exact_formula": "(9*pi/(4*ln(2)))*sqrt(108/(64/21))",
            "decimal": 9*math.pi/(4*math.log(2))*math.sqrt(108/float(Fraction(64, 21))),
            "packing_exponent_rational_upper_bound": str(Fraction(51,100)+Fraction(144,25)/12),
        },
        "selected_logarithmic_size_instances": instances,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
