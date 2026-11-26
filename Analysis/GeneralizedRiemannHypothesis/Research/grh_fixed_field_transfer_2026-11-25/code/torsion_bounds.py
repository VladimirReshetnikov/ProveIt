#!/usr/bin/env python3
"""Exact scalar costs and certified sufficient multivariate order exponents.

Standard-library only. All decisions use integers and fractions.
The mathematical proofs are in grh_fixed_field_transfer.pdf.
"""
from fractions import Fraction
from math import isqrt
import argparse
import json


def is_prime(p):
    return p >= 2 and all(p % q for q in range(2, isqrt(p) + 1))


def vp_integer(n, p):
    if n <= 0:
        raise ValueError("The integer must be positive.")
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def validate(p, e):
    if not is_prime(p):
        raise ValueError("p must be prime.")
    if e < 1:
        raise ValueError("The ramification index must be positive.")


def shell_cost(p, e, h):
    validate(p, e)
    if h < 1:
        raise ValueError("Shell indices start at one.")
    return Fraction(1, p ** min(vp_integer(e, p), h - 1))


def horizon_cost(p, e, h0, H):
    validate(p, e)
    if h0 < 1:
        raise ValueError("h0 must be positive.")
    if H < h0:
        return Fraction(0)
    w = vp_integer(e, p)
    transient_end = min(H, w)
    total = sum((Fraction(1, p ** (h - 1))
                 for h in range(h0, transient_end + 1)), Fraction(0))
    tail_start = max(h0, w + 1)
    if H >= tail_start:
        total += Fraction(H - tail_start + 1, p ** w)
    return total


def scalar_cutoff(p, e, h0, B):
    """First H for which C_K({h0,...,H}) > B, including equality cases."""
    validate(p, e)
    B = Fraction(B)
    if B < 0 or h0 < 1:
        raise ValueError("Require B >= 0 and h0 >= 1.")
    w = vp_integer(e, p)
    prefix = Fraction(0)
    for h in range(h0, w + 1):
        prefix += Fraction(1, p ** (h - 1))
        if prefix > B:
            return h
    tail_start = max(h0, w + 1)
    return tail_start + int((B - prefix) * p ** w)


def ceil_log_integer(p, n):
    """Least a >= 0 such that p**a >= positive integer n."""
    if n < 1:
        raise ValueError("n must be positive.")
    power, a = 1, 0
    while power < n:
        power *= p
        a += 1
    return a


def first_radial_level(p, rho):
    rho = Fraction(rho)
    if rho <= 0:
        raise ValueError("rho must be positive.")
    h, N = 1, p - 1
    while Fraction(1, N) > rho:
        h += 1
        N *= p
    return h


def multivariate_cutoff(p, e, dimension, rho, B, h0=None):
    """Finite-slope recurrence followed by the exact scalar cutoff.

This can improve the manuscript's simple closed sufficient upper bound.
No polynomial degree or packet-cardinality input is used.
"""
    validate(p, e)
    rho, B = Fraction(rho), Fraction(B)
    if dimension < 1 or rho <= 0 or B < 0:
        raise ValueError("Require dimension >= 1, rho > 0, B >= 0.")
    if h0 is None:
        h0 = first_radial_level(p, rho)
    if h0 < 1 or Fraction(1, (p - 1) * p ** (h0 - 1)) > rho:
        raise ValueError("h0 does not satisfy the radial condition.")
    radius, P, steps = rho, 1, []
    for j in range(dimension - 1):
        M = int(B / radius) + 1
        next_radius = radius / M ** 2
        steps.append({"step": j + 1, "radius_before": str(radius),
                      "slope_choices": M, "radius_after": str(next_radius)})
        radius, P = next_radius, P * M
    start = h0 + ceil_log_integer(p, P * P)
    H = scalar_cutoff(p, e, start, B)
    return {
        "p": p, "ramification_index": e,
        "wild_exponent": vp_integer(e, p), "dimension": dimension,
        "rho": str(rho), "budget": str(B), "coordinate_lower_exponent": h0,
        "slope_steps": steps, "slope_product_bound": P,
        "final_radius": str(radius), "scalar_start_level": start,
        "sufficient_upper_exponent": H,
        "scalar_cost_before": str(horizon_cost(p, e, start, H - 1)),
        "scalar_cost_at": str(horizon_cost(p, e, start, H)),
        "note": "Bounds root-of-unity order exponents, not conductor norms."
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--p", type=int, required=True)
    parser.add_argument("--e", type=int, required=True)
    parser.add_argument("--dimension", type=int, default=1)
    parser.add_argument("--rho", default="1")
    parser.add_argument("--budget", required=True)
    parser.add_argument("--h0", type=int)
    args = parser.parse_args()
    print(json.dumps(multivariate_cutoff(
        args.p, args.e, args.dimension, args.rho, args.budget, args.h0),
        indent=2))


if __name__ == "__main__":
    main()

