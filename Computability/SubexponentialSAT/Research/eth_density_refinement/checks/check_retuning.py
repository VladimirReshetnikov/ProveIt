#!/usr/bin/env python3
"""Exact checks for the retuned tapered-Hermite contraction parameters.

No third-party dependencies. This checks the arithmetic lemmas, not the full
SAT algorithm. All valuation and multiplicity checks use integer arithmetic.
"""

from fractions import Fraction
import json
import math


def v2(n):
    n = abs(n)
    if not n:
        raise ValueError("v2(0) is not finite")
    return (n & -n).bit_length() - 1


def ceildiv(a, b):
    return (a + b - 1) // b


def slope(M, a, u):
    L = 1 << a
    unit_conditions = sum((L >> i) * (u - i) for i in range(u))
    return (M * (2 * L - 1)) // unit_conditions + 1


def exact_loss(h, a, u, i):
    return h * sum(j * min(j, u - i) * (1 << (a - i - j))
                   for j in range(1, a - i + 1))


def check_small_parameters():
    cases = 0
    nodes = 0
    coefficients = 0
    largest_precision_ratio = Fraction(0)
    for a in range(1, 8):
        L = 1 << a
        grid = [t for t in range(-L, L) if t]
        for u in range(1, a + 1):
            base = sum((L >> i) * (u - i) for i in range(u))
            closed = L * (2 * u - 2) + (L >> (u - 1))
            assert base == closed
            for M in range(u, u + 13):
                h = slope(M, a, u)
                old_h = ceildiv(3 * M, u)
                q = {t: h * max(0, u - v2(t)) for t in grid}
                total = sum(q.values())
                degree = M * (2 * L - 1)
                assert total > degree
                assert (h - 1) * base <= degree  # minimal integral slope
                assert h <= old_h
                assert max(q.values()) <= 3 * M
                if u >= 2:
                    assert h <= ceildiv(M, u - 1)
                for t in grid:
                    if not q[t]:
                        continue
                    i = v2(t)
                    D = L >> i
                    direct_val = sum(q[z] * (v2(z) - v2(t - z))
                                     for z in grid if z != t)
                    loss = exact_loss(h, a, u, i)
                    assert direct_val == -loss
                    assert 0 <= loss <= 6 * h * D
                    delta = loss + (q[t] - 1) * (a + 1 - i)
                    simple_delta = 6 * h * D + (q[t] - 1) * (a + 1 - i)
                    old_delta = 8 * old_h * D + 8 * M * (a + 1)
                    assert 0 <= delta <= simple_delta < old_delta
                    largest_precision_ratio = max(
                        largest_precision_ratio, Fraction(delta, old_delta))
                    for j in range(q[t]):
                        assert delta + direct_val - j * (a + 1 - i) >= 0
                        coefficients += 1
                    nodes += 1
                cases += 1
    return {
        "parameter_cases": cases,
        "retained_nodes_checked": nodes,
        "coefficient_error_bounds_checked": coefficients,
        "largest_new_to_old_precision_increment_ratio": str(largest_precision_ratio),
    }


def packing_data(eta):
    return {
        "eta": str(eta),
        "L_exponent": str(4 * eta),
        "D_arr_exponent": str(48 * eta),
        "D_arr_squared_Delta_exponent": str(Fraction(9, 10) + 96 * eta),
        "L_times_D_arr_exponent": str(52 * eta),
        "packing_exponent_below_one": Fraction(9, 10) + 96 * eta < 1,
    }


def entropy_coefficient(eta, precision_coefficient):
    rho = 3 / 32
    return (2 * math.pi * math.sqrt(precision_coefficient) /
            (math.log(2) * math.sqrt(float(eta)) * (1 - rho * math.sqrt(2))))


def main():
    old = entropy_coefficient(Fraction(1, 131072), 24)
    new = entropy_coefficient(Fraction(1, 2048), 6)
    aggressive = entropy_coefficient(Fraction(1, 1024), 6)
    assert math.isclose(old / new, 16)
    result = {
        "status": "PASS",
        "scope": "arithmetic lemmas only; not a SAT implementation or formal proof",
        "exact_checks": check_small_parameters(),
        "packing": [packing_data(Fraction(1, x)) for x in (131072, 2048, 1024)],
        "base_two_mode_entropy_coefficient_per_C": {
            "source_matched_analysis": old,
            "retuned_recommended": new,
            "retuned_aggressive": aggressive,
            "source_over_recommended": old / new,
            "source_over_aggressive": old / aggressive,
            "unchanged_additive_leaf_coefficient": 1,
        },
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
