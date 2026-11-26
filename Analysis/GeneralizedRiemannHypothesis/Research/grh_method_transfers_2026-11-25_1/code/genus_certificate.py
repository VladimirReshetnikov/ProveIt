#!/usr/bin/env python3
"""Exact arithmetic checks for the intermediate-genus exclusion theorem.

This checks constants, ranges, and a demonstration discriminant. It does
not verify GRH, class field theory, Bach--Sorenson, or the EKN census.
Run with Python 3; no third-party dependencies are required.
"""
from fractions import Fraction as Q
from math import isqrt
import json


def exp_bounds(x: Q, terms=240):
    """Rational lower/upper bounds for exp(x), x>=0, via positive series."""
    assert x >= 0 and terms + 2 > x
    term = Q(1)
    total = term
    for j in range(1, terms + 1):
        term *= x / j
        total += term
    first_tail = term * x / (terms + 1)
    # Every later ratio is <= x/(terms+2).
    return total, total + first_tail / (1 - x / (terms + 2))


def prime_trial(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def frac_data(x):
    return {"numerator": x.numerator, "denominator": x.denominator,
            "illustrative_decimal": float(x)}


def main():
    x0 = 31 * 10**19
    x1 = 25 * 10**24
    y0_upper = Q(236, 5)
    assert exp_bounds(Q(47))[1] < x0
    assert exp_bounds(y0_upper)[0] > x0
    assert exp_bounds(Q(59))[0] > x1

    rows = [
        (4, Q(407, 100), Q(638, 100), 1200000),
        (8, Q(6516, 1000), Q(698, 100), 75000),
        (16, Q(1396, 100), Q(644, 100), 850),
        (32, Q(2792, 100), Q(708, 100), 14),
    ]
    certificates = []
    for n, a, b, radius in rows:
        # Derivative sign of (a*y+b)^6 exp(-y) for all y>=47.
        assert 6 * a < a * 47 + b
        m = a * y0_upper + b
        ratio = 4 * radius * m**6 / x0
        assert ratio < 1
        maximal_integer_radius = Q(x0, 4 * m**6)
        certificates.append({
            "field_degree": n, "a": frac_data(a), "b": frac_data(b),
            "safe_ramified_norm_radius": radius,
            "prime_sqrt_bound_at_log_upper": frac_data(m),
            "exact_ratio_to_census_cutoff": frac_data(ratio),
            "integer_radius_floor": maximal_integer_radius.numerator //
                                    maximal_integer_radius.denominator,
        })

    # Table 3 range checks: n>=8 remains in the 100--1000 row.
    for n in (8, 16, 32):
        assert 100 < (n // 2) * 47 < (n // 2) * 59 < 1000
    # For n=4 the lower-row envelope also dominates the upper-row bound.
    assert Q(407, 100) > Q(3054, 1000)
    assert Q(407, 100) * 50 + Q(638, 100) > \
           Q(3054, 1000) * 50 + Q(708, 100)

    primes = [2, 3, 5, 7, 11, 1000000007, 1000000009]
    assert all(prime_trial(p) for p in primes)
    assert len(set(primes)) == 7
    rad = 1
    for p in primes:
        rad *= p
    abs_discriminant = 4 * rad  # -rad is squarefree and 2 mod 4.
    assert rad % 4 == 2
    assert x0 < abs_discriminant < 21 * 10**21
    assert abs_discriminant // primes[-1] > 10**8
    product_five = 2 * 3 * 5 * 7 * 11
    assert product_five < 1200000

    output = {
        "all_assertions_passed": True,
        "exact_arithmetic": "fractions.Fraction; primality by trial division",
        "census_cutoff": x0, "published_global_upper_bound": x1,
        "logarithm_certificates": "exp(47)<X0<exp(236/5); X1<exp(59)",
        "certificates": certificates,
        "demonstration": {
            "D": -abs_discriminant, "ramified_primes": primes,
            "largest_prime_cofactor": abs_discriminant // primes[-1],
            "five_smallest_product": product_five,
            "passes_prior_stated_numerical_conditions": True,
            "excluded_by_new_genus_certificate": True,
        },
        "not_checked": ["full Lean GRH build", "class field theory",
                        "Bach-Sorenson proof", "EKN census"],
    }
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
