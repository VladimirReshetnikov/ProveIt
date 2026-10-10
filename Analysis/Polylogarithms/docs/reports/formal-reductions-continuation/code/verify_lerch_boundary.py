#!/usr/bin/env python3
"""Exact rational checks for the Lerch elementary-boundary theorems.

This program does not numerically locate zeros or prove the perturbation
theorem.  It verifies finite coefficient identities and certifies signs
of the constants that enter the analytic theorem.  All interval arithmetic
uses fractions.Fraction; no floating-point operation enters a certificate.
"""

from fractions import Fraction as F
from math import factorial
from pathlib import Path
import argparse
import json

from upstream_stieltjes_certificate import enclosure as stieltjes_enclosure
from upstream_stieltjes_certificate import self_test as stieltjes_self_test


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def mul(a, b):
    products = [x * y for x in a for y in b]
    return min(products), max(products)


def scale(a, c):
    return mul(a, (c, c))


def evaluate(coefficients, interval):
    value = F(0), F(0)
    for coefficient in reversed(coefficients):
        value = add(mul(value, interval), (coefficient, coefficient))
    return value


def log2_interval(terms):
    u = F(1, 3)
    lower = 2 * sum((u ** (2 * j + 1) / (2 * j + 1)
                     for j in range(terms)), F(0))
    tail = 2 * u ** (2 * terms + 1) / ((2 * terms + 1) * (1 - u * u))
    return lower, lower + tail


def polynomial_by_operators(n, k):
    result = [F(0)] * n + [F(1)]
    for j in range(1, k + 1):
        result = [result[i] + F(i + 1, j) * result[i + 1]
                  for i in range(n)] + [result[n]]
    return result


def polynomial_by_coefficients(n, k):
    elementary = [F(1)] + [F(0)] * k
    for j in range(1, k + 1):
        for i in range(j, 0, -1):
            elementary[i] += elementary[i - 1] / j
    return [F(factorial(n), factorial(r)) * elementary[n - r]
            if n - r <= k else F(0)
            for r in range(n + 1)]


def fraction_data(x):
    return {"numerator": str(x.numerator), "denominator": str(x.denominator)}


def fixed_decimal(integer, digits):
    sign = "-" if integer < 0 else ""
    s = str(abs(integer)).zfill(digits + 1)
    return sign + s[:-digits] + "." + s[-digits:]


def outward_decimal(interval, digits=16):
    factor = 10 ** digits
    lo = interval[0] * factor
    hi = interval[1] * factor
    low_int = lo.numerator // lo.denominator
    high_int = -((-hi.numerator) // hi.denominator)
    return [fixed_decimal(low_int, digits), fixed_decimal(high_int, digits)]


def interval_data(interval):
    return {"lower": fraction_data(interval[0]),
            "upper": fraction_data(interval[1]),
            "outward_decimal": outward_decimal(interval)}


def sign_of(interval):
    if interval[0] > 0:
        return 1
    if interval[1] < 0:
        return -1
    return 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-index", type=int, default=16)
    parser.add_argument("--log-terms", type=int, default=80)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("lerch_boundary_certificates.json"))
    args = parser.parse_args()
    log_interval = log2_interval(args.log_terms)
    minus_log = -log_interval[1], -log_interval[0]
    identity_checks = 0
    grid = []
    for n in range(1, args.max_index + 1):
        for k in range(1, n + 2):
            p = polynomial_by_operators(n, k)
            assert p == polynomial_by_coefficients(n, k)
            identity_checks += 1
            if n <= k:
                continue
            d = n - k
            assert all(c == 0 for c in p[:d])
            assert p[d] == F(factorial(n), factorial(k) * factorial(d))
            delta = scale(evaluate(p, minus_log),
                          F((-1) ** d * factorial(k) * factorial(d),
                            2 ** (k + 1) * factorial(n)))
            sgn = sign_of(delta)
            assert sgn, (n, k, "Increase --log-terms to separate this interval.")
            count = k + 1 if d % 2 else k + (2 if sgn < 0 else 0)
            grid.append({"n": n, "k": k, "d": d, "sign_delta": sgn,
                         "small_positive_rho_simple_zero_count": count,
                         "delta_interval": interval_data(delta)})
            if k == 1:
                assert sgn == 1
                assert count == (2 if n % 2 == 0 else 1)

    p43 = polynomial_by_operators(4, 3)
    assert p43 == [F(0), F(4), F(12), F(22, 3), F(1)]
    derivative = scale(evaluate(p43, minus_log), F(1, 64))
    assert derivative[0] > 0
    coarse_lower = F(8, 27) - F(22, 3) * F(9, 16) + 8 - 4
    assert coarse_lower == F(37, 216)
    assert log_interval[0] > F(2, 3) and log_interval[1] < F(3, 4)

    # Replay precisely the upstream endpoint signs used in the new theorems:
    # two for the uniform n=2 classification and nine for the n=3,4 endpoint
    # counts that force interior multiple-zero events.
    stieltjes_self_test()
    endpoint_checks = []
    endpoint_cases = [(2, "1", 1), (2, "13/10", -1),
                      (3, "4/5", 1), (3, "11/10", -1),
                      (3, "3/2", 1), (3, "21/10", -1),
                      (4, "4/5", 1), (4, "47/50", -1),
                      (4, "6/5", 1), (4, "17/10", -1),
                      (4, "11/5", 1)]
    for n, a, expected in endpoint_cases:
        value = stieltjes_enclosure(n, 1, F(a), M=40, R=16)
        assert value.sign() == expected
        endpoint_checks.append({"n": n, "k": 1, "rho": 1, "a": a,
                                "expected_sign": expected,
                                "normalization": "a^(k+1) G_{n,k}(a,1)",
                                "outward_decimal": value.decimal(35),
                                "scaled_lower_integer": str(value.lo),
                                "scaled_upper_integer": str(value.hi),
                                "scale": "10^90", "M": 40, "R": 16})

    payload = {
        "arithmetic": "fractions.Fraction, all rational endpoints exact",
        "analytic_proof": "article/sections/lerch_zeros.tex",
        "source_commit": "a2a4cf58c49c745058c40e4a6748d472a3420f18",
        "identity_checks": identity_checks,
        "log_terms": args.log_terms,
        "log2_interval": interval_data(log_interval),
        "counterexample_n4_k3_derivative": interval_data(derivative),
        "counterexample_coarse_positive_factor": fraction_data(coarse_lower),
        "small_rho_grid": grid,
        "upstream_endpoint_certificate_replay": {
            "source": "upstream_stieltjes_certificate.py",
            "original_repository_path": "Analysis/Polylogarithms/docs/reports/"
                                        "stieltjes-derivative-zeros/code/"
                                        "06-zero-geometry-exact_verify.py",
            "source_commit": "a2a4cf58c49c745058c40e4a6748d472a3420f18",
            "evaluations": endpoint_checks
        },
        "limitations": [
            "No numerical value of the small-rho threshold is certified.",
            "The perturbation proof, not the grid, gives the zero counts.",
            "No interior multiple-zero location or nondegeneracy is certified."
        ]
    }
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps({"identity_checks": identity_checks,
                      "certified_delta_signs": len(grid),
                      "replayed_endpoint_signs": len(endpoint_checks),
                      "counterexample_derivative_interval": outward_decimal(derivative),
                      "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
