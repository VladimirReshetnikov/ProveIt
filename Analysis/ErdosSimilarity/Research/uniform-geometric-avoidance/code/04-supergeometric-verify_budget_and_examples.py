#!/usr/bin/env python3
"""Exact finite checks for the biased routing budget and rational examples.

Python standard library only. This script verifies finite identities and
integer bounds. It is not a proof of the asymptotic or continuum theorems,
and it does not construct the universal compact avoiding set.
"""

import argparse
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
import json


CHECKS = {}


def check(category, condition):
    CHECKS[category] = CHECKS.get(category, 0) + 1
    if not condition:
        raise AssertionError(category)


def ceil_fraction(value):
    return -((-value.numerator) // value.denominator)


def biased_probability_checks():
    rows = []
    for p in (F(1, 3), F(2, 5), F(3, 4)):
        for theta in (F(1, 2), F(1, 3), F(2, 7)):
            for q in range(1, 13):
                # Sum over the number of fresh active gates. The terminal
                # failures are independent only AFTER fixing the selectors.
                miss = sum(F(comb(q, k)) * theta ** k * (1-theta) ** (q-k)
                           * (1-p) ** k for k in range(q+1))
                check("biased_conditional_probability", miss == (1-p*theta) ** q)
            rows.append({"terminal_p": str(p), "selector_theta": str(theta),
                         "test_counts": [1, 12]})
    return rows


def compressed_window_checks():
    cases = 0
    max_span_bits = 0
    for M in range(2, 7):
        for g in (1, 3):
            for xi in (F(1), F(1, 2), F(1, 4), F(2, 3)):
                sigma = M + (M-1)*g
                for depth in range(1, 8):
                    if depth > 1:
                        previous = sigma
                        r = ceil_fraction(F(g+previous) / xi)
                        check("compressed_descendant_span", g+previous <= xi*r)
                        sigma = M*(r+g+previous)+(M-1)*g
                        upper_step = F(2*M, 1)/xi*previous+F(4*M, 1)/xi*g
                        check("compressed_step_bound", sigma <= upper_step)
                    check("compressed_total_span", sigma <= (g+1)*(F(4*M, 1)/xi)**depth)
                    cases += 1
                    max_span_bits = max(max_span_bits, sigma.bit_length())
    return {"parameter_depth_cases": cases, "max_span_bit_length": max_span_bits,
            "branching": [2, 6], "depth": [1, 7], "gaps": [1, 3],
            "relative_spans": ["1", "1/2", "1/4", "2/3"]}


def k_value(n):
    """k(n) from source label eq:rational-example, with exact integers.

    n >= 1.
    """
    inner = (n+16).bit_length()-1
    h = inner.bit_length()-1
    return 1+isqrt(h)


def rational_example_checks():
    previous_k = k_value(1)
    exponent = 0
    first_exponents = []
    for n in range(1, 20001):
        k = k_value(n)
        check("rational_gap_positive", k >= 1)
        check("rational_gap_monotone", k >= previous_k)
        old_exponent = exponent
        exponent += k
        check("rational_exponent_increment", exponent-old_exponent == k)
        previous_k = k
        if n <= 12:
            first_exponents.append(exponent)

    thresholds = []
    for h in (2, 3, 4):
        # k(n) >= h+1 iff n+16 >= 2**(2**(h*h)).
        threshold = (1 << (1 << (h*h)))-16
        check("rational_exact_threshold_before", k_value(threshold-1) == h)
        check("rational_exact_threshold_at", k_value(threshold) == h+1)
        check("rational_exact_threshold_after", k_value(threshold+1) == h+1)
        thresholds.append({"new_k": h+1, "threshold": f"2^(2^{h*h}) - 16",
                           "threshold_bit_length": threshold.bit_length()})

    # A known exponential polynomial with a polynomially weighted geometric
    # term, alternating term, and persistent zeros in an unbounded example.
    bounded = [F(1 if n % 2 == 0 else -1)+F(n, 2**n) for n in range(50)]
    # Annihilator (S+1)(S-1/2)^2 = S^3 - 3S/4 + 1/4.
    for n in range(len(bounded)-3):
        check("bounded_nonconvergent_recurrence",
              bounded[n+3]-F(3, 4)*bounded[n+1]+F(1, 4)*bounded[n] == 0)
    unbounded = [2**n*(1+(-1)**n) for n in range(40)]
    for n in range(len(unbounded)-2):
        check("unbounded_cancellation_recurrence", unbounded[n+2] == 4*unbounded[n])
    for n in range(1, len(unbounded), 2):
        check("unbounded_sequence_need_not_diverge_in_modulus", unbounded[n] == 0)

    return {"first_dyadic_exponents": first_exponents, "prefix_length": 20000,
            "exact_step_thresholds": thresholds,
            "bounded_example": "(-1)^n + n/2^n",
            "unbounded_cancellation_example": "2^n(1+(-1)^n)"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path,
                        default=Path(__file__).resolve().parent.parent / "verification" / "budget_and_examples.json")
    args = parser.parse_args()
    report = {
        "scope": "Exact finite identities, integer span bounds and example checks; no asymptotic or universal-set certification.",
        "biased_selector_cases": biased_probability_checks(),
        "compressed_windows": compressed_window_checks(),
        "examples": rational_example_checks(),
        "arithmetic": "exact rational and integer",
        "checks": CHECKS,
        "total_checks": sum(CHECKS.values()),
        "status": "passed",
    }
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "total_checks": report["total_checks"],
                      "output": args.json.name}, indent=2))


if __name__ == "__main__":
    main()
