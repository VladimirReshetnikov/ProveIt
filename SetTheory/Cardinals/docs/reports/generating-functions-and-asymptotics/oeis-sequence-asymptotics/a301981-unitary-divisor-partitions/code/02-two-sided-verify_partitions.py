#!/usr/bin/env python3
"""Finite exact checks for A301981 and A301982.

Two independent weight algorithms and two independent coefficient algorithms
are compared. This script uses only the Python standard library. It checks
definitions and initial data; it does not prove the asymptotic oscillations.

Usage: python3 code/verify_partitions.py [--n 160] [--output PATH]
"""
import argparse
import json
from math import comb, gcd, isqrt
from pathlib import Path


PREFIX_MINUS = [
    1, 1, 4, 8, 19, 37, 84, 154, 313, 581, 1109, 2001, 3696,
    6518, 11637, 20215, 35173, 60007, 102404, 171960, 288286,
]
PREFIX_PLUS = [
    1, 1, 3, 7, 12, 26, 52, 92, 170, 310, 541, 945, 1636,
    2760, 4639, 7743, 12725, 20795, 33730, 54184, 86547,
]


def weights_by_divisors(nmax):
    """Directly enumerate d with gcd(d,n/d)=1."""
    weights = [0]
    for n in range(1, nmax + 1):
        total = 0
        for d in range(1, isqrt(n) + 1):
            if n % d == 0 and gcd(d, n // d) == 1:
                total += d
                if d * d != n:
                    total += n // d
        weights.append(total)
    return weights


def weights_by_prime_powers(nmax):
    """Factor each n and multiply (1+p^a), independently of divisor enumeration."""
    weights = [0]
    for n in range(1, nmax + 1):
        remaining, p, total = n, 2, 1
        while p * p <= remaining:
            if remaining % p == 0:
                prime_power = 1
                while remaining % p == 0:
                    remaining //= p
                    prime_power *= p
                total *= 1 + prime_power
            p += 1
        if remaining > 1:
            total *= 1 + remaining
        weights.append(total)
    return weights


def product_coefficients(weights, distinct):
    """Multiply finite binomial factors, truncating every factor to degree nmax."""
    nmax = len(weights) - 1
    coefficients = [1] + [0] * nmax
    for size in range(1, nmax + 1):
        multiplicity = weights[size]
        limit = nmax // size
        if distinct:
            limit = min(limit, multiplicity)
        factor = [
            comb(multiplicity, k) if distinct else comb(multiplicity + k - 1, k)
            for k in range(limit + 1)
        ]
        previous = coefficients
        coefficients = [0] * (nmax + 1)
        for degree, value in enumerate(previous):
            if value:
                for k in range(min(limit, (nmax - degree) // size) + 1):
                    coefficients[degree + k * size] += value * factor[k]
    return coefficients


def derivative_coefficients(weights, distinct):
    """Solve n*a_n = sum_{k=1}^n [z^k](z F'/F)*a_(n-k)."""
    nmax = len(weights) - 1
    logarithmic_derivative = [0] * (nmax + 1)
    for divisor in range(1, nmax + 1):
        for multiple in range(divisor, nmax + 1, divisor):
            quotient = multiple // divisor
            sign = -1 if distinct and quotient % 2 == 0 else 1
            logarithmic_derivative[multiple] += sign * divisor * weights[divisor]
    coefficients = [1]
    for n in range(1, nmax + 1):
        numerator = sum(
            logarithmic_derivative[k] * coefficients[n - k]
            for k in range(1, n + 1)
        )
        quotient, remainder = divmod(numerator, n)
        assert remainder == 0, (n, remainder)
        coefficients.append(quotient)
    return coefficients


def check(nmax):
    assert nmax >= 20, "nmax must be at least 20 to verify all stored OEIS terms"
    divisors = weights_by_divisors(nmax)
    factors = weights_by_prime_powers(nmax)
    assert divisors == factors, "unitary-divisor weight algorithms disagree"
    report = {
        "scope": "Finite exact definition checks; not an asymptotic proof",
        "maximum_n": nmax,
        "weights": {"independent_algorithms_agree": True},
        "sequences": {},
        "sources": ["https://oeis.org/A301981", "https://oeis.org/A301982"],
    }
    for name, distinct, prefix in [
        ("A301981", False, PREFIX_MINUS),
        ("A301982", True, PREFIX_PLUS),
    ]:
        product = product_coefficients(divisors, distinct)
        recurrence = derivative_coefficients(factors, distinct)
        assert product == recurrence, (name, "coefficient algorithms disagree")
        assert product[:len(prefix)] == prefix, (name, "OEIS prefix mismatch")
        assert all(value > 0 for value in product), (name, "nonpositive coefficient")
        report["sequences"][name] = {
            "independent_algorithms_agree": True,
            "oeis_initial_terms_checked": len(prefix),
            "positive_through_maximum_n": True,
            "last_term": str(product[-1]),
        }
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=160)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = check(args.n)
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
