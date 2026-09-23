#!/usr/bin/env python3
"""Exact finite sanity checks for surcomplex_exponential_kernels.tex.

Standard-library only. This is NOT a formal verification of the article:
no class recursion, arbitrary surreal support, or reflection theorem is tested.
Run: python3 verify.py --output verification_results.json
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Mapping

Q = Fraction
Polynomial = dict[Fraction, Fraction]
COUNTS: Counter[str] = Counter()


def check(condition: bool, group: str, detail: str = "") -> None:
    """Record a passed equality, or stop immediately at its first failure."""
    if not condition:
        raise AssertionError(f"{group}: {detail}")
    COUNTS[group] += 1


def mod_one(value: Fraction) -> Fraction:
    return value - (value.numerator // value.denominator)


@lru_cache(maxsize=None)
def residue(n: int) -> int:
    """CRT representative a_n: 1 at the 3-primary part, 0 elsewhere."""
    if n < 1:
        raise ValueError("The modulus must be a positive integer.")
    prime_part, coprime_part = 1, n
    while coprime_part % 3 == 0:
        prime_part *= 3
        coprime_part //= 3
    if prime_part == 1:
        return 0
    return (coprime_part * pow(coprime_part, -1, prime_part)) % n


def character(value: Fraction) -> Fraction:
    return mod_one(Q(value.numerator * residue(value.denominator), value.denominator))


def character_presentation(numerator: int, denominator: int) -> Fraction:
    if denominator < 1:
        raise ValueError("The denominator must be positive.")
    return mod_one(Q(numerator * residue(denominator), denominator))


@lru_cache(maxsize=None)
def binomial(exponent: Fraction, degree: int) -> Fraction:
    if degree < 0:
        return Q(0)
    answer = Q(1)
    for k in range(degree):
        answer *= (exponent - k) / (k + 1)
    return answer


def check_crt() -> dict[str, object]:
    for n in range(1, 1001):
        a = residue(n)
        check(0 <= a < n, "crt_representative_range", f"n={n}")
        for d in range(1, n + 1):
            if n % d == 0:
                check(a % d == residue(d), "crt_divisor_compatibility", f"d={d}, n={n}")

    for numerator in range(-9, 10):
        for denominator in range(1, 25):
            value = character_presentation(numerator, denominator)
            check(value == character(Q(numerator, denominator)),
                  "character_reduced_presentation")
            for factor in range(1, 10):
                check(value == character_presentation(numerator * factor, denominator * factor),
                      "character_unreduced_presentation")

    values = sorted({Q(m, n) for m in range(-7, 8) for n in range(1, 17)})
    for x in values:
        for y in values:
            check(character(x + y) == mod_one(character(x) + character(y)),
                  "character_additivity", f"x={x}, y={y}")
    for k in range(1, 65):
        check(character(Q(1, 2**k)) == 0, "two_power_tower", f"k={k}")
        check(character(Q(1, 3**k)) == Q(1, 3**k), "three_power_tower", f"k={k}")
    check(character(Q(1)) == 0, "character_integral_value")
    sample_moduli = (2, 3, 4, 6, 8, 9, 12, 18, 24, 27)
    check([residue(n) for n in sample_moduli] == [0, 1, 0, 4, 0, 1, 4, 10, 16, 1],
          "printed_crt_table")
    return {
        "residue_moduli_tested": [1, 1000],
        "rational_values_for_pairwise_additivity": len(values),
        "root_tower_depth": 64,
        "sample_residues": {str(n): residue(n) for n in sample_moduli},
    }


def composition_coefficient(r: Fraction, a: Fraction, b: Fraction, n: int) -> Fraction:
    # sigma_a sigma_b(t^r), divided by t^r; exponent character ell(r)=r.
    return sum((binomial(-r, k) * b**k * binomial(-r-k, n-k) * a**(n-k)
                for k in range(n+1)), Q(0))


def check_shifts() -> dict[str, object]:
    exponents = (Q(-5), Q(-1), Q(-1, 2), Q(0), Q(1, 3), Q(1), Q(2), Q(5, 2))
    parameters = (Q(-2), Q(-1), Q(0), Q(1, 2), Q(1), Q(3))
    order = 16
    for r in exponents:
        for a in parameters:
            for b in parameters:
                for n in range(order+1):
                    actual = composition_coefficient(r, a, b, n)
                    expected = binomial(-r, n) * (a+b)**n
                    check(actual == expected, "shift_composition_coefficients",
                          f"r={r}, a={a}, b={b}, n={n}")
            for n in range(order+1):
                check(composition_coefficient(r, a, -a, n) == (1 if n == 0 else 0),
                      "shift_inverse_coefficients")
    for r in exponents:
        for s in exponents:
            for a in parameters:
                for n in range(order+1):
                    actual = sum((binomial(-r, k) * binomial(-s, n-k) * a**n
                                  for k in range(n+1)), Q(0))
                    check(actual == binomial(-r-s, n) * a**n,
                          "shift_monomial_multiplicativity")
    for a in parameters:
        for n in range(order+1):
            expected = Q(1) if n == 0 else a if n == 1 else Q(0)
            check(binomial(Q(1), n) * a**n == expected, "omega_translation_coefficients")
    return {
        "maximum_expansion_degree": order,
        "rational_exponents": [str(r) for r in exponents],
        "shift_parameters": [str(a) for a in parameters],
        "coefficient_identity":
            "sum_k binom(-r,k)b^k binom(-r-k,n-k)a^(n-k) = binom(-r,n)(a+b)^n",
    }


def shifted(poly: Mapping[Fraction, Fraction], beta: Fraction) -> Polynomial:
    return {exponent + beta: coefficient for exponent, coefficient in poly.items() if coefficient}


def evaluate_linear(poly: Mapping[Fraction, Fraction], values: Mapping[Fraction, Fraction]) -> Fraction:
    if any(exponent <= 0 for exponent in poly):
        raise ValueError("This finite L is defined only on purely infinite monomials.")
    return sum((coefficient * values[exponent] for exponent, coefficient in poly.items()), Q(0))


def check_fresh_supports() -> dict[str, object]:
    # Finite Laurent examples, not an implementation of the class construction.
    examples: list[Polynomial] = [
        {Q(1): Q(1)},
        {Q(2): Q(1), Q(1): Q(3), Q(0): Q(-4)},
        {Q(-1): Q(1), Q(0): Q(2)},
        {Q(-3): Q(5), Q(1, 2): Q(-1)},
        {Q(5, 2): Q(7, 3), Q(-2): Q(1), Q(0): Q(-1)},
        {Q(17): Q(-3), Q(-11, 2): Q(9, 7)},
    ]
    linear_values: Polynomial = {}
    records: list[dict[str, object]] = []
    for index, poly in enumerate(examples):
        for exponent in poly:
            if exponent > 0:
                linear_values.setdefault(exponent, Q(0))
        old = dict(linear_values)
        S = set(old) | {Q(0)}
        G = set(poly) | {Q(0)}
        bound = max(s-g for s in S for g in G)
        beta = Q(bound.numerator // bound.denominator + 1)
        product = shifted(poly, beta)
        check(beta > 0 and all(g > 0 for g in product), "fresh_positive_support")
        check(all(g > s for g in set(product) | {beta} for s in S),
              "fresh_support_strict_separation")
        pivot = next(g for g, coefficient in poly.items() if g != 0 and coefficient != 0)
        check(beta+pivot != beta and poly[pivot] != 0, "fresh_rational_rank_two")
        for exponent in product:
            linear_values[exponent] = Q(0)
        linear_values[beta] = Q(0)
        linear_values[beta+pivot] = Q(1, 2) / poly[pivot]
        check(all(linear_values[e] == value for e, value in old.items()),
              "fresh_preserves_previous_assignments")
        h = {beta: Q(1)}
        check(evaluate_linear(h, linear_values) == 0, "fresh_period_witness")
        check(evaluate_linear(product, linear_values) == Q(1, 2), "fresh_nonperiod_product")
        if index == 0:
            check(evaluate_linear(poly, linear_values) == 0,
                  "two_periods_with_nonperiod_product")
        records.append({
            "input": {str(g): str(c) for g, c in sorted(poly.items())},
            "fresh_integer_exponent": str(beta),
            "L_h": "0", "L_xh": "1/2",
        })
    return {"number_of_finite_examples": len(examples), "examples": records}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    args = parser.parse_args()
    report = {
        "status": "PASS",
        "arithmetic": "Exact integers and fractions; no floating-point comparisons.",
        "limitations": [
            "Not a formal verification or a Lean proof.",
            "No claim about all surreal supports is inferred from finite examples.",
            "Class recursion, witness reflection, and novelty are not machine-checked.",
        ],
        "crt_and_character": check_crt(),
        "strong_shift_finite_coefficients": check_shifts(),
        "fresh_support_finite_instances": check_fresh_supports(),
        "check_counts": dict(sorted(COUNTS.items())),
        "total_exact_checks": sum(COUNTS.values()),
        "generated_utc": datetime.now(timezone.utc).isoformat(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {report['total_exact_checks']} exact finite checks")
    print(f"Report: {args.output.resolve()}")


if __name__ == "__main__":
    main()
