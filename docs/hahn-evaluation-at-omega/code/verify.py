#!/usr/bin/env python3
"""Exact, finite checks accompanying the Hahn evaluation article.

Python 3.9+; standard library only. No floating-point arithmetic is used.
These tests are regression checks, not a proof of an infinite identity and
not a representation or implementation of the class of surreal numbers.

This program is the union of the two check batteries written for the two
research reports merged into this one. It audits both witness series: the
square root B(x) of 1-x used for the ring obstruction, and the
nonnegative-coefficient pair H(x), G(x) used for the semiring obstruction.
It also runs both finite exponent-reversal harnesses, the randomized one and
the fixed-scale deterministic one, because they sample different cases.

Run from the archive root:
    python code/verify.py --degree 256 --trials 1000 --output results
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import random
import sys
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Sequence

Polynomial = Dict[Fraction, Fraction]
Series = List[Fraction]


class VerificationFailure(RuntimeError):
    """An exact algebraic check failed."""


def require(condition: bool, message: str) -> None:
    """Unlike assert, this check is not removed by python -O."""
    if not condition:
        raise VerificationFailure(message)


# --------------------------------------------------------------------------
# Power-series coefficients
# --------------------------------------------------------------------------

def sqrt_one_minus_coefficients(degree: int) -> Series:
    """Coefficients of B(x) from the quadratic recursion of Lemma 2.1."""
    if degree < 0:
        raise ValueError("degree must be nonnegative")
    coefficients = [Fraction(1)]
    for n in range(1, degree + 1):
        target = Fraction(-1 if n == 1 else 0)
        inner = sum((coefficients[k] * coefficients[n - k]
                     for k in range(1, n)), Fraction(0))
        coefficients.append((target - inner) / 2)
    return coefficients


def sqrt_unit(unit: Sequence[Fraction], degree: int) -> Series:
    """The unique square root with constant coefficient 1, truncated.

    This is the executable counterpart of the general unit square-root lemma:
    it accepts an arbitrary unit series rather than a fixed scaling of B.
    """
    if not unit or unit[0] != 1:
        raise ValueError("the series must have constant coefficient 1")
    root = [Fraction(1)]
    for n in range(1, degree + 1):
        target = unit[n] if n < len(unit) else Fraction(0)
        cross = sum((root[i] * root[n - i] for i in range(1, n)), Fraction(0))
        root.append((target - cross) / 2)
    return root


def binomial_coefficients(degree: int) -> Series:
    """Independent first-order recurrence for (-1)^n binom(1/2,n)."""
    result = [Fraction(1)]
    for n in range(1, degree + 1):
        result.append(result[-1] * Fraction(2 * n - 3, 2 * n))
    return result


def catalan_formula(n: int) -> Fraction:
    if n == 0:
        return Fraction(1)
    catalan = math.comb(2 * n - 2, n - 1) // n
    return -Fraction(catalan, 2 ** (2 * n - 1))


def catalan_by_convolution(count: int) -> List[int]:
    """Catalan numbers from C_0 = 1 and C_m = sum C_i C_{m-1-i}."""
    catalan = [1]
    for m in range(1, count):
        catalan.append(sum(catalan[i] * catalan[m - 1 - i] for i in range(m)))
    return catalan


def central_binomial_coefficients(degree: int) -> Series:
    """Coefficients of H(x) = (1-x)^{-1/2}, all strictly positive."""
    return [Fraction(math.comb(2 * n, n), 4 ** n) for n in range(degree + 1)]


def truncated_product(a: Sequence[Fraction], b: Sequence[Fraction],
                      degree: int) -> Series:
    return [sum((a[k] * b[n - k]
                 for k in range(max(0, n - len(b) + 1), min(n, len(a) - 1) + 1)),
                Fraction(0)) for n in range(degree + 1)]


# --------------------------------------------------------------------------
# Finite Laurent polynomials with rational exponents
# --------------------------------------------------------------------------

def clean(poly: Polynomial) -> Polynomial:
    return {exponent: coefficient for exponent, coefficient in poly.items()
            if coefficient != 0}


def add(a: Polynomial, b: Polynomial) -> Polynomial:
    out = dict(a)
    for exponent, coefficient in b.items():
        out[exponent] = out.get(exponent, Fraction(0)) + coefficient
    return clean(out)


def multiply(a: Polynomial, b: Polynomial) -> Polynomial:
    out: Polynomial = {}
    for exponent_a, coefficient_a in a.items():
        for exponent_b, coefficient_b in b.items():
            exponent = exponent_a + exponent_b
            out[exponent] = (out.get(exponent, Fraction(0))
                             + coefficient_a * coefficient_b)
    return clean(out)


def reverse_exponents(poly: Polynomial, scale: Fraction) -> Polynomial:
    if scale <= 0:
        raise ValueError("scale must be positive")
    return {-scale * exponent: coefficient for exponent, coefficient in poly.items()}


def random_polynomial(rng: random.Random) -> Polynomial:
    out: Polynomial = {}
    for _ in range(rng.randrange(0, 13)):
        exponent = Fraction(rng.randint(-24, 24), rng.randint(1, 8))
        coefficient = Fraction(rng.randint(-20, 20), rng.randint(1, 12))
        out[exponent] = out.get(exponent, Fraction(0)) + coefficient
    return clean(out)


def random_laurent(rng: random.Random) -> Polynomial:
    """The second report's generator: a different exponent and size range."""
    out: Polynomial = {}
    for _ in range(rng.randint(0, 12)):
        exponent = Fraction(rng.randint(-16, 16), rng.randint(1, 4))
        coefficient = Fraction(rng.randint(-9, 9), rng.randint(1, 7))
        out[exponent] = out.get(exponent, Fraction(0)) + coefficient
    return clean(out)


def check_reversal(a: Polynomial, c: Polynomial, scale: Fraction,
                   label: str) -> None:
    image_a, image_c = reverse_exponents(a, scale), reverse_exponents(c, scale)
    require(reverse_exponents(add(a, c), scale) == add(image_a, image_c),
            f"addition compatibility fails at {label}")
    require(reverse_exponents(multiply(a, c), scale) == multiply(image_a, image_c),
            f"multiplication compatibility fails at {label}")
    require([(-scale * e) for e in sorted(a)] == sorted(image_a, reverse=True),
            f"support orientation fails at {label}")
    target_support = [-scale * e for e in sorted(a)]
    require(all(target_support[i] > target_support[i + 1]
                for i in range(len(target_support) - 1)),
            f"support strict decrease fails at {label}")


# --------------------------------------------------------------------------
# The battery
# --------------------------------------------------------------------------

FIXED_SEED = 1729
FIXED_SCALES = (Fraction(1), Fraction(2), Fraction(3, 2))
SIGNED_LINEAR_COEFFICIENTS = [
    sign * c
    for c in (Fraction(1), Fraction(2), Fraction(3),
              Fraction(1, 2), Fraction(2, 3), Fraction(7, 5))
    for sign in (-1, 1)
]


def verify(degree: int, trials: int, seed: int, fixed_pairs: int,
           output: Path) -> dict:
    if degree < 2 or trials < 1 or fixed_pairs < 1:
        raise ValueError("degree must be >= 2; trials and fixed pairs must be >= 1")

    one = [Fraction(1)] + [Fraction(0)] * degree
    target_b = [Fraction(1), Fraction(-1)] + [Fraction(0)] * (degree - 1)

    # --- The ring witness B(x), by five independent routes. ---------------
    b = sqrt_one_minus_coefficients(degree)
    from_generic_root = sqrt_unit(target_b, degree)
    from_binomial = binomial_coefficients(degree)
    from_catalan = [catalan_formula(n) for n in range(degree + 1)]
    convolved = catalan_by_convolution(degree + 1)
    from_convolution = [Fraction(1)] + [
        -Fraction(convolved[n - 1], 2 ** (2 * n - 1)) for n in range(1, degree + 1)]
    require(b == from_generic_root == from_binomial == from_catalan
            == from_convolution,
            "coefficient formulas disagree")
    require(all(q < 0 for q in b[1:]), "a nonconstant coefficient is not negative")
    require(all(q.denominator & (q.denominator - 1) == 0 for q in b),
            "a coefficient is not dyadic")
    require(truncated_product(b, b, degree) == target_b, "square identity fails")

    # --- The semiring witnesses H(x) and G(x). ----------------------------
    h = central_binomial_coefficients(degree)
    g = [Fraction(1)] * (degree + 1)
    require(all(q > 0 for q in h), "an H coefficient is not strictly positive")
    require(truncated_product(h, h, degree) == g, "H(x)^2 = G(x) fails")
    require(truncated_product(b, h, degree) == one, "B(x)H(x) = 1 fails")
    require(truncated_product([Fraction(1), Fraction(-1)], g, degree) == one,
            "the geometric identity (1-x)G(x) = 1 fails")

    # --- Differential recurrences for both series. ------------------------
    for n in range(degree):
        require(2 * (n + 1) * b[n + 1] == (2 * n - 1) * b[n],
                f"B differential recurrence fails at degree {n}")
        require(2 * (n + 1) * h[n + 1] == (2 * n + 1) * h[n],
                f"H differential recurrence fails at degree {n}")

    # --- Catalan numbers, generated by convolution rather than a formula. -
    catalan = catalan_by_convolution(degree)
    for n in range(1, degree + 1):
        require(catalan[n - 1] == math.comb(2 * (n - 1), n - 1) // n,
                f"Catalan closed formula disagrees with the recurrence at {n - 1}")
        require(b[n] == -Fraction(catalan[n - 1], 2 ** (2 * n - 1)),
                f"Catalan expression for b_{n} fails")

    # --- Unit square roots: integer scalings of B, then arbitrary units. --
    scaled_degree = min(degree, 64)
    for multiplier in range(1, 17):
        for sign in (-1, 1):
            # B(-sign * multiplier * x)^2 = 1 + sign * multiplier * x.
            scaled = [q * (-sign * multiplier) ** n
                      for n, q in enumerate(b[:scaled_degree + 1])]
            target_scaled = ([Fraction(1), Fraction(sign * multiplier)]
                             + [Fraction(0)] * (scaled_degree - 1))
            require(truncated_product(scaled, scaled, scaled_degree) == target_scaled,
                    f"scaled square identity fails: multiplier={multiplier}, sign={sign}")
    for c in SIGNED_LINEAR_COEFFICIENTS:
        unit = [Fraction(1), c] + [Fraction(0)] * (scaled_degree - 1)
        root = sqrt_unit(unit, scaled_degree)
        require(truncated_product(root, root, scaled_degree) == unit,
                f"general unit square root fails for 1+({c})x")

    # --- Exponent reversal, randomized scales. ----------------------------
    rng = random.Random(seed)
    for trial in range(trials):
        a, c = random_polynomial(rng), random_polynomial(rng)
        scale = Fraction(rng.randint(1, 16), rng.randint(1, 16))
        check_reversal(a, c, scale, f"random trial {trial}")

    # --- Exponent reversal, fixed scales including a non-integer one. -----
    fixed_rng = random.Random(FIXED_SEED)
    for trial in range(fixed_pairs):
        a, c = random_laurent(fixed_rng), random_laurent(fixed_rng)
        for scale in FIXED_SCALES:
            check_reversal(a, c, scale, f"fixed-scale trial {trial}, scale {scale}")

    # --- Reports. ---------------------------------------------------------
    output.mkdir(parents=True, exist_ok=True)
    with (output / "coefficients.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(["n", "numerator", "denominator", "exact_fraction",
                         "h_n", "coefficient_B_squared", "coefficient_H_squared"])
        for n, q in enumerate(b):
            writer.writerow([n, q.numerator, q.denominator, str(q),
                             str(h[n]), str(target_b[n]), str(g[n])])
    report = {
        "status": "PASS",
        "arithmetic": "fractions.Fraction; exact integers and rational numbers only",
        "square_identity": f"B(x)^2 = 1-x modulo x^{degree + 1}",
        "semiring_identities": [f"H(x)^2 = G(x) modulo x^{degree + 1}",
                                f"B(x)H(x) = 1 modulo x^{degree + 1}",
                                f"(1-x)G(x) = 1 modulo x^{degree + 1}"],
        "coefficient_count": degree + 1,
        "coefficients_per_main_series": degree + 1,
        "main_modulus": f"x^{degree + 1}",
        "coefficient_formulas_compared": ["quadratic recursion",
                                          "general unit square-root recursion",
                                          "binomial recursion",
                                          "Catalan closed formula",
                                          "Catalan convolution recurrence"],
        "all_nonconstant_coefficients_negative": True,
        "all_coefficients_dyadic": True,
        "all_H_coefficients_positive": True,
        "checks": {
            "B_recursive_equals_closed_formula": "PASS",
            "B_squared_equals_one_minus_x": "PASS",
            "H_squared_equals_geometric_series": "PASS",
            "B_times_H_equals_one": "PASS",
            "geometric_identity": "PASS",
            "coefficient_signs": "PASS",
            "coefficients_dyadic": "PASS",
            "Catalan_recurrence_and_formula": "PASS",
            "both_differential_recurrences": "PASS",
            "scaled_integer_unit_squares": "PASS",
            "signed_rational_unit_square_roots": "PASS",
            "finite_exponent_reversal_addition": "PASS",
            "finite_exponent_reversal_multiplication": "PASS",
            "finite_exponent_support_orientation": "PASS",
        },
        "scaled_square_identities": 32,
        "scaled_square_degree": scaled_degree,
        "unit_square_root_checks": {
            "maximum_degree": scaled_degree,
            "linear_coefficients": [str(c) for c in SIGNED_LINEAR_COEFFICIENTS],
        },
        "sparse_rational_exponent_trials": trials,
        "checks_per_sparse_trial": ["addition", "multiplication",
                                    "support order reversal"],
        "random_seed": seed,
        "fixed_scale_reversal_checks": {
            "seed": FIXED_SEED,
            "polynomial_pairs": fixed_pairs,
            "positive_scales": [str(c) for c in FIXED_SCALES],
            "scale_pair_cases": fixed_pairs * len(FIXED_SCALES),
        },
        "limitations": [
            "Finite truncations do not prove the all-coefficient identity.",
            "Finite Laurent-polynomial checks do not prove Hahn summability.",
            "No surreal-number implementation or proof-assistant verification is used.",
            "The complete arguments are the mathematical proofs in article.pdf.",
        ],
        "scope": "Finite regression checks only; no infinite proof or surreal kernel verification."
    }
    (output / "verification.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def bounded_positive(value: str) -> int:
    result = int(value)
    if not 1 <= result <= 2048:
        raise argparse.ArgumentTypeError("choose an integer from 1 to 2048")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=bounded_positive, default=256)
    parser.add_argument("--trials", type=bounded_positive, default=1000)
    parser.add_argument("--fixed-pairs", type=bounded_positive, default=200,
                        help="Laurent-polynomial pairs for the fixed-scale harness.")
    parser.add_argument("--seed", type=int, default=20260920)
    parser.add_argument("--output", type=Path, default=Path("results"))
    args = parser.parse_args()
    try:
        report = verify(args.degree, args.trials, args.seed, args.fixed_pairs,
                        args.output)
    except (ValueError, AssertionError, OSError, VerificationFailure) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
