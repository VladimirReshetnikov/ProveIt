#!/usr/bin/env python3
"""Reproduce exact checks and write the research data (standard library only).

Run from any directory: python code/verify.py
Checks are finite corroboration, not a replacement for the proofs in report.tex.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
import sys
from collections import Counter
from fractions import Fraction
from math import factorial, gcd, prod
from pathlib import Path
from time import perf_counter

from hankel_arithmetic import (
    biarithmetic_matrix, biarithmetic_product, determinant, determinant_product,
    digit_sum, factor_integer, factorial_valuation, hankel_matrix,
    hankel_ratio_sequence, hilbert_denominator, inverse_formula, denominator_valuation,
    numerator_factorization, plane_partition_polynomial, predicted_numerator,
    prime_exponent_sequence, remove_supported_primes, residue_square_count,
    residual_count, sharpness_witness, superfactorial_valuation,
    two_shift_certificate, universal_denominator, valuation,
)


def run(output: Path) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    counts: Counter[str] = Counter()
    started = perf_counter()

    def check(name: str, condition: bool, context: object = None) -> None:
        if not condition:
            raise AssertionError(f"{name} failed: {context!r}")
        counts[name] += 1

    # Independent determinant algorithm: no Cauchy formula used by elimination.
    for n in range(9):
        for m in range(1, 17):
            for a in range(1, 17):
                direct = determinant(hankel_matrix(n, m, a))
                product = determinant_product(n, m, a)
                check("matrix_vs_product", direct == product, (n, m, a))
                check("matrix_vs_numerator_theorem", direct.numerator == predicted_numerator(n, m, a), (n, m, a))

    for n in range(33):
        for m in range(1, 25):
            for a in range(1, 25):
                result = determinant_product(n, m, a)
                check("extended_product_vs_numerator", result.numerator == predicted_numerator(n, m, a), (n, m, a))
                if gcd(a, m) == 1:
                    check("universal_denominator_divides", result.denominator % universal_denominator(n, m) == 0, (n, m, a))

    # Directly enumerate the residue square and its residual part.
    for N in range(1, 31):
        for d in range(1, 41):
            brute = Counter((i + j) % d for i in range(N) for j in range(N))
            for r in range(d):
                check("residue_count", residue_square_count(N, d, r) == brute[r], (N, d, r))
                b = N % d
                check("residual_lower_bound", residual_count(d, b, r) >= max(0, 2 * b - d), (N, d, r))
            b = N % d
            check("residual_minimum_at_minus_one", residual_count(d, b, d - 1) == max(0, 2 * b - d), (N, d))

    primes = [q for q in range(2, 48) if factor_integer(q) == {q: 1}]
    for n in range(11):
        for m in range(1, 13):
            for a in range(1, 13):
                if gcd(a, m) != 1:
                    continue
                B = determinant_product(n, m, a).denominator
                for q in primes:
                    check("denominator_valuation", denominator_valuation(n, m, a, q) == valuation(B, q), (n, m, a, q))

    # Verify the inverse by multiplying matrices, without using a library inverse.
    for n in range(6):
        for m in range(1, 9):
            for a in range(1, 9):
                C, inverse = hankel_matrix(n, m, a), inverse_formula(n, m, a)
                for i in range(n + 1):
                    for j in range(n + 1):
                        entry = sum(C[i][k] * inverse[k][j] for k in range(n + 1))
                        check("inverse_identity_entry", entry == int(i == j), (n, m, a, i, j))
                        check("inverse_denominator_support", remove_supported_primes(inverse[i][j].denominator, m) == 1, (n, m, a, i, j))

    witness_rows = []
    for n in range(7):
        for m in range(1, 13):
            B = determinant_product(n, m, 1).denominator
            running_gcd = B
            candidate_primes = sorted(set(p for s in range(2 * n + 1)
                                          for p in factor_integer(1 + m * s)))
            for q in candidate_primes:
                a = sharpness_witness(n, m, q)
                W = determinant_product(n, m, a).denominator
                check("sharpness_witness", gcd(a, m) == 1 and valuation(W, q) == valuation(hilbert_denominator(n), q), (n, m, q, a))
                running_gcd = gcd(running_gcd, W)
                witness_rows.append((n, m, q, a, valuation(W, q)))
            check("finite_gcd_certificate", running_gcd == universal_denominator(n, m), (n, m))

    # Global closed form of the reduced fraction, and the noncoprime pair.
    for n in range(8):
        superfactorial = prod(factorial(k) for k in range(n + 1))
        for m in range(1, 13):
            coprime_part = remove_supported_primes(superfactorial, m)
            supported_part = superfactorial // coprime_part
            for a in range(1, 13):
                H = determinant_product(n, m, a)
                if gcd(a, m) == 1:
                    entry_product = prod((a + m * s) ** min(s + 1, 2 * n + 1 - s)
                                         for s in range(2 * n + 1))
                    check("global_closed_form",
                          H.numerator == m ** (n * (n + 1)) * supported_part ** 2
                          and entry_product % coprime_part ** 2 == 0
                          and H.denominator == entry_product // coprime_part ** 2,
                          (n, m, a))
                else:
                    g = gcd(a, m)
                    primitive = determinant_product(n, m // g, a // g)
                    shared = gcd(primitive.numerator, g ** (n + 1))
                    check("noncoprime_reduced_pair",
                          H.numerator == primitive.numerator // shared
                          and H.denominator == g ** (n + 1) * primitive.denominator // shared,
                          (n, m, a))

    # Two explicitly constructed offsets realizing the universal gcd.
    certificates = []
    for m in range(1, 21):
        for n in range(8):
            cert = two_shift_certificate(n, m)
            check("two_shift_certificate",
                  cert["gcd"] == cert["predicted_gcd"] and gcd(cert["a2"], m) == 1,
                  (n, m))
            if m in (2, 3, 4, 6, 10) and 1 <= n <= 4:
                certificates.append({key: str(value) if key.startswith("denominator") else value
                                     for key, value in cert.items()})

    # Unequal row and column steps: support bound and universal divisor.
    for m1 in range(1, 10):
        for m2 in range(1, 10):
            for a in range(1, 10):
                for n in range(5):
                    value = biarithmetic_product(n, m1, m2, a)
                    check("two_step_numerator_support",
                          remove_supported_primes(value.numerator, m1 * m2) == 1, (n, m1, m2, a))
                    check("two_step_universal_divisor",
                          value.denominator % remove_supported_primes(hilbert_denominator(n), m1 * m2) == 0,
                          (n, m1, m2, a))
                    if n <= 2:
                        direct = determinant(biarithmetic_matrix(n, m1, m2, a))
                        check("two_step_direct_determinant", direct == value, (n, m1, m2, a))

    # The published OEIS terms against independently eliminated matrices.
    published = {
        2: [1, 4, 256, 65536, 1073741824, 70368744177664, 73786976294838206464],
        3: [1, 9, 729, 4782969, 282429536481, 150094635296999121,
            6461081889226673298932241],
    }
    for p, terms in published.items():
        for n, expected in enumerate(terms):
            check("published_oeis_terms",
                  determinant(hankel_matrix(n, p, 1)).numerator == expected, (n, p))

    for n in range(7):
        for m in range(1, 9):
            for a in range(1, 9):
                H = determinant_product(n, m, a)
                reciprocal = m ** (n + 1) * hilbert_denominator(n) * plane_partition_polynomial(n + 1, Fraction(a, m) - 1)
                check("box_polynomial_identity", reciprocal == 1 / H, (n, m, a))
    for N in range(1, 9):
        for height in range(21):
            check("box_polynomial_integrality", plane_partition_polynomial(N, height).denominator == 1, (N, height))

    for p in [2, 3, 5, 7, 11, 13]:
        S = 0
        values = [prime_exponent_sequence(n, p) for n in range(513)]
        for n in range(513):
            S += digit_sum(n, p)
            check("digit_sum_formula", 2 * (p - 1) * values[n] == p * n * (n + 1) - 2 * S, (n, p))
            check("superfactorial_valuation", superfactorial_valuation(n, p) == sum(factorial_valuation(k, p) for k in range(n + 1)), (n, p))
            if n:
                previous2 = values[n - 2] if n >= 2 else 0
                check("second_difference", values[n] - 2 * values[n - 1] + previous2 == 1 + valuation(n, p), (n, p))
        # Formal coefficient extraction from L(z)/(1-z)^2.
        coefficients = [0] * 513
        d = 1
        while d <= 512:
            for multiple in range(d, 513, d):
                for n in range(multiple, 513):
                    coefficients[n] += n - multiple + 1
            d *= p
        check("lambert_series_all_coefficients", coefficients == values, p)
        for ell in range(1, 6):
            P = p ** ell
            E = prime_exponent_sequence(P - 1, p)
            check("complete_digit_block", 2 * (p - 1) * E == p * (P - 1) * P - ell * P * (p - 1), (p, ell))

    for m in range(2, 31):
        values = [1] + [predicted_numerator(n, m) for n in range(13)]  # index -1,0,...
        for n in range(1, 13):
            supported = n // remove_supported_primes(n, m)
            check("multiplicative_recurrence", values[n + 1] * values[n - 1] == values[n] ** 2 * m * m * supported * supported, (n, m))

    # Explicit boundaries of the statement.
    # Third independent evaluation route: the size-ratio recursion of eq. (Hratio).
    for m in range(1, 41):
        for a in range(1, 41):
            if gcd(a, m) != 1:
                continue
            ladder = hankel_ratio_sequence(12, m, a)
            for n, value in enumerate(ladder):
                check("ratio_recursion_vs_product", value == determinant_product(n, m, a), (n, m, a))
                check("ratio_recursion_vs_numerator_theorem",
                      value.numerator == predicted_numerator(n, m, a), (n, m, a))

    check("composite_naive_counterexample", predicted_numerator(2, 4) == 16384 and 16 ** 3 == 4096)
    check("squared_moments_counterexample", determinant([[1, Fraction(1, 4)], [Fraction(1, 4), Fraction(1, 9)]]) == Fraction(7, 144))
    check("sparse_indices_counterexample", determinant([[1, Fraction(1, 3)], [Fraction(1, 3), Fraction(1, 5)]]) == Fraction(4, 45))

    with (output / "numerators.csv").open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["n", "m", "a", "numerator", "denominator", "numerator_factorization"])
        for m in [2, 3, 4, 5, 6, 7, 10, 12]:
            for n in range(13):
                H = determinant_product(n, m)
                writer.writerow([n, m, 1, H.numerator, H.denominator, json.dumps(numerator_factorization(n, m), sort_keys=True)])
    with (output / "oeis_numerators.csv").open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["n", "matrix_size", "m", "a", "reduced_numerator"])
        for m in [2, 3, 4, 5, 6, 10, 12]:
            for n in range(36):
                writer.writerow([n, n + 1, m, 1, predicted_numerator(n, m)])
    with (output / "small_determinants.csv").open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["n", "matrix_size", "m", "a", "numerator", "denominator"])
        for m in [1, 2, 3, 4, 6, 10, 12]:
            for a in [1, 2, 3, 5]:
                for n in range(6):
                    H = determinant(hankel_matrix(n, m, a))
                    writer.writerow([n, n + 1, m, a, H.numerator, H.denominator])
    (output / "gcd_certificates.json").write_text(json.dumps(certificates, indent=2) + "\n")
    with (output / "exponents.csv").open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["n", "E_2", "E_3", "E_5", "E_7"])
        for n in range(513):
            writer.writerow([n] + [prime_exponent_sequence(n, p) for p in [2, 3, 5, 7]])
    with (output / "gcd_witnesses.csv").open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["n", "m", "q", "offset_a", "denominator_q_valuation"])
        writer.writerows(witness_rows)
    for p, label in [(2, "A122249"), (3, "A122251")]:
        with (output / f"{label}_terms.txt").open("w") as handle:
            handle.write(f"# Independently computed terms; not an OEIS-submitted b-file.\n# n numerator of det[1/({p}(i+j)+1)] for 0<=i,j<=n\n")
            for n in range(31):
                handle.write(f"{n} {predicted_numerator(n, p)}\n")

    summary = {"status": "PASS", "python": platform.python_version(),
               "arithmetic": "exact integers and fractions.Fraction; no floating-point tests",
               "checks": dict(sorted(counts.items())), "total_checks": sum(counts.values()),
               "elapsed_seconds": round(perf_counter() - started, 3),
               "limitations": "Finite verification only. No external proof-assistant verification or peer review is claimed."}
    (output / "verification.json").write_text(json.dumps(summary, indent=2) + "\n")
    (output / "verification.txt").write_text(
        "EXACT VERIFICATION: PASS\n" + "\n".join(f"{key}: {value}" for key, value in sorted(counts.items()))
        + f"\nTotal checks: {sum(counts.values())}\nPython: {platform.python_version()}\n"
        + f"Elapsed seconds: {summary['elapsed_seconds']}\n"
        + "Finite verification corroborates, but does not replace, the mathematical proofs.\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    try:
        print(json.dumps(run(args.output), indent=2))
    except (AssertionError, ValueError, OSError) as error:
        print(f"VERIFICATION FAILED: {error}", file=sys.stderr)
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()
