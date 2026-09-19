#!/usr/bin/env python3
"""Reproduce the exact checks and data in the research note.

Run from any directory: python3 /path/to/code/verify.py
Output is written to the sibling data/ directory. No network or dependencies.
"""
from __future__ import annotations

import csv
import json
import platform
import sys
from collections import Counter
from fractions import Fraction
from math import factorial, gcd
from pathlib import Path
from time import perf_counter

from arithmetic_hankel import (
    biarithmetic_product, denominator_valuation, factor_integer, gcd_certificate,
    hankel_direct, hankel_product, hankel_sequence, hilbert_denominator,
    inverse_formula, numerator_formula, rational_determinant, remove_primes,
    residue_tail, superfactorial_valuation, universal_denominator, valuation,
)


def require(condition: bool, message: object) -> None:
    if not condition:
        raise AssertionError(message)


def run() -> None:
    start = perf_counter()
    data = Path(__file__).resolve().parents[1] / "data"
    data.mkdir(exist_ok=True)
    counts: Counter[str] = Counter()

    # Direct determinant versus closed product AND reduced-numerator theorem.
    for d in range(1, 25):
        for b in range(1, 25):
            if gcd(d, b) != 1:
                continue
            for m in range(9):
                direct = hankel_direct(m, d, b)
                require(direct == hankel_product(m, d, b), ("product", m, d, b))
                require(direct.numerator == numerator_formula(m, d, b), ("numerator", m, d, b))
                counts["direct_primitive_determinants"] += 1
    print("Direct primitive determinants:", counts["direct_primitive_determinants"], flush=True)

    # Larger m; product-ratio evaluation does not use the numerator theorem.
    for d in range(1, 41):
        for b in range(1, 41):
            if gcd(d, b) != 1:
                continue
            for m, value in enumerate(hankel_sequence(35, d, b)):
                require(value.numerator == numerator_formula(m, d, b), ("large", m, d, b))
                require(value.denominator % universal_denominator(m, d) == 0, ("universal", m, d, b))
                counts["primitive_product_ratio_cases"] += 1
    print("Product-ratio cases:", counts["primitive_product_ratio_cases"], flush=True)

    # Removing gcd(d,b)=1: independent direct determinants test scaling.
    for d in range(1, 19):
        for b in range(1, 19):
            if gcd(d, b) == 1:
                continue
            for m in range(7):
                direct = hankel_direct(m, d, b)
                require(direct == hankel_product(m, d, b), ("nonprimitive product", m, d, b))
                require(direct.numerator == numerator_formula(m, d, b), ("nonprimitive numerator", m, d, b))
                counts["direct_nonprimitive_determinants"] += 1

    # Exhaustive residue-count lemma, including empty and incomplete blocks.
    for h in range(2, 33):
        for m in range(65):
            q, r = divmod(m, h)
            direct_counts = [0] * h
            for i in range(m):
                for j in range(m):
                    direct_counts[(i + j) % h] += 1
            factorial_count = 2 * sum(j // h for j in range(m))
            for c in range(h):
                excess = h * q + residue_tail(h, r, c)
                require(direct_counts[c] - factorial_count == excess, ("residue", h, m, c))
                require(residue_tail(h, r, c) >= max(0, 2 * r - h), ("tail bound", h, m, c))
                counts["residue_class_identities"] += 1

    # Exact denominator valuations, computed two different ways.
    primes = [p for p in range(2, 80) if factor_integer(p) == {p: 1}]
    for d in range(1, 14):
        for b in range(1, 14):
            if gcd(d, b) != 1:
                continue
            for m in range(8):
                denominator = hankel_product(m, d, b).denominator
                for p in primes:
                    require(valuation(denominator, p) == denominator_valuation(m, d, b, p), ("valuation", m, d, b, p))
                    counts["denominator_prime_valuations"] += 1
    print("Residue and local valuation identities checked.", flush=True)

    # Explicit two-shift gcd certificates, not just gcds of short prefixes.
    certificates = []
    for d in range(1, 21):
        for m in range(9):
            cert = gcd_certificate(m, d)
            require(gcd(d, cert["b2"]) == 1, ("certificate primitive", m, d))
            require(cert["gcd"] == cert["predicted_gcd"], ("gcd certificate", m, d))
            counts["two_shift_gcd_certificates"] += 1
            if d in (2, 3, 4, 6, 10) and 2 <= m <= 5:
                certificates.append({key: str(value) if key.startswith("denominator") else value for key, value in cert.items()})

    # Verify the full inverse by multiplication, not only its determinant.
    for d in range(1, 13):
        for b in range(1, 13):
            for m in range(1, 6):
                inv = inverse_formula(m, d, b)
                for i in range(m):
                    for j in range(m):
                        entry = sum(Fraction(1, b + d * (i + k)) * inv[k][j] for k in range(m))
                        require(entry == int(i == j), ("inverse", m, d, b, i, j))
                        require(remove_primes(inv[i][j].denominator, d) == 1, ("inverse support", m, d, b, i, j))
                        counts["inverse_entry_checks"] += 1
                counts["inverse_matrices"] += 1

    # Different row and column step sizes: support and universal divisor.
    for a in range(1, 10):
        for b in range(1, 10):
            for c in range(1, 10):
                for m in range(6):
                    value = biarithmetic_product(m, a, b, c)
                    require(remove_primes(value.numerator, a * b) == 1, ("bi-support", m, a, b, c))
                    require(value.denominator % remove_primes(hilbert_denominator(m), a * b) == 0, ("bi-denominator", m, a, b, c))
                    if m <= 3:
                        direct = rational_determinant([[Fraction(1, c + a * i + b * j) for j in range(m)] for i in range(m)])
                        require(direct == value, ("bi-product", m, a, b, c))
                        counts["direct_biarithmetic_determinants"] += 1
                    counts["biarithmetic_support_cases"] += 1

    # Check the logarithmic-time superfactorial valuation against factorials.
    for p in (2, 3, 5, 7, 11):
        for m in range(121):
            direct = sum(valuation(factorial(j), p) for j in range(m))
            require(direct == superfactorial_valuation(m, p), ("superfactorial", m, p))
            counts["superfactorial_valuation_checks"] += 1

    # Published initial values as an indexing/normalization regression test.
    known = {
        2: [1, 4, 256, 65536, 1073741824, 70368744177664, 73786976294838206464],
        3: [1, 9, 729, 4782969, 282429536481, 150094635296999121, 6461081889226673298932241],
    }
    for d, values in known.items():
        for n, expected in enumerate(values):
            require(hankel_direct(n + 1, d).numerator == expected, ("OEIS", n, d))
            counts["published_initial_terms"] += 1

    # Deliberately false extensions, with exact counterexamples.
    require(hankel_direct(3, 4, 1) == Fraction(16384, 52360425), "composite example")
    require(4 ** (2 * sum(k // (4 ** a) for k in range(1, 3) for a in range(3))) == 4096, "naive composite")
    require(hankel_direct(2, 2, 2) == Fraction(1, 48), "nonprimitive example")
    require(hankel_direct(3, 4, 2) == Fraction(32, 496125), "nonsquare example")
    require(rational_determinant([[Fraction(1), Fraction(1, 3)], [Fraction(1, 3), Fraction(1, 5)]]) == Fraction(4, 45), "sparse example")
    counts["false_extension_regressions"] = 5

    with (data / "oeis_numerators.csv").open("w", newline="") as file:
        writer = csv.writer(file)
        writer.writerow(["oeis_index_n", "matrix_size_m", "step_d", "reduced_numerator"])
        for d in (2, 3, 4, 5, 6, 10, 12):
            for n in range(36):
                writer.writerow([n, n + 1, d, numerator_formula(n + 1, d)])
    with (data / "small_determinants.csv").open("w", newline="") as file:
        writer = csv.writer(file)
        writer.writerow(["m", "d", "b", "numerator", "denominator"])
        for d in (1, 2, 3, 4, 6, 10, 12):
            for b in (1, 2, 3, 5):
                for m in range(6):
                    value = hankel_direct(m, d, b)
                    writer.writerow([m, d, b, value.numerator, value.denominator])
    (data / "gcd_certificates.json").write_text(json.dumps(certificates, indent=2) + "\n")
    report = {
        "status": "all checks passed", "arithmetic": "Python int and fractions.Fraction only",
        "python": platform.python_version(), "elapsed_seconds": round(perf_counter() - start, 3),
        "test_groups": dict(counts),
        "interpretation": "Finite exact tests audit the implementation; the all-parameter claims are proved in report.pdf.",
    }
    (data / "verification_summary.json").write_text(json.dumps(report, indent=2) + "\n")
    (data / "verification_summary.txt").write_text("All exact checks passed.\n\n" + "\n".join(f"{key}: {value}" for key, value in counts.items()) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    run()
