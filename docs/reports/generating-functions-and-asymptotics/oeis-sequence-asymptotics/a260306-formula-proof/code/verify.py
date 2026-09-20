#!/usr/bin/env python3
"""Exact, reproducible checks for the proof of OEIS A260306.

Python 3.10+; standard library only. No network access unless --check-oeis
is supplied. All coefficient computations use exact rational arithmetic.
Finite checks supplement, but do not replace, the mathematical proof.
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json
import sys
import time
import urllib.request


def nonnegative(n: int) -> int:
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise ValueError("The index must be a nonnegative integer.")
    return n


def coefficients_recurrence(last_index: int) -> list[Fraction]:
    """c_n = delta(n,0) - 2**n*n!*h_(2n+1), using the proved recurrence."""
    nonnegative(last_index)
    h = [Fraction(1)]
    for k in range(1, 2 * last_index + 2):
        convolution = sum(
            (h[k - j] * h[j] / (j + 1) for j in range(1, k)),
            Fraction(0),
        )
        h.append((h[k - 1] / k - convolution) * Fraction(k + 1, k + 2))
    return [
        Fraction(int(n == 0)) - 2**n * factorial(n) * h[2 * n + 1]
        for n in range(last_index + 1)
    ]


def coefficient_inverse(n: int) -> Fraction:
    """Extract [z^(2n+1)] A(z)^(-n-1) by a separate power-series rule."""
    nonnegative(n)
    degree, p = 2 * n + 1, n + 1
    a = [Fraction(2, factorial(k + 2)) for k in range(degree + 1)]
    f = [Fraction(1)]
    # A*f' = -p*A'*f; A(0)=1.
    for m in range(1, degree + 1):
        value = sum(
            ((m + (p - 1) * k) * a[k] * f[m - k]
             for k in range(1, m + 1)),
            Fraction(0),
        )
        f.append(-value / m)
    return -2**n * factorial(n) * f[degree]


def stirling_table(max_m: int, max_k: int) -> list[list[int]]:
    """Ordinary Stirling numbers of the second kind."""
    nonnegative(max_m)
    nonnegative(max_k)
    table = [[0] * (max_k + 1) for _ in range(max_m + 1)]
    table[0][0] = 1
    for m in range(1, max_m + 1):
        for k in range(1, min(m, max_k) + 1):
            table[m][k] = k * table[m - 1][k] + table[m - 1][k - 1]
    return table


def associated_stirling_table(max_m: int, max_k: int) -> list[list[int]]:
    """Partitions into blocks of size at least 3; integer recurrence."""
    nonnegative(max_m)
    nonnegative(max_k)
    table = [[0] * (max_k + 1) for _ in range(max_m + 1)]
    table[0][0] = 1
    for m in range(1, max_m + 1):
        for k in range(1, min(m // 3, max_k) + 1):
            table[m][k] = k * table[m - 1][k]
            table[m][k] += comb(m - 1, 2) * table[m - 3][k - 1]
    return table


def coefficient_double(n: int, table: list[list[int]] | None = None) -> Fraction:
    """The exact double sum displayed in OEIS A260306."""
    nonnegative(n)
    M = 2 * n + 1
    if table is None:
        table = stirling_table(3 * M, M)
    fac = [factorial(k) for k in range(3 * M + 1)]
    total = Fraction(0)
    for i in range(1, M + 1):
        for j in range(1, i + 1):
            L = M + i + j
            total += Fraction(
                (-1)**(j + 1) * 2**i * table[L][j],
                fac[L] * fac[M - i] * fac[i - j] * (n + i + 1),
            )
    return 2**n * factorial(3 * n + 2) * total


def coefficient_triple(n: int) -> Fraction:
    """Literal triple sum, independent of the Stirling-number recurrence."""
    nonnegative(n)
    M = 2 * n + 1
    total = Fraction(0)
    for i in range(1, M + 1):
        for j in range(1, i + 1):
            L = M + i + j
            for k in range(1, j + 1):
                total += Fraction(
                    (-1)**(k + 1) * 2**i * k**L
                    * comb(M, i) * comb(i, j) * comb(j, k),
                    factorial(L) * (n + i + 1),
                )
    return Fraction(2**n * factorial(3 * n + 2), factorial(M)) * total


def coefficient_associated(
    n: int, table: list[list[int]] | None = None
) -> Fraction:
    """The one-sum corollary using partitions with block size >= 3."""
    nonnegative(n)
    M = 2 * n + 1
    if table is None:
        table = associated_stirling_table(3 * M, M)
    return sum(
        (Fraction(
            (-1)**(k + 1) * 2**(n + k) * factorial(n + k)
            * table[M + 2 * k][k],
            factorial(M + 2 * k),
        ) for k in range(1, M + 1)),
        Fraction(0),
    )


def fetch_bfile(url: str) -> dict[int, int]:
    """Fetch a public OEIS b-file; reject duplicate indices and malformed data."""
    request = urllib.request.Request(
        url, headers={"User-Agent": "A260306-proof-exact-verification/1.0"}
    )
    with urllib.request.urlopen(request, timeout=45) as response:
        text = response.read().decode("utf-8-sig")
    values: dict[int, int] = {}
    for line_number, line in enumerate(text.splitlines(), 1):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) != 2:
            raise ValueError(f"Malformed b-file line {line_number}: {line!r}")
        index, value = map(int, parts)
        if index in values:
            raise ValueError(f"Duplicate b-file index {index}")
        values[index] = value
    if not values:
        raise ValueError("The downloaded b-file contains no data.")
    return values


def require_equal(actual: object, expected: object, message: str) -> None:
    if actual != expected:
        raise AssertionError(f"{message}: got {actual}, expected {expected}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=117)
    parser.add_argument("--formula-max", type=int, default=20)
    parser.add_argument("--triple-max", type=int, default=10)
    parser.add_argument("--check-oeis", action="store_true")
    parser.add_argument(
        "--out-dir", type=Path, default=Path(__file__).resolve().parents[1] / "artifacts"
    )
    args = parser.parse_args()
    for value in (args.max_n, args.formula_max, args.triple_max):
        nonnegative(value)
    if max(args.formula_max, args.triple_max) > args.max_n:
        parser.error("--formula-max and --triple-max must not exceed --max-n")
    args.out_dir.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    coefficients = coefficients_recurrence(args.max_n)
    M = 2 * args.formula_max + 1
    ordinary = stirling_table(3 * M, M)
    associated = associated_stirling_table(3 * M, M)
    checks: dict[str, object] = {}
    for n in range(args.formula_max + 1):
        require_equal(coefficient_inverse(n), coefficients[n], f"inverse, n={n}")
        require_equal(coefficient_double(n, ordinary), coefficients[n], f"double, n={n}")
        require_equal(
            coefficient_associated(n, associated), coefficients[n], f"associated, n={n}"
        )
    checks["inverse_power_vs_inverse_function_recurrence"] = [0, args.formula_max]
    checks["double_sum_vs_recurrence"] = [0, args.formula_max]
    checks["associated_stirling_sum_vs_recurrence"] = [0, args.formula_max]
    for n in range(args.triple_max + 1):
        require_equal(coefficient_triple(n), coefficients[n], f"triple, n={n}")
    checks["literal_triple_sum_vs_recurrence"] = [0, args.triple_max]
    # A small fixed regression test, also printed in the article.
    expected = [Fraction(1, 3), Fraction(4, 135), Fraction(-8, 2835),
                Fraction(-16, 8505), Fraction(8992, 12629925)]
    for n, value in enumerate(expected[:len(coefficients)]):
        require_equal(coefficients[n], value, f"initial coefficient, n={n}")
    checks["fixed_initial_coefficients"] = [0, min(4, args.max_n)]
    fixture_path = Path(__file__).resolve().parents[1] / "artifacts" / "reference_prefix.json"
    fixture = json.loads(fixture_path.read_text(encoding="utf-8"))
    for accession, part in [("A260306", "numerator"), ("A065973", "denominator")]:
        reference = fixture[accession]["values"]
        count = min(len(reference), len(coefficients))
        for n in range(count):
            require_equal(getattr(coefficients[n], part), reference[n],
                          f"offline {accession}, n={n}")
        checks[f"offline_{accession}_prefix"] = {
            "checked_range_inclusive": [0, count - 1],
            "url": fixture[accession]["url"],
            "source_accessed": fixture["accessed"], "result": "all equal",
        }
    if args.check_oeis:
        for accession, part in [("A260306", "numerator"), ("A065973", "denominator")]:
            url = f"https://oeis.org/{accession}/b{accession[1:]}.txt"
            reference = fetch_bfile(url)
            # Check every requested index: no silent truncation to an intersection.
            for n, value in enumerate(coefficients):
                if n not in reference:
                    raise AssertionError(f"{accession} has no reference value at n={n}")
                require_equal(getattr(value, part), reference[n], f"{accession}, n={n}")
            checks[f"oeis_{accession}"] = {
                "url": url, "checked_range_inclusive": [0, args.max_n],
                "reference_rows_available": len(reference), "result": "all equal",
            }
    with (args.out_dir / "coefficients.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["n", "numerator", "denominator"])
        for n, value in enumerate(coefficients):
            writer.writerow([n, value.numerator, value.denominator])
    report = {
        "status": "PASS", "arithmetic": "exact fractions and integers",
        "python": sys.version.split()[0], "generated_range_inclusive": [0, args.max_n],
        "checks": checks, "elapsed_seconds": round(time.monotonic() - start, 3),
        "scope": "Finite computational checks; the article contains the all-index proof.",
    }
    (args.out_dir / "checks.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
