#!/usr/bin/env python3
"""Independent exact checks for the delivered Apéry Hankel data.

Run from any directory: python3 code/verify.py
Only Python's standard library is required. Output defaults to data/verification.json.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import platform
import sys
import time

from apery_exact import (apery_binomial, apery_hankel, apery_moments,
                         leading_hankel, read_table)

ROOT = Path(__file__).resolve().parents[1]


def determinant_fraction(matrix: list[list[Fraction | int]]) -> Fraction:
    """Ordinary rational Gaussian elimination, with row pivoting."""
    a = [[Fraction(x) for x in row] for row in matrix]
    n = len(a)
    determinant = Fraction(1)
    for k in range(n):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return Fraction(0)
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            determinant = -determinant
        pivot = a[k][k]
        determinant *= pivot
        for i in range(k + 1, n):
            factor = a[i][k] / pivot
            for j in range(k + 1, n):
                a[i][j] -= factor * a[k][j]
            a[i][k] = 0
    return determinant


def determinant_mod(matrix: list[list[int]], prime: int) -> int:
    """Independent Gaussian elimination over a prime field."""
    a = [[v % prime for v in row] for row in matrix]
    n = len(a)
    out = 1
    for k in range(n):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            out = -out % prime
        pivot = a[k][k]
        out = out * pivot % prime
        inverse = pow(pivot, -1, prime)
        for i in range(k + 1, n):
            factor = a[i][k] * inverse % prime
            for j in range(k + 1, n):
                a[i][j] = (a[i][j] - factor * a[k][j]) % prime
            a[i][k] = 0
    return out


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    return all(n % d for d in range(2, math.isqrt(n) + 1))


def require(condition: bool, description: str) -> None:
    # Explicit checks remain active under python -O.
    if not condition:
        raise AssertionError(description)


def verify(table_path: Path) -> dict:
    start = time.perf_counter()
    data = read_table(table_path)
    n_max = len(data) - 1
    moments = apery_moments(2 * n_max)
    counts: dict[str, int] = {}
    for n, value in enumerate(moments):
        require(value == apery_binomial(n), f"Apéry definition mismatch at {n}")
    counts["recurrence_vs_binomial_moments"] = len(moments)

    # Values displayed by OEIS A228143, revision #40, 2026-09-13.
    prefix = [1, 48, 161856, 39002646528, 674708032182398976,
              839431510934341028210638848,
              75178263784150214825106859877233852416,
              484905075185415831301477770434885768003422223597568,
              225327830550164300895512117291590826401931052058453494726924435456,
              7544971365077550026405694467600069733983243666195122776655161969325034606646263808]
    checked = min(len(prefix), len(data))
    require(data[:checked] == prefix[:checked], "OEIS displayed prefix mismatch")
    counts["oeis_displayed_prefix"] = checked

    python_max = min(40, n_max)
    require(leading_hankel(moments, python_max) == data[:python_max + 1],
            "Python/GMP fraction-free disagreement")
    counts["python_vs_delivered_exact_determinants"] = python_max + 1

    rational_max = min(12, n_max)
    for n in range(rational_max + 1):
        matrix = [[moments[i+j] for j in range(n+1)] for i in range(n+1)]
        require(determinant_fraction(matrix) == data[n], f"rational Gaussian at {n}")
    counts["rational_gaussian_determinants"] = rational_max + 1

    primes = [1000000007, 1000000009, 998244353]
    for p in primes:
        require(is_prime(p), f"invalid verification prime {p}")
    selected = sorted({n for n in [0,1,2,5,10,20,40,80,120,160,n_max] if n<=n_max})
    for n in selected:
        matrix = [[moments[i+j] for j in range(n+1)] for i in range(n+1)]
        for p in primes:
            require(determinant_mod(matrix, p) == data[n] % p,
                    f"modular mismatch at n={n}, p={p}")
    counts["modular_gaussian_determinants"] = len(primes) * len(selected)

    # Desnanot--Jacobi condensation for shifted Hankel matrices.
    shifts = [apery_hankel(16, shift=r) for r in range(6)]
    for r in range(4):
        for n in range(1, 17):
            smaller = 1 if n == 1 else shifts[r+2][n-2]
            require(shifts[r][n] * smaller ==
                    shifts[r][n-1]*shifts[r+2][n-1] - shifts[r+1][n-1]**2,
                    f"condensation mismatch {(n,r)}")
    counts["shifted_condensation_identities"] = 64

    # Cauchy determinant identity for a power-weight model, rational parameters.
    for s in [Fraction(0), Fraction(1,2), Fraction(2), Fraction(7)]:
        for n in range(8):
            matrix = [[1/(s+1+i+j) for j in range(n+1)] for i in range(n+1)]
            numerator = math.prod(math.factorial(i)**2 for i in range(n+1))
            denominator = math.prod(s+1+i+j for i in range(n+1) for j in range(n+1))
            require(determinant_fraction(matrix) == numerator / denominator,
                    f"power-weight model mismatch {(n,s)}")
    counts["cauchy_power_weight_determinants"] = 32

    for n in range(501):
        require((2*n+1)*math.comb(2*n,n)**2 <= 16**n,
                f"central-binomial bound failed at {n}")
    counts["central_binomial_inequalities"] = 501
    return {
        "status": "PASS", "python_version": platform.python_version(),
        "platform": platform.platform(), "table": str(table_path.name),
        "n_max": n_max, "last_determinant_decimal_digits": len(str(data[-1])),
        "all_delivered_determinants_positive": all(d > 0 for d in data),
        "modular_primes": primes, "modular_indices": selected,
        "checks": counts, "elapsed_seconds": round(time.perf_counter()-start, 3),
        "scope": "Finite exact checks, not a replacement for the mathematical proof."
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--table", type=Path,
                        default=ROOT / "data/determinants_0_200.txt")
    parser.add_argument("--output", type=Path,
                        default=ROOT / "data/verification.json")
    args = parser.parse_args()
    result = verify(args.table)
    text = json.dumps(result, indent=2) + "\n"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
