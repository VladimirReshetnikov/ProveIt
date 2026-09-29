#!/usr/bin/env python3
"""Independently check the small cyclotomic norm certificates.

Python standard library only. This auditor reconstructs integer
multiplication matrices, checks their determinants by fraction-free
elimination, and checks that the affine orbits partition every pair set.
It does not call SymPy or trust the claimed matrix/norm/orbit size.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from itertools import combinations
from pathlib import Path
from typing import Iterable


def determinant(matrix: list[list[int]]) -> int:
    """Bareiss determinant with exact division and row pivoting."""
    n = len(matrix)
    if n == 0:
        return 1
    assert all(len(row) == n for row in matrix)
    a = [row[:] for row in matrix]
    sign, previous = 1, 1
    for k in range(n-1):
        if a[k][k] == 0:
            row = next((r for r in range(k+1, n) if a[r][k]), None)
            if row is None:
                return 0
            a[k], a[row] = a[row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                numerator = a[i][j]*pivot-a[i][k]*a[k][j]
                assert numerator % previous == 0, "Non-exact Bareiss division"
                a[i][j] = numerator // previous
            a[i][k] = 0
        previous = pivot
    return sign*a[-1][-1]


def matrix_for_pair(p: int, left: Iterable[int], right: Iterable[int]) -> list[list[int]]:
    q = [0]*p
    for i in left:
        q[i] += 1
    for i in right:
        q[i] -= 1
    matrix = [[0]*(p-1) for _ in range(p-1)]
    for column in range(p-1):
        for exponent, coefficient in enumerate(q):
            remainder = (exponent+column) % p
            if remainder == p-1:
                for row in range(p-1):
                    matrix[row][column] -= coefficient
            else:
                matrix[remainder][column] += coefficient
    return matrix


def canonical(left: Iterable[int], right: Iterable[int]):
    return tuple(sorted((tuple(sorted(left)), tuple(sorted(right)))))


def orbit(p: int, left: tuple[int, ...], right: tuple[int, ...]):
    return {canonical(((a*i+b) % p for i in left),
                      ((a*i+b) % p for i in right))
            for a in range(1, p) for b in range(p)}


def prime_divisors(n: int) -> set[int]:
    factors = set()
    d = 2
    while d*d <= n:
        while n % d == 0:
            factors.add(d)
            n //= d
        d += 1
    if n > 1:
        factors.add(n)
    return factors


def audit(path: Path) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    expected_cases = {(5, 2), (7, 2), (7, 3)}
    assert {(row["p"], row["k"]) for row in data} == expected_cases
    totals, report = 0, {}
    for p, k in sorted(expected_cases):
        rows = [r for r in data if (r["p"], r["k"]) == (p, k)]
        subsets = list(combinations(range(p), k))
        all_pairs = set(combinations(subsets, 2))
        covered = set()
        counts = Counter()
        for row in rows:
            left, right = tuple(row["A"]), tuple(row["B"])
            assert len(left) == len(right) == k
            assert tuple(sorted(set(left))) == left
            assert tuple(sorted(set(right))) == right
            assert all(0 <= i < p for i in left+right)
            assert left < right
            current = orbit(p, left, right)
            assert (left, right) == min(current)
            assert current <= all_pairs
            assert not covered.intersection(current), "Repeated affine orbit"
            assert len(current) == row["orbit_size"]
            matrix = matrix_for_pair(p, left, right)
            assert matrix == row["multiplication_matrix"]
            norm = abs(determinant(matrix))
            assert norm > 0 and norm == row["norm"]
            counts[norm] += len(current)
            covered.update(current)
        assert covered == all_pairs, "Some unordered subset pairs are missing"
        primes = sorted({l for n in counts for l in prime_divisors(n)})
        assert primes == {(5,2): [5], (7,2): [2,7], (7,3): [2,7,29]}[(p,k)]
        report[f"p{p}_k{k}"] = {"pairs": len(covered), "orbits": len(rows),
                                  "norm_multiplicities": dict(sorted(counts.items())),
                                  "prime_divisors": primes}
        totals += len(covered)
    assert len(data) == 29 and totals == 850
    return {"status": "PASS", "dependency": "Python standard library only",
            "matrices_checked": len(data), "pairs_covered": totals, "cases": report}


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O; assertions are part of the checker.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cert", type=Path,
                        default=Path("certificates/cyclotomic_norm_certificates.json"))
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()
    report = audit(args.cert)
    text = json.dumps(report, indent=2)+"\n"
    if args.out:
        args.out.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
