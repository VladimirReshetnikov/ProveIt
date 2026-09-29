#!/usr/bin/env python3
"""Independent finite closure: positive Stirling sums and cubed order bounds.

Does not import the primary implementation or read its computed tables.
Uses only the Python standard library. Failures raise exceptions, even under -O.
"""
from __future__ import annotations
import argparse
import json
from math import comb, factorial, gcd
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def split(n: int) -> tuple[int, int]:
    for a in range(n // 2, 0, -1):
        if gcd(a, n - a) == 1:
            return a, n - a
    raise ValueError("n must be at least two")


def threshold(k: int) -> int:
    if k < 4:
        raise ValueError("The eventual theorem requires k >= 4.")
    h = (k // 2) * ((k + 1) // 2)
    m = h - 1 - k % 2
    c = comb(k, k // 2) * (1 + k % 2)
    b = k * k * 3**k
    ell = 0
    while 2**ell < 2 * c:
        ell += 1
    s = 4
    while 64 * b * b * m**s > c * c * h**s:
        s += 1
    u = 3
    while (k * (k - 1) * (k - 2))**(2 * u) < (2 * c)**6 * h**(3 * u):
        u += 1
    return max(7, k + 1, ell * (s + 1), u)


def run(k: int) -> dict:
    N = threshold(k)
    first = max(7, k + 1)
    powers = [k**r for r in range(N)]
    threes = [3**r for r in range(N + 2)]
    stirling = [[0] * (k + 1) for _ in range(N)]
    stirling[0][0] = 1
    for r in range(1, N):
        for j in range(1, k + 1):
            stirling[r][j] = j * stirling[r - 1][j] + stirling[r - 1][j - 1]
    chrom = [0, 0]
    products = [0, 0]
    for s in range(2, N):
        a, b = split(s)
        products.append(a * b)
        chrom.append(sum(factorial(k) // factorial(k - j) * stirling[a][j]
                         * (k - j)**b for j in range(1, k + 1)))
    divisors = [[] for _ in range(N)]
    for d in range(1, N):
        for m in range(2 * d, N, d):
            divisors[m].append(d)
    cross_values = [[] for _ in range(N)]
    same_values = [[] for _ in range(N)]
    for m in range(2, N):
        for d in divisors[m]:
            s = m // d
            cross_values[m].append((chrom[s]**d, d * products[s], d))
            cycle = (k - 1)**s + (-1)**s * (k - 1)
            same_values[m].append(cycle**d)
    comparisons = 0
    cubic_fallbacks = 0
    distinguished_equalities = 0
    for n in range(first, N):
        D = chrom[n] - products[n]
        if powers[n] - D <= powers[n - 1]:
            raise ArithmeticError(f"Minimality inference failed: {n=}, {k=}")
        for gap in (powers[n] - powers[n - 1], (k - 1)**2 * powers[n - 2] - 1):
            comparisons += 1
            if gap <= D:
                raise ArithmeticError(f"Non-mixed case not strictly excluded: {n=}, {k=}")
        for m in range(2, n + 1):
            r = n - m
            # 3^ceil(r/3) is a simple integer upper bound on 3^(r/3).
            coarse = threes[(r + 2) // 3]
            for proper, period_factor, d in cross_values[m]:
                comparisons += 1
                allowance = proper * powers[r] - D
                distinguished = m == n and d == 1
                if distinguished:
                    if allowance != period_factor:
                        raise ArithmeticError("Distinguished identity failed")
                    distinguished_equalities += 1
                elif allowance > period_factor * coarse:
                    pass
                else:
                    cubic_fallbacks += 1
                    if allowance <= 0 or allowance**3 <= period_factor**3 * threes[r]:
                        raise ArithmeticError(f"Cross-cycle inequality failed: {k=}, {n=}, {m=}, {d=}")
            for proper in same_values[m]:
                comparisons += 1
                allowance = proper * powers[r] - D
                if allowance > m * coarse:
                    continue
                cubic_fallbacks += 1
                if allowance <= 0 or allowance**3 <= m**3 * threes[r]:
                    raise ArithmeticError(f"Same-cycle inequality failed: {k=}, {n=}, {m=}")
    return dict(k=k, threshold=N, first_n=first, last_n=N-1, rows=N-first,
                comparisons=comparisons, distinguished_equalities=distinguished_equalities,
                cubic_fallbacks=cubic_fallbacks, minimality_checks=N-first,
                unexpected_equalities=0, failures=0,
                method="positive Stirling sums; gcd-scanned splits; cubed real order bound")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--k", type=int, nargs="+", default=[4, 5, 6, 7])
    parser.add_argument("--out", type=Path, default=ROOT / "results")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    reports = []
    for k in args.k:
        report = run(k)
        reports.append(report)
        print(json.dumps(report, sort_keys=True), flush=True)
    (args.out / "independent.json").write_text(json.dumps(reports, indent=2) + "\n")

if __name__ == "__main__":
    main()
