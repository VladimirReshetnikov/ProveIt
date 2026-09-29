#!/usr/bin/env python3
"""Exact arithmetic checks for the finite closure of binary DFAO reversal.

Standard library only. No assertions are relied on; failure raises an exception.
The infinite theorem is proved in article.tex, not inferred from these checks.
"""
from __future__ import annotations
import argparse
import csv
import json
from math import comb, factorial
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]


def nearest_split(n: int) -> tuple[int, int]:
    if n < 2:
        raise ValueError("The component must contain at least two vertices.")
    if n == 2:
        return 1, 1
    if n % 2:
        return n // 2, n // 2 + 1
    delta = 1 if n % 4 == 0 else 2
    return n // 2 - delta, n // 2 + delta


def chromatic(a: int, b: int, k: int) -> int:
    """P(K_{a,b}, k), using the signed disjoint-palette formula."""
    if min(a, b, k) < 0:
        raise ValueError("Arguments must be nonnegative.")
    if a == 0 or b == 0:
        return k ** (a + b)
    f = factorial(k)
    return sum(
        (-1) ** (k - i - j)
        * (f // (factorial(i) * factorial(j) * factorial(k - i - j)))
        * i**a * j**b
        for i in range(1, k)
        for j in range(1, k - i + 1)
    )


def integer_cube_root(n: int) -> int:
    if n < 0:
        raise ValueError("Argument must be nonnegative.")
    lo, hi = 0, 1 << ((n.bit_length() + 2) // 3)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**3 <= n:
            lo = mid
        else:
            hi = mid
    return lo


def parameters(k: int) -> dict[str, int]:
    if k < 4:
        raise ValueError("The eventual theorem requires k >= 4.")
    H = k * k // 4
    M = H - (1 if k % 2 == 0 else 2)
    C = comb(k, k // 2) * (1 if k % 2 == 0 else 2)
    B = k * k * 3**k
    L = (2 * C - 1).bit_length()
    S = 4
    left, right = 64 * B * B * M**S, C * C * H**S
    while left > right:
        S += 1
        left *= M
        right *= H
    K = k * (k - 1) * (k - 2)
    U = 3
    left, right = K**(2 * U), (2 * C)**6 * H**(3 * U)
    while left < right:
        U += 1
        left *= K * K
        right *= H**3
    N = max(k + 1, 7, L * (S + 1), U)
    if N > 3 * k**4:
        raise ArithmeticError("The advertised coarse threshold failed.")
    return dict(k=k, H=H, M=M, C=C, B=B, L=L, S=S, U=U, N=N)


def close_finite_range(k: int, out_dir: Path) -> dict[str, Any]:
    p = parameters(k)
    end = p["N"] - 1
    first = max(7, k + 1)
    kp = [k**r for r in range(end + 1)]
    residual_order = [integer_cube_root(3**r) for r in range(end + 1)]
    cp = [0, 0] + [chromatic(*nearest_split(s), k) for s in range(2, end + 1)]
    cycle_options: list[list[tuple[int, int]]] = [[] for _ in range(end + 1)]
    for ell in range(2, end + 1):
        c = (k - 1)**ell + (-1)**ell * (k - 1)
        power = 1
        for d in range(1, end // ell + 1):
            power *= c
            cycle_options[d * ell].append((ell, power))
    rows = []
    count = 0
    equalities = 0
    for n in range(first, end + 1):
        a, b = nearest_split(n)
        target_gap = cp[n] - a * b
        checks = 0
        margin = None
        closest = ""

        def record(gap: int, case: str, distinguished: bool = False) -> None:
            nonlocal count, checks, margin, closest, equalities
            checks += 1
            count += 1
            difference = gap - target_gap
            if difference < 0:
                raise ArithmeticError(f"Counterexample: k={k}, n={n}, {case}")
            if difference == 0:
                equalities += 1
                if not distinguished:
                    raise ArithmeticError(f"Unexpected equality: k={k}, n={n}, {case}")
            if not distinguished and (margin is None or difference < margin):
                margin, closest = difference, case

        record(kp[n] - kp[n - 1], "two permutations")
        record((k - 1)**2 * kp[n - 2] - 1, "two singular maps")
        for s in range(2, n + 1):
            u, v = nearest_split(s)
            power = 1
            for d in range(1, n // s + 1):
                power *= cp[s]
                r = n - d * s
                gap = power * kp[r] - d * u * v * residual_order[r]
                record(gap, f"bicliques:s={s},d={d},r={r}", s == n and d == 1)
        for m in range(2, n + 1):
            r = n - m
            for ell, power in cycle_options[m]:
                record(power * kp[r] - m * residual_order[r],
                       f"cycles:m={m},length={ell},r={r}")
        rows.append(dict(n=n, k=k, a=a, b=b, comparisons=checks,
                         target_gap=str(target_gap), strict_margin=str(margin),
                         closest_excluded_case=closest))
    out_dir.mkdir(parents=True, exist_ok=True)
    with (out_dir / f"finite_k{k}.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    report = dict(parameters=p, first_n=first, last_n=end, rows=len(rows),
                  comparisons=count, distinguished_equalities=equalities,
                  unexpected_equalities=0, failures=0,
                  minimum_strict_margin=min(int(row["strict_margin"]) for row in rows))
    (out_dir / f"primary_k{k}.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--k", type=int, nargs="+", default=[4, 5, 6, 7])
    parser.add_argument("--out", type=Path, default=ROOT / "results")
    args = parser.parse_args()
    for k in args.k:
        print(json.dumps(close_finite_range(k, args.out), sort_keys=True), flush=True)
    threshold_rows = [parameters(k) for k in range(4, 17)]
    (args.out / "thresholds.json").write_text(json.dumps(threshold_rows, indent=2) + "\n")

if __name__ == "__main__":
    main()
