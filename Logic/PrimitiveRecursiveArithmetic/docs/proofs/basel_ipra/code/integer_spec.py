#!/usr/bin/env python3
"""Natural-number-only common-denominator formulation of the Basel theorem.

This evaluates instances of the mathematical theorem, not formal proofs.
No rational-number or real-number library is used in the target calculation.
"""

from __future__ import annotations
import argparse
import json


def cutoff(k: int) -> int:
    return 2 ** (2 * k + 7)


def factorial(n: int) -> int:
    result = 1
    for j in range(1, n + 1):
        result *= j
    return result


def delta(a: int, b: int) -> int:
    return max(a - b, 0) + max(b - a, 0)


def components(k: int, n: int) -> tuple[int, int, int]:
    """Return F(n), B(n), C(k,n); intended guard n >= cutoff(k)."""
    f = factorial(2 * n)
    b = sum((f // j) ** 2 for j in range(1, n + 1))
    c = sum(
        max(f // (4 * j + 1) - f // (4 * j + 3), 0)
        for j in range(cutoff(k) // 2)
    )
    return f, b, c


def check(k: int, n: int) -> bool:
    if n < cutoff(k):
        return True
    f, b, c = components(k, n)
    return 2**k * delta(6 * b, 16 * c**2) <= f**2


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--k", type=int, default=0)
    parser.add_argument("--n", type=int)
    args = parser.parse_args()
    if args.k < 0 or (args.n is not None and args.n < 0):
        parser.error("Inputs must be natural numbers.")
    n = cutoff(args.k) if args.n is None else args.n
    ok = check(args.k, n)
    print(json.dumps({
        "k": args.k, "n": n, "cutoff": cutoff(args.k),
        "target_holds": ok,
        "status": "evaluated instance, not a universal proof",
        "arithmetic": "natural numbers; factorial; bounded division; bounded sums",
    }, indent=2))
    if not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
