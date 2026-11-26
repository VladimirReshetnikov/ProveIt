#!/usr/bin/env python3
"""Enumerate positive n <= limit having no solution n=xy+yz+zx with 0<x<y<z.

Uses only exact integer arithmetic. The default limit 5,000,000 corresponds
to the absolute discriminant threshold 20,000,000 for orders of discriminant
-4n. Run 'python3 idoneal.py' to reproduce idoneal-output.txt.
"""
from argparse import ArgumentParser
from math import isqrt


def has_witness(n):
    """Exhaust the factorizations (n + x*x) = (x+y)(x+z)."""
    for x in range(1, isqrt(n // 3) + 1):
        product = n + x * x
        for a in range(2 * x + 1, isqrt(product - 1) + 1):
            if product % a == 0:
                return True
    return False


def has_equal_pair(n):
    """With two equal sides u and third side v, n-u^2 = 2uv."""
    for u in range(1, isqrt(n - 1) + 1):
        remainder = n - u * u
        if remainder % (2 * u) == 0:
            return True
    return False


def enumerate_exceptions(limit):
    remaining = bytearray([1]) * (limit + 1)
    remaining[0] = 0
    # With x+y=a and y=a-x, z=y+1,y+2,... gives one progression.
    for a in range(3, min(101, limit + 1)):
        for x in range(1, (a - 1) // 2 + 1):
            y = a - x
            first = x * y + a * (y + 1)
            if first <= limit:
                count = (limit - first) // a + 1
                remaining[first::a] = bytes(count)
    candidates = [n for n, flag in enumerate(remaining) if flag]
    exceptions = [n for n in candidates if not has_witness(n)]
    return len(candidates), exceptions


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("limit", type=int, nargs="?", default=5_000_000)
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("limit must be positive")
    count, exceptions = enumerate_exceptions(args.limit)
    print(f"Inclusive interval: 1 to {args.limit}")
    print(f"Candidates after the progression sieve: {count}")
    print(f"Exceptions after exact factorization tests: {len(exceptions)}")
    print(", ".join(map(str, exceptions)))
    unrestricted_exceptions = [n for n in exceptions if not has_equal_pair(n)]
    print(f"Exceptions when repeated coordinates are allowed: {len(unrestricted_exceptions)}")
    print(", ".join(map(str, unrestricted_exceptions)))
