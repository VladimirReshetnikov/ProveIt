#!/usr/bin/env python3
"""Exact arithmetic for smallest perfect-power tetration bases.

All routines use Python's standard library. No power tower is constructed.
See article.tex for the proof of minimum_root, not just numerical evidence.
"""
from __future__ import annotations
import argparse
import csv
import sys
from pathlib import Path


def _positive_int(n: int, name: str) -> None:
    if isinstance(n, bool) or not isinstance(n, int) or n < 1:
        raise ValueError(f"{name} must be a positive integer")


def valuation(n: int, p: int) -> int:
    """Exponent of p in nonzero n; callers use the primes 2 or 5."""
    if not isinstance(n, int) or n == 0:
        raise ValueError("valuation requires a nonzero integer")
    if not isinstance(p, int) or p < 2:
        raise ValueError("p must be an integer at least 2")
    n = abs(n)
    if p == 2:
        return (n & -n).bit_length() - 1
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def c2(x: int) -> int:
    _positive_int(x, "x")
    if x < 3 or x % 2 == 0:
        raise ValueError("c2 requires an odd integer x > 1")
    return valuation(x - 1, 2) + valuation(x + 1, 2) - 1


def c5(x: int) -> int:
    _positive_int(x, "x")
    if x == 1 or x % 5 == 0:
        raise ValueError("c5 requires x > 1, not divisible by 5")
    if x % 5 == 1:
        return valuation(x - 1, 5)
    if x % 5 == 4:
        return valuation(x + 1, 5)
    return valuation(x * x + 1, 5)


def speed(x: int) -> int:
    """Eventual decimal congruence speed of integer tetration base x."""
    _positive_int(x, "x")
    if x == 1:
        return 0
    if x % 10 == 0:
        raise ValueError("multiples of 10 do not have a finite constant speed")
    if x % 2 == 0:
        return c5(x)
    if x % 5 == 0:
        return c2(x)
    return min(c2(x), c5(x))


def speed_of_power(x: int, exponent: int) -> int:
    """Compute V(x**exponent) without constructing x**exponent."""
    _positive_int(x, "x")
    _positive_int(exponent, "exponent")
    if x == 1:
        return 0
    if x % 10 == 0:
        raise ValueError("x must not be divisible by 10")
    u2, u5 = valuation(exponent, 2), valuation(exponent, 5)
    if x % 2 == 0:
        return c5(x) + u5
    if x % 5 == 0:
        return c2(x) + u2
    return min(c2(x) + u2, c5(x) + u5)


def restricted_minimum(s: int) -> int:
    """Smallest odd multiple of 5 with c2(x)=s, for s >= 2."""
    _positive_int(s, "s")
    if s < 2:
        raise ValueError("s must be at least 2")
    coefficient = 3 if s % 2 else 1
    sign = -1 if s % 4 in (0, 1) else 1
    return coefficient * (1 << s) + sign


def minimum_root(n: int) -> int:
    """Smallest x>1, 10 not dividing x, with V(x**n)=n (proved)."""
    _positive_int(n, "n")
    if n == 1:
        return 2
    if n == 2:
        return 7
    return restricted_minimum(n - valuation(n, 2))


def rho(n: int) -> int:
    """Smallest n-th perfect power >1 with decimal tetration speed n."""
    return pow(minimum_root(n), n)


def strict_minimum_root(n: int) -> int:
    """Minimum root when the resulting power must have maximal degree n."""
    _positive_int(n, "n")
    return 55 if n == 3 else minimum_root(n)


def strict_rho(n: int) -> int:
    """Minimum of maximal perfect-power degree exactly n and speed n."""
    return pow(strict_minimum_root(n), n)


def idempotent_tail(digits: int) -> int:
    """E_d: 0 modulo 5**d and 1 modulo 2**d, in [0,10**d)."""
    _positive_int(digits, "digits")
    five, two = 5 ** digits, 1 << digits
    return five * pow(five, -1, two)


def predicted_tail(n: int, digits: int) -> int:
    _positive_int(n, "n")
    _positive_int(digits, "digits")
    if n < 3 or digits > n:
        raise ValueError("requires n >= 3 and 1 <= digits <= n")
    sign = -1 if n % 4 == 1 else 1
    return (sign * idempotent_tail(digits)) % (10 ** digits)


def minus_one_roots5(t: int) -> tuple[int, int]:
    """The two roots of z**2=-1 modulo 5**t, by exact Hensel lifting."""
    _positive_int(t, "t")
    r, modulus = 2, 5
    for _ in range(1, t):
        quotient = (r * r + 1) // modulus
        j = (-quotient * pow(2 * r, -1, 5)) % 5
        r += j * modulus
        modulus *= 5
    return tuple(sorted((r, modulus - r)))


def nonfive_lower_bound(t: int) -> int:
    """Exact minimum x>1 with 5 not dividing x and c5(x) >= t."""
    _positive_int(t, "t")
    r, _ = minus_one_roots5(t)
    return min(r, 5 ** t - 1)


def write_root_table(path: Path, count: int) -> None:
    _positive_int(count, "count")
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["n", "v2_n", "v5_n", "s", "t", "minimum_root", "speed"])
        for n in range(1, count + 1):
            r = minimum_root(n)
            w.writerow([n, valuation(n, 2), valuation(n, 5),
                        n - valuation(n, 2), n - valuation(n, 5), r,
                        speed_of_power(r, n)])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="?", help="index n")
    parser.add_argument("--root-only", action="store_true")
    parser.add_argument("--strict", action="store_true", help="maximal perfect-power degree exactly n")
    parser.add_argument("--digits", type=int, help="compute only last d digits")
    parser.add_argument("--table", type=Path, help="CSV destination")
    parser.add_argument("--count", type=int, default=100)
    args = parser.parse_args()
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    if args.table:
        write_root_table(args.table, args.count)
    elif args.n is not None:
        if args.digits is not None:
            _positive_int(args.digits, "digits")
            root = strict_minimum_root(args.n) if args.strict else minimum_root(args.n)
            value = pow(root, args.n, 10 ** args.digits)
            print(str(value).zfill(args.digits))
        else:
            root = strict_minimum_root(args.n) if args.strict else minimum_root(args.n)
            print(root if args.root_only else pow(root, args.n))
    else:
        parser.error("provide n or --table")


if __name__ == "__main__":
    main()
