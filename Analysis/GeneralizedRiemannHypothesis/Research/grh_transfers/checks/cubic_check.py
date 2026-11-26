#!/usr/bin/env python3
"""Finite checks for the standard S3 character of X^3-X-1 (disc. -23).

Python 3 standard library only. Class counts and root checks are exact.
Displayed weighted real sums use floating point and provide illustrations.
Run: python3 cubic_check.py
"""
from bisect import bisect_right
import argparse
import math

F = (-1, -1, 0, 1)
X = (0, 1, 0)


def primes(bound):
    flags = bytearray(b"\x01") * (bound + 1)
    flags[:2] = b"\0\0"
    for p in range(2, math.isqrt(bound) + 1):
        if flags[p]:
            flags[p*p::p] = b"\0" * (1 + (bound-p*p)//p)
    return (p for p in range(2, bound+1) if flags[p])


def multiply(a, b, p):
    """Multiply modulo X^3-X-1 in characteristic p."""
    a0, a1, a2 = a
    b0, b1, b2 = b
    v3 = a1*b2 + a2*b1
    v4 = a2*b2
    return ((a0*b0+v3) % p, (a0*b1+a1*b0+v3+v4) % p,
            (a0*b2+a1*b1+a2*b0+v4) % p)


def x_power(n, p):
    power = X
    result = (1, 0, 0)
    while n:
        if n % 2:
            result = multiply(result, power, p)
        n //= 2
        power = multiply(power, power, p)
    return result


def trim(coeffs):
    while coeffs and not coeffs[-1]:
        coeffs.pop()
    return coeffs


def roots_over_extension(p, k):
    """Degree gcd(F, X^(p^k)-X), computed by polynomial division over F_p."""
    a = list(F)
    b = list(x_power(p**k, p))
    b[1] = (b[1]-1) % p
    b = trim(b)
    while b:
        inv = pow(b[-1], -1, p)
        while len(a) >= len(b):
            i = len(a)-len(b)
            scale = a[-1]*inv
            for j in range(len(b)):
                a[i+j] = (a[i+j]-scale*b[j]) % p
            trim(a)
        a, b = b, a
    return len(a)-1


def trace(root_count, k):
    """Number of fixed points of the kth power, minus one."""
    if root_count == 3:
        return 2
    if root_count == 1:
        return 2 if k % 2 == 0 else 0
    if root_count == 0:
        return 2 if k % 3 == 0 else -1
    raise ValueError("not a separable cubic cycle type")


def make_rows(bound):
    rows = []
    example_primes = {}
    for p in primes(bound):
        if p == 23:
            continue
        root_count = roots_over_extension(p, 1)
        if p <= 2000:
            brute = sum((a*a*a-a-1) % p == 0 for a in range(p))
            assert root_count == brute, (p, root_count, brute)
        if p <= 200:
            for k in range(1, 7):
                assert roots_over_extension(p, k)-1 == trace(root_count, k), (p, k)
        if p > 2:
            symbol = pow((-23) % p, (p-1)//2, p)
            assert (symbol == p-1) == (root_count == 1), p
        example_primes.setdefault(root_count, p)
        pk, k = p, 1
        while pk <= bound:
            rows.append((pk, trace(root_count, k)*math.log(p), k == 1, root_count))
            pk *= p
            k += 1
    return sorted(rows), example_primes


def interval_kernel(n, x, scale):
    # Integral of 1_(n<=t) / t^2 for t in [x,scale*x].
    return 1/max(n, x)-1/(scale*x)


def run(points, scale):
    rows, examples = make_rows(scale*max(points))
    keys = [n for n, *_ in rows]
    print("Finite tests for X^3-X-1, p=23 excluded")
    print("Smallest unramified primes by roots:", sorted(examples.items()))
    print("Exact columns: counts of primes <= x with 3, 1, 0 roots.")
    print(f"A(x): all prime powers. J(x) = -int_x^({scale}x) A(t) dt/t^2.")
    print("J_prime: same integral using only first powers.")
    print("        x    split    mixed    inert           A(x)            J(x)         J_prime")
    for x in points:
        nlo, nhi = bisect_right(keys, x), bisect_right(keys, scale*x)
        counts = {0:0, 1:0, 3:0}
        for _, _, first, root_count in rows[:nlo]:
            if first:
                counts[root_count] += 1
        a = math.fsum(v for _, v, _, _ in rows[:nlo])
        j = -math.fsum(v*interval_kernel(n, x, scale) for n, v, _, _ in rows[:nhi])
        jprime = -math.fsum(v*interval_kernel(n, x, scale) for n, v, first, _ in rows[:nhi] if first)
        # Independent finite-difference identity J(x) = S(x)-S(scale*x).
        def smoothed(y):
            return math.fsum(v*(1/n-1/y) for n, v, _, _ in rows[:bisect_right(keys,y)])
        assert math.isclose(j, smoothed(x)-smoothed(scale*x), abs_tol=5e-14)
        print(f"{x:9d} {counts[3]:8d} {counts[1]:8d} {counts[0]:8d} "
              f"{a:14.6f} {j:15.10f} {jprime:15.10f}")


def run_mod_four(points, scale):
    """Independent prime-only comparison for the odd real character mod 4."""
    data = [(p, (1 if p % 4 == 1 else -1)*math.log(p))
            for p in primes(scale*max(points)) if p != 2]
    print()
    print("Prime-only mod-4 race, chi(1)=1, chi(3)=-1, p=2 excluded")
    print("        x       J_mod4_prime      sqrt(x)*J_mod4_prime")
    for x in points:
        j = -math.fsum(v*interval_kernel(p, x, scale) for p, v in data if p <= scale*x)
        print(f"{x:9d} {j:18.10f} {math.sqrt(x)*j:24.10f}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cutoffs", nargs="*", type=int, default=[100, 1000, 10000, 100000])
    parser.add_argument("--scale", type=int, default=4, help="integer dilation >= 2")
    args = parser.parse_args()
    if args.scale < 2:
        parser.error("use a scale >= 2")
    if min(args.cutoffs) < 2:
        parser.error("use integer cutoffs >= 2")
    run(args.cutoffs, args.scale)
    run_mod_four(args.cutoffs, args.scale)
