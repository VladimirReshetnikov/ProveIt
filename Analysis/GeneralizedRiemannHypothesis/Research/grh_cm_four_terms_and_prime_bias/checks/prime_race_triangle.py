#!/usr/bin/env python3
"""Rational certificate that three critical-scale race vectors mod 4 surround zero."""

from fractions import Fraction
from math import isqrt

SCALE = 10**10
TERMS = 16
SAMPLES = (293, 283, 228)  # in counterclockwise order


def log_bounds_from_ratio(z):
    """Bounds for log((1+z)/(1-z)), where 0 <= z <= 1/3."""
    assert 0 <= z <= Fraction(1, 3)
    partial = sum(2 * z ** (2 * j + 1) / (2 * j + 1) for j in range(TERMS))
    remainder = 2 * z ** (2 * TERMS + 1) / ((2 * TERMS + 1) * (1 - z*z))
    return partial, partial + remainder


LOG_TWO = log_bounds_from_ratio(Fraction(1, 3))


def scaled_log_bounds(p):
    """Integer lower and upper bounds for SCALE times the natural log."""
    k = p.bit_length() - 1
    z = Fraction(p - 2**k, p + 2**k)
    lo, hi = log_bounds_from_ratio(z)
    low = SCALE * (k * LOG_TWO[0] + lo)
    high = SCALE * (k * LOG_TWO[1] + hi)
    return low.__floor__(), high.__ceil__()


def sieve_prime_powers(limit):
    primes = [True] * (limit + 1)
    for p in range(2, isqrt(limit) + 1):
        if primes[p]:
            for multiple in range(p*p, limit + 1, p):
                primes[multiple] = False
    for p in range(3, limit + 1, 2):
        if primes[p]:
            weight = scaled_log_bounds(p)
            power = p
            while power <= limit:
                yield power, weight
                power *= p


def deviation(n, powers):
    """Two interval coordinates for SCALE times psi(n;4,a)-SCALE*n/2."""
    coords = [[-n * SCALE // 2] * 2 for _ in range(2)]
    for power, (lo, hi) in powers:
        if power <= n:
            interval = coords[power % 4 // 2]
            interval[0] += lo
            interval[1] += hi
    return coords


def multiply(a, b):
    corners = [x * y for x in a for y in b]
    return min(corners), max(corners)


def determinant_lower(v, w):
    return multiply(v[0], w[1])[0] - multiply(v[1], w[0])[1]


def main():
    powers = list(sieve_prime_powers(max(SAMPLES)))
    points = [deviation(n, powers) for n in SAMPLES]
    for i, v in enumerate(points):
        j = (i + 1) % len(points)
        low = determinant_lower(v, points[j])
        assert low > 0
        # Floor in units of 1/1000, retaining entirely rational arithmetic.
        print(f"det({SAMPLES[i]}, {SAMPLES[j]}) >= {low * 1000 // SCALE**2}/1000")
    print("All three determinants are positive; the normalized triangle contains zero strictly.")


if __name__ == "__main__":
    main()
