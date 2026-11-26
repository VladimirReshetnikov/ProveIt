#!/usr/bin/env python3
"""Verify the C8 Fourier coefficients and rational-prime classes for D=-95."""
from argparse import ArgumentParser
from fractions import Fraction
from math import isqrt


def add(p, q):
    return (p[0] + q[0], p[1] + q[1])


def mul(p, q):
    """Multiply coefficients in Q(sqrt(2))."""
    return (p[0]*q[0] + 2*p[1]*q[1], p[0]*q[1] + p[1]*q[0])


def scale(p, k):
    return (p[0]*k, p[1]*k)


def fourier(weight):
    """Inversion symmetry kills the imaginary part."""
    assert all(weight[j] == weight[-j] for j in range(8))
    half = Fraction(1, 2)
    cosine = [(1, 0), (0, half), (0, 0), (0, -half),
              (-1, 0), (0, -half), (0, 0), (0, half)]
    result = []
    for k in range(8):
        total = (0, 0)
        for j in range(8):
            total = add(total, mul(weight[j], cosine[(j*k) % 8]))
        result.append(scale(total, Fraction(1, 8)))
    return result


def primes_to(limit):
    prime = bytearray(b'\x01') * (limit + 1)
    prime[:2] = b'\x00\x00'
    for n in range(2, isqrt(limit) + 1):
        if prime[n]:
            prime[n*n::n] = bytes((limit - n*n)//n + 1)
    return {n for n in range(2, limit+1) if prime[n]}


def represented_primes(form, primes, limit):
    a, b, c = form
    assert b*b - 4*a*c == -95
    values = set()
    # 4aQ = (2ax+by)^2 + 95y^2, and (x,y) and (-x,-y) have the same norm.
    for y in range(isqrt(4*a*limit//95) + 1):
        cap = isqrt(4*a*limit - 95*y*y)
        x_min = -((cap + b*y)//(2*a))
        x_max = (cap - b*y)//(2*a)
        for x in range(x_min, x_max + 1):
            value = a*x*x + b*x*y + c*y*y
            if value in primes:
                values.add(value)
    return values


def main(limit):
    half = Fraction(1, 2)
    zero = (0, 0)
    weight = [zero, zero, (half, 0), (0, half), (1, 0), (0, half), (half, 0), zero]
    expected = [(Fraction(1, 4), Fraction(1, 8)), (-Fraction(1, 4), 0), zero, zero,
                (Fraction(1, 4), -Fraction(1, 8)), zero, zero, (-Fraction(1, 4), 0)]
    assert fourier(weight) == expected
    print('Checked all eight Fourier coefficients exactly in Q(sqrt(2)).')
    patterns = 0
    for mask in range(32):
        indicator = [((mask >> min(j, 8-j)) & 1, 0) for j in range(8)]
        coeffs = fourier(indicator)
        assert (coeffs[1] == zero) == (coeffs[3] == zero)
        patterns += 1
    print(f'Checked the order-eight orbit obstruction on all {patterns} symmetric indicators.')
    primes = primes_to(limit) - {5, 19}
    split = {p for p in primes if p == 2 or pow(-95, (p-1)//2, p) == 1}
    classes = [(1, 1, 24), (2, 1, 12), (4, 1, 6), (3, 1, 8), (5, 5, 6)]
    counted = set()
    for j, form in enumerate(classes):
        matches = represented_primes(form, primes, limit)
        assert not counted.intersection(matches)
        counted.update(matches)
        print(f'Exponents ±{j}, {form}: {len(matches)} primes; first five {sorted(matches)[:5]}')
    assert counted == split
    print(f'All {len(split)} unramified split primes up to {limit} partitioned exactly.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('limit', type=int, nargs='?', default=100000)
    args = parser.parse_args()
    if args.limit < 2:
        parser.error('limit must be at least 2')
    main(args.limit)
