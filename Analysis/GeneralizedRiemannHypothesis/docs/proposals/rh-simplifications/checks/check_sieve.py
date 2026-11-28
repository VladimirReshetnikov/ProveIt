#!/usr/bin/env python3
"""Exact finite checks of the convolution and square-pair algebra in the sieve reduction."""
from fractions import Fraction
from math import isqrt


def mobius(n):
    factors = 0
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            n //= divisor
            factors += 1
            if n % divisor == 0:
                return 0
        divisor += 1
    return (-1) ** (factors + (n > 1))


def squarefree_kernel(n):
    d = isqrt(n)
    while n % (d * d) != 0:
        d -= 1
    return n // (d * d)


def legendre(n, d):
    a = pow(n, (d - 1) // 2, d)
    return -1 if a == d - 1 else a


def chi5(n):
    # Character of order four given by chi(2)=i. Integer real/imaginary parts.
    return (0, 1, 1j, -1j, -1)[n % 5]


def product_check(M, N, d):
    assert M <= N
    vals = [0] * (M * N + 1)
    products = [0] * len(vals)
    for k in range(1, M + 1):
        for n in range(1, N + 1):
            vals[k * n] += mobius(k)
            products[k * n] += (mobius(k) * chi5(k) * legendre(k, d)
                                * chi5(n) * legendre(n, d))
    assert vals[1] == 1
    assert all(vals[k] == 0 for k in range(2, M + 1))
    for k in range(1, len(vals)):
        assert products[k] == vals[k] * chi5(k) * legendre(k, d)
        assert vals[k] == sum(mobius(t) for t in range(1, M + 1)
                              if k % t == 0 and k // t <= N)
    weights = {n: Fraction(abs(vals[n]), n) for n in range(M + 1, len(vals)) if vals[n]}
    groups = {}
    for n, value in weights.items():
        h = squarefree_kernel(n)
        groups[h] = groups.get(h, 0) + value
    sum_over_pairs = sum(a * b for k, a in weights.items() for n, b in weights.items()
                         if isqrt(k * n) ** 2 == k * n)
    assert sum(v * v for v in groups.values()) == sum_over_pairs


def exponent_check():
    for beta in (Fraction(501, 1000), Fraction(2, 3), Fraction(9, 10)):
        alpha = (beta - Fraction(1, 2)) / 2
        b = alpha / 2
        sigma = Fraction(1, 2) + alpha
        c = alpha ** 2 / 2
        e = alpha ** 2 / 16
        assert Fraction(1, 2) - (1 - b) * sigma + b * (1 - sigma) == -alpha / 2
        assert -2 * b * alpha + 2 * e + 2 * b * e < -c
        assert -alpha < -c


if __name__ == '__main__':
    for M, N in ((1, 2), (3, 7), (8, 17), (11, 32)):
        for d in (7, 23, 47):
            product_check(M, N, d)
    exponent_check()
    print('Passed 12 finite convolution and square-pair checks and 3 rational exponent checks.')
