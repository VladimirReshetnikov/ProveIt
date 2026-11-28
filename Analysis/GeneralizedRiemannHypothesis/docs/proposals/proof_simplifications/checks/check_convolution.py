#!/usr/bin/env python3
"""Exact finite checks of a truncated Dirichlet polynomial and its Möbius factor.

Uses the order-four character modulo 5 induced to modulus 80. Tests both
balanced and unbalanced sharp cutoffs. Gaussian-integer pairs and a common
integer denominator evaluate the polynomials at s=1 without roundoff.
"""
from math import gcd, isqrt, lcm


def add(z, w):
    return z[0] + w[0], z[1] + w[1]


def multiply(z, w):
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def scale(t, z):
    return t * z[0], t * z[1]


def gaussian_sum(terms):
    total = (0, 0)
    for term in terms:
        total = add(total, term)
    return total


def factor(n):
    factors = []
    p = 2
    while p * p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            factors.append((p, exponent))
        p += 1
    if n > 1:
        factors.append((n, 1))
    return factors


def mobius(n):
    factors = factor(n)
    if any(e > 1 for _, e in factors):
        return 0
    return (-1) ** len(factors)


def kernel(n):
    k = 1
    for p, e in factor(n):
        if e % 2:
            k *= p
    return k


def psi(n):
    if gcd(n, 80) > 1:
        return (0, 0)
    return {1: (1, 0), 2: (0, 1), 3: (0, -1), 4: (-1, 0)}[n % 5]


def legendre(n, d):
    u = pow(n, (d - 1) // 2, d)
    return -1 if u == d - 1 else u


def check(length, mollifier_length, d):
    assert not any(d % p == 0 for p in range(2, isqrt(d) + 1))
    limit = length * mollifier_length
    assert isqrt(limit) < d
    denominator = lcm(*range(1, max(length, mollifier_length) + 1))
    denominator_sq = denominator * denominator

    def xi(n):
        return scale(legendre(n, d), psi(n))

    p_value = gaussian_sum(scale(denominator // n, xi(n)) for n in range(1, length + 1))
    m_value = gaussian_sum(scale(mobius(n) * (denominator // n), xi(n))
                           for n in range(1, mollifier_length + 1))
    direct_product = multiply(p_value, m_value)
    full = (0, 0)
    by_kernel = {}
    for n in range(1, limit + 1):
        coefficient = sum(mobius(j) for j in range(1, mollifier_length + 1)
                          if n % j == 0 and n // j <= length)
        if n <= min(length, mollifier_length):
            assert coefficient == int(n == 1)
        k = kernel(n)
        r = isqrt(n // k)
        assert k * r * r == n and r < d
        assert legendre(n, d) == legendre(k, d)
        if coefficient == 0:
            continue
        assert denominator_sq % n == 0
        term = scale(coefficient * (denominator_sq // n), psi(n))
        full = add(full, scale(legendre(n, d), term))
        by_kernel[k] = add(by_kernel.get(k, (0, 0)), term)
    grouped = gaussian_sum(scale(legendre(k, d), term) for k, term in by_kernel.items())
    assert direct_product == full == grouped


if __name__ == '__main__':
    cutoffs = [(6, 6), (8, 8), (11, 11), (20, 7), (64, 9), (117, 12)]
    primes = (71, 79, 103, 127)
    for lengths in cutoffs:
        for d in primes:
            check(*lengths, d)
    print(f'{len(cutoffs) * len(primes)} exact polynomial-product and square-kernel checks passed.')
