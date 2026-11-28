#!/usr/bin/env python3
"""Finite arithmetic checks for square-pair grouping and twist mollification.

All comparisons use integers apart from the final finite Fourier-transform
experiment, for which the script reports the largest complex residual.
"""

from cmath import exp
from fractions import Fraction
from math import gcd, isqrt, pi


def factor(n):
    factors = []
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            factors.append((p, e))
        p += 1
    if n > 1:
        factors.append((n, 1))
    return factors


def mobius(n):
    factors = factor(n)
    return 0 if any(e > 1 for _, e in factors) else (-1) ** len(factors)


def is_square(n):
    return isqrt(n) ** 2 == n


def odd(n):
    while n % 2 == 0:
        n //= 2
    return n


def jacobi(a, b):
    """Jacobi symbol computed using prime factorization and Euler's criterion."""
    assert b >= 1 and b % 2 == 1
    ans = 1
    for p, e in factor(b):
        symbol = pow(a % p, (p - 1) // 2, p)
        ans *= (-1 if symbol == p - 1 else symbol) ** e
    return ans


def square_pair_check(bound):
    pairs = {(n, m) for n in range(1, bound + 1) for m in range(1, bound + 1)
             if is_square(n * m)}
    generated = {(k * u**2, k * v**2)
                 for k in range(1, bound + 1) if mobius(k) != 0
                 for u in range(1, isqrt(bound // k) + 1)
                 for v in range(1, isqrt(bound // k) + 1)}
    assert pairs == generated

    # Odd parts, including the independent powers of 2 in each index.
    groups = {}
    for n in range(1, bound + 1):
        sf = 1
        for p, e in factor(odd(n)):
            if e % 2:
                sf *= p
        groups.setdefault(sf, []).append(n)
    odd_pairs = {(n, m) for xs in groups.values() for n in xs for m in xs}
    assert odd_pairs == {(n, m) for n in range(1, bound + 1)
                         for m in range(1, bound + 1) if is_square(odd(n * m))}
    return len(pairs), len(odd_pairs)


def gram_check():
    # Use a nontrivial integral complex coefficient sequence (a_n,b_n) and
    # denominators sharing primes, several with proper square divisors.
    indices = [1, 3, 7, 9, 15, 21, 25, 27, 33, 45, 49]
    weights = {n: ((5 * n + 1) % 9 - 4, (n**2 + 2) % 7 - 3) for n in indices}
    left = right_re = right_im = 0
    for d in range(18, 81):
        real = sum(a * jacobi(-d, n) for n, (a, b) in weights.items())
        imag = sum(b * jacobi(-d, n) for n, (a, b) in weights.items())
        left += real**2 + imag**2
    for n, (a, b) in weights.items():
        for m, (c, e) in weights.items():
            corr = sum(jacobi(-d, n*m) for d in range(18, 81))
            right_re += (a * c + b * e) * corr
            right_im += (b * c - a * e) * corr
    assert (left, 0) == (right_re, right_im)
    return left


def coefficient_checks(y, bound):
    """Coefficients of L times the reciprocal truncated at y."""
    assert bound > 2*y > 1
    terms = []
    for n in range(1, bound + 1):
        divisors = [k for k in range(1, min(n, y) + 1) if n % k == 0]
        c = sum(mobius(k) for k in divisors)
        # Independent form from the full Möbius-inversion coefficient.
        assert c == (n == 1) - sum(mobius(k) for k in range(y + 1, n + 1) if n % k == 0)
        # Verify twist factorization, also when chi(n) vanishes.
        chi = lambda j: jacobi(j, 35)
        assert chi(n) * c == sum(mobius(k) * chi(k) * chi(n // k) for k in divisors)
        terms.append(c)
    assert terms[:y] == [1] + [0] * (y - 1)
    return next(n for n, c in enumerate(terms, 1) if n > 1 and c != 0)


def smooth_product_check(cutoff, u):
    """Exact smoothed-product coefficients for a rational test cutoff.

    The analytic proof uses a smooth cutoff. This C1 piecewise polynomial
    tests just the algebraic coefficient identity and its initial gap.
    """
    assert 1 <= cutoff <= u

    def weight(n):
        if n <= u:
            return Fraction(1)
        if n >= 2 * u:
            return Fraction(0)
        t = Fraction(n - u, u)
        return 1 - 3*t**2 + 2*t**3

    limit = 2*u*cutoff
    coefficients = [Fraction(0)] * (limit + 1)
    for m in range(1, cutoff + 1):
        for n in range(1, 2*u + 1):
            coefficients[m*n] += mobius(m) * jacobi(m, 35) * jacobi(n, 35) * weight(n)
    for k in range(1, limit + 1):
        c = sum(mobius(m) * weight(k // m)
                for m in range(1, cutoff + 1) if k % m == 0)
        assert coefficients[k] == jacobi(k, 35) * c
        if k <= cutoff:
            assert c == (k == 1)
    assert coefficients[1:cutoff + 1] == [1] + [0] * (cutoff - 1)
    return limit


def gauss_check():
    # Primitive complex character mod 5 determined by chi(2)=i, times
    # the Legendre character mod 7. This product is primitive mod 35.
    base = [0, 1, 1j, -1j, -1]
    chi = lambda n: base[n % 5] * jacobi(n, 7)
    q = 35
    assert all(abs(chi(n)) == (gcd(n, q) == 1) for n in range(q))
    e = lambda a: exp((2j * pi / q) * (a % q))
    tau = sum(chi(n) * e(n) for n in range(q))
    residuals = [abs(abs(tau)**2 - q)]
    for k in range(q):
        transform = sum(chi(n) * e(k * n) for n in range(q))
        residuals.append(abs(transform - complex(chi(k)).conjugate() * tau))
    assert max(residuals) < 1e-11
    return max(residuals)


if __name__ == "__main__":
    print("Square-pair counts (full, odd parts), indices 1..96:", square_pair_check(96))
    print("Jacobi Gram identity, two integer sides:", gram_check())
    for cutoff in [4, 12, 24]:
        print(f"Mollifier cutoff {cutoff}, first nonconstant coefficient at",
              coefficient_checks(cutoff, 100))
    print("Smoothed product, Y=12 and U=20, all coefficients checked through",
          smooth_product_check(12, 20))
    print(f"Gauss transforms mod 35, maximum residual: {gauss_check():.3g}")
