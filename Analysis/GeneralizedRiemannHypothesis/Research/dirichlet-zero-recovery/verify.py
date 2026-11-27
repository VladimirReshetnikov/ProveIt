#!/usr/bin/env python3
"""Finite checks for the zero-measure recovery theorem, using the standard library.

Run with Python 3.9 or later. Numerical quadrature and roundoff checks only
illustrate the explicit formula. They do not certify any L-function zeros,
infinite products, or exponential-moment estimates.
"""
import cmath
import itertools
import math
from fractions import Fraction

UNITS = (1, 2, 3, 4)
CHI = {1: 1 + 0j, 2: 1j, 3: -1j, 4: -1 + 0j}


def sieve(limit):
    prime = bytearray([1]) * (limit + 1)
    prime[:2] = b"\x00\x00"
    for n in range(2, math.isqrt(limit) + 1):
        if prime[n]:
            prime[n*n::n] = bytes(1 + (limit - n*n) // n)
    return [n for n in range(2, limit + 1) if prime[n]]


def multiplier(x):
    return (math.exp(-x * math.sinh(x)) * math.sin(math.pi * math.exp(x))
            * math.sin(math.pi * math.exp(-x)))


def check_regularized_multiplier():
    # U_0(iy) = exp(y sin y) |S(exp(iy))|^2. Check its continuous
    # endpoint values as well as interior samples. Strict positivity on
    # the entire interval is proved in the paper, independently of the grid.
    def regularized_sine(w):
        return math.pi if w == 1 else cmath.sin(math.pi*w)/(1-w)

    samples = []
    for j in range(-128, 129):
        y = math.pi*j/256
        samples.append(math.exp(y*math.sin(y)) *
                       abs(regularized_sine(cmath.exp(1j*y)))**2)
    assert min(samples) > 0
    assert abs(samples[128]-math.pi**2) < 1e-13
    assert abs(samples[-1] - math.exp(math.pi/2)*math.sinh(math.pi)**2/2) < 1e-11
    for n in range(2, 33):
        assert abs(regularized_sine(n)) < 1e-13
    print("Regularized U_0: positive Laplace samples on the closed critical interval;")
    print("its value at zero is pi^2, and integer factors vanish for n=2,...,32.")


def cosine_samples():
    # f(t) = pi^(-1) integral_0^infty F(x) cos(xt) dx.
    # On the real axis |F(x)| <= exp(-x sinh x); the tail at x=4 is tiny.
    values = []
    for panels in (2048, 4096):
        step = 4 / panels
        grid = [k * step for k in range(panels + 1)]
        weights = [step / (3 * math.pi) *
                   (1 if k in (0, panels) else (4 if k % 2 else 2)) *
                   multiplier(x) for k, x in enumerate(grid)]
        values.append([math.fsum(w * math.cos(x * t)
                                 for x, w in zip(grid, weights))
                       for t in (0, 2, 4, 6, 8, 10)])
    assert max(abs(a-b) for a, b in zip(*values)) < 1e-12
    assert min(values[-1]) < 0 < max(values[-1])
    return values[-1]


def log_blaschke(p, target):
    if p == target:
        return -math.inf
    return math.log(abs((p - target) / (p + target)))


def finite_product(primes, limit, residue, t):
    """Two frequency signs with a and a^(-1) mod 5; factors can overlap in p."""
    total = []
    inverse = pow(residue, -1, 5)
    for p in itertools.takewhile(lambda p: p <= limit, primes):
        if p % 5 == residue:
            total.append(log_blaschke(p, math.exp(t)))
        if p % 5 == inverse:
            total.append(log_blaschke(p, math.exp(-t)))
    return math.exp(math.fsum(total))


def laurent_product(first, second):
    terms = {}
    for i, a in first.items():
        for j, b in second.items():
            terms[i+j] = terms.get(i+j, 0) + a*b
    return {k: v for k, v in terms.items() if v}


def rational_interpolation_check():
    # A constant row F=1. The prime p=2 contributes the positive node
    # tanh(log(2)/2)=1/3; p=3 gives the negative node -1/2.
    nodes = (Fraction(1, 3), Fraction(-1, 2))

    def blaschke(w):
        return math.prod((w-s)/(1-s*w) for s in nodes)

    derivatives = {s: 1 / (1-s*s) * math.prod(
        (s-r)/(1-r*s) for r in nodes if r != s) for s in nodes}
    for w in (Fraction(0), Fraction(1, 5), Fraction(-2, 7)):
        interpolant = sum(blaschke(w) / (derivatives[s] * (w-s))
                          for s in nodes)
        assert 1-interpolant == blaschke(0)*blaschke(w)
        assert (1-interpolant)**2 * (1-w*w) <= blaschke(w)**2
    print("Exact constant-row disk interpolation at three rational test points.")


def main():
    print("Modulo 5 quartic characters, shifts, and finite-prime factors")
    for a in UNITS:
        for b in UNITS:
            assert CHI[a*b % 5] == CHI[a]*CHI[b]
    assert CHI[4] == -1 and CHI[2] != CHI[2].conjugate()
    columns = [[CHI[a], CHI[a].conjugate()] for a in UNITS]
    gram = [[sum(row[i].conjugate()*row[j] for row in columns) / 4
             for j in range(2)] for i in range(2)]
    assert gram == [[1, 0], [0, 1]]
    print("Both characters odd; normalized two-column Gram matrix is I_2.")

    # Test how a shift contributes to a character row at log p. With the
    # negative-exponent transform, the positive-frequency atom uses bar(chi).
    shifts = ((Fraction(1, 3), 2), (Fraction(-2, 5), 1))
    primes = sieve(100000)
    for p in (2, 3, 7, 11, 13, 17):
        for tau, weight in shifts:
            direct = weight * cmath.exp(-1j * float(tau)*math.log(p))
            assert abs(direct - weight * p**(-1j*float(tau))) < 1e-12
    print("Finite shifts agree with the prime phases p^(-i*tau).")
    print("Both frequency signs, a=2 and a^(-1)=3 (mod 5):")
    print("     X         B_X(0)       B_X(log(3/2))")
    last = (1, 1)
    for limit in (10, 100, 1000, 10000, 100000):
        values = tuple(finite_product(primes, limit, 2, t)
                       for t in (0, math.log(1.5)))
        assert all(0 < v < u for u, v in zip(last, values))
        print(f"{limit:6d}     {values[0]:.8f}       {values[1]:.8f}")
        last = values

    rational_interpolation_check()
    check_regularized_multiplier()

    for n in range(1, 65):
        assert abs(multiplier(math.log(n))) < 1e-14
        assert abs(multiplier(-math.log(n))) < 1e-14
    assert abs(multiplier(math.log(1.5))) > 0.5
    print("F(+/-log n) checked for 1 <= n <= 64; F(log(3/2)) is nonzero.")
    print("Inverse cosine integrals (two-grid agreement at 1e-12):")
    for t, value in zip((0, 2, 4, 6, 8, 10), cosine_samples()):
        print(f"f({t:2d}) = {value:+.10f}")

    # Independently multiply the two Laurent polynomials in x = exp(z).
    h = {0: 2, 1: 1, -1: 1}
    left = laurent_product(h, {0: 1, -1: -1})
    right = laurent_product({1: 1, 0: 1}, {0: 1, -2: -1})
    assert left == right == {1: 1, 0: 1, -1: -1, -2: -1}
    print("Exact Laurent identity: H(z)(1-e^-z)=(e^z+1)(1-e^(-2z)).")
    print("Finite checks passed.")


if __name__ == "__main__":
    main()
