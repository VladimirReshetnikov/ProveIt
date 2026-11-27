#!/usr/bin/env python3
"""Rational enclosures for the first three Li coefficients and spectral moments.

Usage: python moment_constants.py
Import moment_constants() to obtain (C, tau, M2), each as an interval with
fractions.Fraction endpoints .lo and .hi. No external packages are needed.
"""

from fractions import Fraction as F
from functools import cache
from math import factorial

from constants_verify import Bounds, atan_reciprocal, interval, log_point, outward


BERNOULLI = (F(1, 6), F(-1, 30), F(1, 42), F(-1, 30))


def power(value, exponent):
    result = interval(1)
    for _ in range(exponent):
        result *= value
    return result


def log_derivative(order, degree, n, log_n):
    """The order-th derivative of (log x)^degree / x at x=n."""
    harmonic = sum((F(1, j) for j in range(1, order+1)), F(0))
    harmonic2 = sum((F(1, j*j) for j in range(1, order+1)), F(0))
    shifted = log_n - harmonic
    factors = (interval(1), shifted, shifted*shifted-harmonic2)
    return factors[degree] * F((-1)**order * factorial(order), n**(order+1))


def corrected_sum(main, derivatives):
    """Euler--Maclaurin from n to infinity with the B8 remainder.

    Here f^(8) >= 0 on the tail, and higher derivatives vanish at infinity.
    Supremum of |B8({x})| equals |B8| (or use its cosine series). Thus
    the B8 remainder is at most |B8| (-f^(7)(n)) / 8!.
    """
    result = main - F(1, 2)*derivatives[0]
    for j, bernoulli in enumerate(BERNOULLI, start=1):
        result -= (bernoulli / factorial(2*j)) * derivatives[2*j-1]
    error = -derivatives[7].lo * abs(BERNOULLI[-1]) / factorial(8)
    assert error >= 0
    return outward(result + Bounds(-error, error))


@cache
def li_constants():
    n = 256
    log_n = log_point(n)
    # H_8 < 3, sum_{j<=8} 1/j^2 < 2 and log(N)>5 entail f^(8)>=0
    # for each of the three logarithmic summands and every x>=N.
    assert log_n.lo > 5
    gammas = []
    for degree in range(3):
        finite = sum((power(log_point(j), degree) * F(1, j)
                      for j in range(1, n+1)), interval(0))
        main = finite - F(1, degree+1)*power(log_n, degree+1)
        derivatives = {j: log_derivative(j, degree, n, log_n)
                       for j in (0, 1, 3, 5, 7)}
        gammas.append(corrected_sum(main, derivatives))
    gamma, gamma1, gamma2 = gammas

    # For f=x^(-3), tail integral from N to infinity equals 1/(2N^2).
    finite_zeta = sum((F(1, j**3) for j in range(1, n+1)), F(0))
    derivatives = {j: interval(F((-1)**j*factorial(j+2), 2*n**(j+3)))
                   for j in (0, 1, 3, 5, 7)}
    zeta3 = corrected_sum(interval(finite_zeta+F(1, 2*n*n)), derivatives)
    pi = 16*atan_reciprocal(5) - 4*atan_reciprocal(239)
    log4pi = Bounds(log_point(4*pi.lo).lo, log_point(4*pi.hi).hi)

    # Derivatives of log xi(s) at s=1, from the Laurent expansion of zeta.
    first = 1 + F(1, 2)*(gamma-log4pi)
    second = -1 + F(1, 8)*pi*pi - gamma*gamma - 2*gamma1
    third = 2 - F(7, 4)*zeta3 + 3*gamma2 + 6*gamma*gamma1 + 2*power(gamma, 3)
    return tuple(outward(v) for v in (first, 2*first+second,
                                      3*first+3*second+F(1, 2)*third))


@cache
def moment_constants():
    """Sum w*(1-cos(theta))^j for j = 0, 1, 2."""
    first, second, third = li_constants()
    c = 2*first
    d1 = second - 2*first
    d2 = third - 2*second + first
    return tuple(outward(v) for v in (c, c-d1, F(1, 2)*(3*c-4*d1+d2)))


def main():
    values = li_constants() + moment_constants()
    labels = ('lambda_1', 'lambda_2', 'lambda_3', 'C', 'tau', 'M2')
    for label, value in zip(labels, values):
        assert value.hi - value.lo < F(1, 10**16)
        # Both integer endpoints below are outward rounded. Scaling is exact.
        scale = 10**19
        left = (scale*value.lo).__floor__()
        right = (scale*value.hi).__ceil__()
        print(f'{left}/10^19 <= {label} <= {right}/10^19')


if __name__ == '__main__':
    main()
