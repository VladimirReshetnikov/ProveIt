#!/usr/bin/env python3
"""Exact certificate for the Gaussian return bound at d=16, 2n=26.

Uses only Python's standard library and exact integer/rational arithmetic.
Two independent coefficient computations must agree. The bound on pi is
certified from Machin's identity and finite alternating arctangent sums.
"""

from fractions import Fraction
from math import comb, factorial


def require(condition):
    if not condition:
        raise ArithmeticError("Exact counterexample certificate failed")


def integer_recurrence(d, m):
    # C[m,d] = (m!)^2 [t^m] (sum t^k/(k!)^2)^d.
    coeffs = [1] * (m + 1)
    for _ in range(1, d):
        coeffs = [
            sum(comb(n, k) ** 2 * coeffs[n-k] for k in range(n+1))
            for n in range(m+1)
        ]
    return comb(2*m, m) * coeffs[m]


def truncated_product(a, b, m):
    return [sum(a[k] * b[n-k] for k in range(n+1))
            for n in range(m+1)]


def rational_power(d, m):
    # Independently square the truncated ordinary generating series.
    base = [Fraction(1, factorial(k)**2) for k in range(m+1)]
    out = [Fraction(1)] + [Fraction(0)] * m
    while d:
        if d & 1:
            out = truncated_product(out, base, m)
        d >>= 1
        if d:
            base = truncated_product(base, base, m)
    result = factorial(2*m) * out[m]
    require(result.denominator == 1)
    return result.numerator


def main():
    d, m = 16, 13
    walks = integer_recurrence(d, m)
    require(walks == rational_power(d, m))
    require(walks == 23062502564288544059408295833600)
    probability = Fraction(walks, (2*d)**(2*m))
    require(probability == Fraction(5630493790109507827003978475, 2**118))

    # pi = 16 atan(1/5) - 4 atan(1/239).
    # The four-term sum is a strict lower bound on atan(1/5),
    # whereas 1/239 is a strict upper bound on atan(1/239).
    arctan_lower = sum(
        (Fraction((-1)**j, (2*j+1)*5**(2*j+1)) for j in range(4)),
        Fraction(0),
    )
    machin_lower = 16*arctan_lower - Fraction(4, 239)
    pi_lower = Fraction(333, 106)
    require(machin_lower > pi_lower)

    gaussian_upper = 2 * (Fraction(d, 4*m)/pi_lower)**(d//2)
    ratio_lower = probability / gaussian_upper
    require(ratio_lower > Fraction(4001, 4000))
    difference = (5630493790109507827003978475 * 4329**8
                  - 2**143 * 53**8)
    require(difference == 241148999863792122048803143474490963808862899634921387)
    require(difference > 0)

    print('Both exact coefficient computations agree.')
    print('Closed walks of length 26 in dimension 16:', walks)
    print('Return probability:', probability)
    print('Certified pi lower bound:', pi_lower)
    print('Certified lower bound on return / Gaussian:', ratio_lower)
    print('In particular, return / Gaussian > 4001/4000 > 1.')
    print('Positive integer difference:', difference)


if __name__ == '__main__':
    main()
