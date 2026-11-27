#!/usr/bin/env python3
"""Certify a zero that separates the conjugate quartic characters modulo 5.

Running this file needs Python 3 and mpmath 1.3.0.  All nonintegral
input constants in the verification are rational values enclosed by
mpmath.iv. Complex powers use exp(s log x) for positive real x.
The printed inequalities are checked by outward-rounded interval arithmetic.
"""
from fractions import Fraction
from math import factorial, prod
from mpmath import iv

iv.dps = 45
R = iv.mpf
C = iv.mpc
ORDER, CUT = 8, 32
# Bernoulli numbers B_2 through B_16.
BERNOULLI = [Fraction(a, b) for a,b in
             [(1,6), (-1,30), (1,42), (-1,30),
              (5,66), (-691,2730), (7,6), (-3617,510)]]


def power(x, exponent):
    return iv.exp(exponent * iv.log(x))


def hurwitz(s, a):
    """Euler--Maclaurin enclosure for Hurwitz zeta(s,a) at our test points."""
    assert abs(s) < 7 and s.real >= R('0.5')
    rising = [C(1)]
    for k in range(2 * ORDER):
        rising.append(rising[-1] * (s + k))
    end = CUT + a
    value = sum(power(n+a, -s) for n in range(CUT))
    value += power(end, 1-s) / (s-1) + power(end, -s) / 2
    for k, b in enumerate(BERNOULLI, 1):
        coefficient = R(b.numerator) / (b.denominator * factorial(2*k))
        value += coefficient * rising[2*k-1] * power(end, 1-s-2*k)
    # The Fourier series of periodic B_16 gives
    # ||B_16({x})||/16! <= 2*zeta(16)/(2*pi)^16 < 4/6^16.
    # The remaining integral of (x+a)^(-Re(s)-16) is <= CUT^(-15).
    bound = (R(4) * prod(7+k for k in range(2*ORDER))
             / (6**(2*ORDER) * CUT**(2*ORDER-1)))
    error = R([-1,1])*bound
    return value + C(error, error)


def l_value(s, conjugate=False):
    unit = C(0, -1 if conjugate else 1)
    characters = [1, unit, -unit, -1]
    return power(R(5), -s)*sum(
        ch * hurwitz(s, R(a)/5) for a,ch in enumerate(characters, 1))


def verify():
    center = C(R('0.5'), R('6.18357819545'))
    h, radius = R('0.000001'), R('0.00000001')
    mid = l_value(center)
    slope = (l_value(center+h)-mid)/h
    partner = l_value(center, conjugate=True)
    # On |s-center|=1/4, both L-functions have modulus <= 64.
    # Indeed |sum_{n<=x} chi(n)| <= 2 by periodicity, and partial
    # summation gives |L(s)| <= 2 |s| / Re(s) < 56 there.
    # Thus the Taylor coefficients at center satisfy |a_k| <= 64*4^k.
    derivative_error = 1024*h/(1-4*h)
    quadratic_tail = 1024*radius**2/(1-4*radius)
    partner_variation = 256*radius/(1-4*radius)
    assert abs(mid) < R('0.00000000001')
    assert abs(slope)-derivative_error > 1
    assert abs(mid)+quadratic_tail < radius
    assert abs(partner)-partner_variation > 2
    print("chi(2)=i, conductor 5, center 1/2 + 6.18357819545 i, radius 10^-8")
    print("|L(center,chi)| < 10^-11; |L'(center,chi)| > 1")
    print("On the boundary the constant plus quadratic tail is < 10^-8.")
    print("Rouche count, including multiplicity: 1 for chi, 0 for conjugate(chi).")
    print("|L(s,conjugate(chi))| > 2 throughout the closed disk.")


if __name__ == "__main__":
    verify()
