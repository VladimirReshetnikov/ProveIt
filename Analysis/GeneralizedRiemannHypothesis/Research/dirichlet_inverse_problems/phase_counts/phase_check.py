#!/usr/bin/env python3
"""Enclose the number of nontrivial zeta zeros in the height interval [10,18],
using five sampling lines with real part 3 through 5, without assuming RH.
Run with Python 3.10+ and mpmath 1.3.x. No zero list is used.

The numerical enclosures use outward-rounded mpmath.iv operations. For each
sample, the Euler-product log and logarithmic derivative are truncated at 256;
their tails are bounded by the integral test. The completed gamma factor and
its derivative use Euler--Maclaurin with a periodic-Bernoulli remainder.
"""
from fractions import Fraction
from math import prod

from mpmath import iv

iv.dps = 40
F = Fraction
N = 256
SHIFT = 24


def convert(value):
    value = F(value)
    return iv.mpf(value.numerator) / value.denominator


def symmetric(radius):
    return iv.mpf([-1, 1]) * radius


def weights(offsets):
    return [prod(k*k / (k*k - h*h) for k in offsets if k != h)
            for h in offsets]


def normalization(offsets):
    # Integral of product_j (1+t^2/h_j^2)^(-1).
    return iv.pi * convert(sum(w*h for w, h in zip(weights(offsets), offsets)))


def prime_powers(limit):
    prime = [True] * (limit + 1)
    for p in range(2, limit + 1):
        if prime[p]:
            for composite in range(2*p, limit+1, p):
                prime[composite] = False
            power, exponent = p, 1
            while power <= limit:
                yield power, exponent, p
                power *= p
                exponent += 1


def gamma_terms(z):
    # Euler--Maclaurin remainder after B_8 is
    # -1/8 * integral_0^inf B_8({u}) (z+u)^(-8) du.
    # Its z-derivative is bounded by differentiating this integral.
    # The Fourier series of B_8 gives |B_8({u})| <= |B_8| = 1/30.
    w = z + SHIFT
    loggamma = (w - convert(F(1, 2))) * iv.log(w) - w
    psi = iv.log(w) - 1/(2*w)
    bernoulli = [F(1, 6), F(-1, 30), F(1, 42), F(-1, 30)]
    for k, value in enumerate(bernoulli, 1):
        coeff = convert(value) / (2*k)
        loggamma += coeff / ((2*k-1)*w**(2*k-1))
        psi -= coeff / w**(2*k)
    for k in range(SHIFT):
        loggamma -= iv.log(z+k)
        psi -= 1/(z+k)
    # Only the imaginary part of log Gamma is used, so its additive real
    # constant log(2*pi)/2 need not be evaluated.
    arggamma = loggamma.imag + symmetric(1/(1680*w.real**7))
    repsi = psi.real + symmetric(1/(240*w.real**8))
    return arggamma, repsi


def phase_and_slope(offset, height):
    h = convert(offset)
    sigma = h + convert(F(1, 2))
    s = iv.mpc(sigma, height)
    arggamma, repsi = gamma_terms(s/2)
    # Continuous log of xi along this vertical line: the elementary factors
    # are in the open right half-plane, and the Euler series defines log zeta.
    phase = (iv.log(s) + iv.log(s-1) - s*iv.log(iv.pi)/2).imag + arggamma
    slope = (1/s + 1/(s-1)).real + (repsi - iv.log(iv.pi))/2
    for n, exponent, p in prime_powers(N):
        term = iv.exp(-s*iv.log(n))
        phase += term.imag/exponent
        slope -= term.real*iv.log(p)
    # Bounds from summing x^-sigma and (log x)x^-sigma, both decreasing at N.
    base = iv.exp((1-sigma)*iv.log(N)) / (sigma-1)
    phase += symmetric(base)
    slope += symmetric(base*(iv.log(N) + 1/(sigma-1)))
    return phase, slope


def verify():
    offsets = [F(n, 2) for n in range(5, 10)]
    left, right = 10, 18
    guard, rest = offsets[::2], offsets[1::2]
    measurements = {(h, t): phase_and_slope(h, t)
                    for h in offsets for t in (left, right)}
    smoothed = sum(convert(w*h)*(measurements[h, right][0] -
                                 measurements[h, left][0])
                   for w, h in zip(weights(offsets), offsets)) / normalization(offsets)
    guard_sum = sum(convert(w*h)*(measurements[h, left][1] +
                                  measurements[h, right][1])
                    for w, h in zip(weights(guard), guard))
    error = normalization(rest) * guard_sum / (2*normalization(offsets))
    # Unconditional comparison accounts for horizontal displacements of every
    # zero from Re(s)=1/2 by up to D=1/2. Reflection makes the common-height
    # pair average a real part of the product evaluated at a complex shift.
    D = convert(F(1, 2))
    upper = prod(1/(1-(D/convert(h))**2) for h in offsets)
    angle = sum(iv.atan2(D, iv.sqrt(convert(h)**2 - D**2)) for h in guard)
    assert angle < iv.pi/2
    lower = iv.cos(angle) / prod(1+(D/convert(h))**2 for h in guard)
    penalty = upper/lower
    unconditional_error = penalty*error
    count = smoothed + symmetric(unconditional_error)
    print("Offsets             ", ", ".join(str(h) for h in offsets))
    print("Heights             ", left, right)
    print("Smoothed count      ", smoothed)
    print("Unscaled guard bound", error)
    print("Displacement penalty", penalty)
    print("Absolute error bound", unconditional_error)
    print("Count enclosure     ", count)
    # Direct interval comparisons, independent of displayed decimal rounding.
    assert smoothed > convert(F(1005, 1000)) and smoothed < convert(F(1007, 1000))
    assert error > 0 and error < convert(F(290, 1000))
    assert unconditional_error > 0 and unconditional_error < convert(F(390, 1000))
    assert count > 0 and count < 2
    print("The only enclosed integer is 1. No RH assumption is used.")


if __name__ == "__main__":
    verify()
