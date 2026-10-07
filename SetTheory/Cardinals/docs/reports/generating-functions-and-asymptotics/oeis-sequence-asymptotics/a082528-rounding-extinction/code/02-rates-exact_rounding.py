#!/usr/bin/env python3
"""Exact rational-power rounding and rational profile formulas (stdlib only).

All exported numeric routines reject bools, floats, invalid signs and invalid
integer domains with explicit exceptions. Fraction is used for exact rational
parameters; rational_power(a, b) validates and reduces a positive ratio.
No floating-point Gamma, logarithm, exponential or root is evaluated here.
"""
from fractions import Fraction
from math import isqrt


def integer(value, name, minimum=0):
    """Validate a genuine integer (bool is deliberately not an integer here)."""
    if type(value) is not int:
        raise TypeError(name + " must be an int, not bool or another type")
    if value < minimum:
        raise ValueError(name + " must be >= " + str(minimum))
    return value


def rational(value, name, positive=False):
    """Accept only exact int or Fraction, with the stated sign restriction."""
    if type(value) not in (int, Fraction):
        raise TypeError(name + " must be an int or Fraction")
    result = Fraction(value)
    if result < 0 or (positive and result == 0):
        raise ValueError(name + (" must be positive" if positive else " must be nonnegative"))
    return result


def rational_power(a, b=1):
    """Return reduced p=a/b; both a and b must be genuine positive integers."""
    return Fraction(integer(a, "a", 1), integer(b, "b", 1))


def _floor_nth_root(value, degree):
    """Integer Newton iteration; inputs already validated by the public caller."""
    if value < 2 or degree == 1:
        return value
    if degree == 2:
        return isqrt(value)
    if degree >= value.bit_length():
        return 1
    x = 1 << ((value.bit_length() + degree - 1) // degree)
    while True:
        y = ((degree - 1) * x + value // x ** (degree - 1)) // degree
        if y >= x:
            # Newton's decreasing iteration has reached floor(value**(1/degree)).
            return x
        x = y


def floor_root_ratio(numerator, denominator, degree):
    """Largest r >= 0 satisfying denominator*r**degree <= numerator."""
    integer(numerator, "numerator")
    integer(denominator, "denominator", 1)
    integer(degree, "degree", 1)
    return _floor_nth_root(numerator // denominator, degree)


def ceil_root_ratio(numerator, denominator, degree):
    """Least r >= 0 satisfying denominator*r**degree >= numerator."""
    r = floor_root_ratio(numerator, denominator, degree)
    return r if denominator * r ** degree == numerator else r + 1


def _forward_step(q, j, a, b):
    return floor_root_ratio(q ** b * (j - 1) ** a, j ** a, b)


def forward_profile(n, k, p):
    """Return (0,q_1,...,q_k), q_1=n, by exact forward rounding."""
    integer(n, "n")
    integer(k, "k", 1)
    p = rational(p, "p", True)
    a, b = p.numerator, p.denominator
    values = [0, n]
    for j in range(2, k + 1):
        values.append(_forward_step(values[-1], j, a, b))
    return tuple(values)


def terminal_quotient(n, k, p):
    """Exact q_k for nonnegative initial integer n and positive integer k."""
    return forward_profile(n, k, p)[-1]


def stopping_index(n, p):
    """First zero index A_p(n), with A_p(0)=1."""
    integer(n, "n")
    p = rational(p, "p", True)
    a, b = p.numerator, p.denominator
    q, j = n, 1
    while q:
        j += 1
        q = _forward_step(q, j, a, b)
    return j


def reverse_profile(k, p, h=1):
    """Return (0,q_1,...,q_k), q_k=h, for positive terminal h.

    q_j is the least integer r with j**a*r**b >= (j+1)**a*q_(j+1)**b.
    h=0 is intentionally outside this positive-threshold API.
    """
    integer(k, "k", 1)
    integer(h, "h", 1)
    p = rational(p, "p", True)
    a, b = p.numerator, p.denominator
    values = [0] * (k + 1)
    values[k] = h
    for j in range(k - 1, 0, -1):
        values[j] = ceil_root_ratio(values[j + 1] ** b * (j + 1) ** a, j ** a, b)
    return tuple(values)


def threshold(k, p, h=1):
    """Smallest n for which the exact forward quotient q_k is at least h."""
    return reverse_profile(k, p, h)[1]


def ceil_fraction(value):
    value = rational(value, "value")
    return -(-value.numerator // value.denominator)


def drift_function(p, u):
    """f_p(u)=u+ceil(p*u) for u>0, with the right-hand value f_p(0)=1."""
    p = rational(p, "p", True)
    u = rational(u, "u")
    return u + ceil_fraction(p * u) if u else Fraction(1)


def gamma_product(p, r):
    """Rational product P_r=prod_(m=1)^r (1-1/((p+1)*m)); P_0=1.

    The name describes the analytically identified product, not a Gamma call.
    """
    p = rational(p, "p", True)
    integer(r, "r")
    alpha, result = 1 / (p + 1), Fraction(1)
    for m in range(1, r + 1):
        result *= 1 - alpha / m
    return result


def invariant_exp(p, u):
    """Exact rational exp(I_p(u)) via finite products, including u=0."""
    p = rational(p, "p", True)
    u = rational(u, "u")
    if u == 0:
        return Fraction(1)
    r = ceil_fraction(p * u)
    return (r + u) / (gamma_product(p, r - 1) * (r + Fraction(r - 1) / p))


def profile_u(p, t):
    """Exact U_p(t)=I_p^(-1)(-log t) for rational 0<t<=1.

    Cell selection uses only rational products. Very small t may require many
    cells: this is an exact finite reference implementation, not a fast solver.
    """
    p = rational(p, "p", True)
    t = rational(t, "t", True)
    if t > 1:
        raise ValueError("t must be <= 1")
    alpha, previous, r = 1 / (p + 1), Fraction(1), 1
    while True:
        current = previous * (1 - alpha / r)
        if current <= t:
            return previous * (r + Fraction(r - 1) / p) / t - r
        previous, r = current, r + 1


def profile_mass_power(p, t):
    """Return H_p(t)**b exactly for p=a/b and rational 0<t<=1.

    H itself need not be rational when b>1; this routine does not approximate it.
    The t=0 endpoint contains a Gamma constant and is outside this exact API.
    """
    p = rational(p, "p", True)
    t = rational(t, "t", True)
    u = profile_u(p, t)
    return t ** (p.numerator + p.denominator) * u ** p.denominator
