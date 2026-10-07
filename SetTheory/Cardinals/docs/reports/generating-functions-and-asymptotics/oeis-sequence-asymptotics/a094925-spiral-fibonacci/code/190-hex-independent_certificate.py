"""Independent certificate arithmetic in the basis 1,sqrt(5).

This module does not import the primary field/certificate implementation.
Pairs of Fractions use sqrt(5)^2=5. The tail is independently summed from
W_r=(12 phi+8) r Q^r +(-7 phi-4) Q^r by geometric-series differentiation.
"""
from fractions import Fraction as F
from math import isqrt


def pair(a=0, b=0):
    if type(a) not in (int, F) or type(b) not in (int, F):
        raise TypeError('independent coefficients must be int or Fraction')
    return F(a), F(b)


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def mul(x, y):
    return x[0] * y[0] + 5 * x[1] * y[1], x[0] * y[1] + x[1] * y[0]


def inv(x):
    norm = x[0] ** 2 - 5 * x[1] ** 2
    if norm == 0:
        raise ZeroDivisionError('zero sqrt(5)-basis element')
    return x[0] / norm, -x[1] / norm


def power(x, n):
    if type(n) is not int:
        raise TypeError('integer exponent required')
    if n < 0:
        return power(inv(x), -n)
    if n == 0:
        return pair(1)
    # Recursive squaring, independently implemented from the primary loop.
    half = power(x, n // 2)
    square = mul(half, half)
    return mul(square, x) if n % 2 else square


def interval(x, lo, hi):
    if type(lo) not in (int, F) or type(hi) not in (int, F):
        raise TypeError('rational endpoints required')
    if lo > hi:
        raise ValueError('reversed endpoints')
    ends = (x[0] + x[1] * lo, x[0] + x[1] * hi)
    return min(ends), max(ends)


def certificate(stages, last, previous):
    if any(type(v) is not int for v in (stages, last, previous)):
        raise TypeError('integer certificate inputs required')
    if stages < 1 or previous <= 0 or last <= previous:
        raise ValueError('invalid stage or terminal sequence values')
    n = 3 * stages ** 2 + 4 * stages + 2
    phi = pair(F(1, 2), F(1, 2))
    q = power(phi, -6)
    c = mul(mul(add(pair(last), mul(inv(phi), pair(previous))),
                power(phi, 1 - n)), pair(0, F(1, 5)))
    a = add(mul(pair(12), phi), pair(8))
    b = add(mul(pair(-7), phi), pair(-4))
    one_minus_q = add(pair(1), mul(pair(-1), q))
    geom = inv(one_minus_q)
    arith = mul(add(pair(stages + 1), mul(pair(-stages), q)), mul(geom, geom))
    t = mul(power(q, stages + 1), add(mul(a, arith), mul(b, geom)))
    bits = 2 * n + 512
    den = 2 ** bits
    s = isqrt(5 * den ** 2)
    if not s ** 2 < 5 * den ** 2 < (s + 1) ** 2:
        raise RuntimeError('independent root bracket failed')
    low, high = F(s, den), F(s + 1, den)
    cl, ch = interval(c, low, high)
    tl, th = interval(t, low, high)
    if not 0 < cl <= ch or not 0 < tl <= th < 1:
        raise ValueError('independent certificate prerequisites failed')
    bounds = cl, ch / (1 - th)
    return {'center_sqrt5': c, 'tail_sqrt5': t, 'interval': bounds,
            'original_index_interval': (2 * bounds[0] / (1 + high),
                                        2 * bounds[1] / (1 + low))}
