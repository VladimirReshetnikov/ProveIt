#!/usr/bin/env python3
"""Certify the zeta Li-curvature estimates by rational interval arithmetic.

Python 3 standard library. All inclusion tests use fractions.Fraction.
The Euler--Maclaurin bound and the elementary series used here are also
described alongside their implementation.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from functools import cache


@dataclass(frozen=True)
class Bounds:
    lo: F
    hi: F

    def __add__(self, other):
        other = interval(other)
        return Bounds(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Bounds(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-interval(other))

    def __rsub__(self, other):
        return interval(other) + (-self)

    def __mul__(self, other):
        other = interval(other)
        products = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Bounds(min(products), max(products))

    __rmul__ = __mul__


def interval(x):
    if isinstance(x, Bounds):
        return x
    return Bounds(F(x), F(x))


def outward(x):
    """Round interval endpoints outward to keep intermediate integers short."""
    scale = 10 ** 24
    lower = (x.lo * scale).__floor__()
    upper = (x.hi * scale).__ceil__()
    return Bounds(F(lower, scale), F(upper, scale))


def log_unit(x):
    """Natural log for 1 <= x <= 2 from the positive arctanh series."""
    assert 1 <= x <= 2
    t = (x - 1) / (x + 1)
    count = 28
    partial = sum((2 * t ** (2*j + 1) / (2*j + 1) for j in range(count)), F(0))
    remainder = 2 * t ** (2*count + 1) / ((2*count + 1) * (1 - t*t))
    return outward(Bounds(partial, partial + remainder))


@cache
def log_point(x):
    x = F(x)
    assert x >= 1
    k = 0
    while x >= 2:
        x /= 2
        k += 1
    return log_unit(x) + k * log_unit(F(2))


def atan_reciprocal(denominator):
    """Adjacent alternating sums enclose atan(1/denominator)."""
    t = F(1, denominator)
    count = 20
    partial = sum(((-1)**j * t**(2*j+1) / (2*j+1) for j in range(count)), F(0))
    next_sum = partial + (-1)**count * t**(2*count+1) / (2*count+1)
    return outward(Bounds(min(partial, next_sum), max(partial, next_sum)))


def stieltjes_constants(n=256):
    """Euler--Maclaurin on the tail of sum(f(k)) - integral(f).

    For f(x)=1/x or log(x)/x and n>=256, f'''' >= 0 on [n,infinity).
    Since sup |B4({x})| = 1/30, the absolute remainder after the B4 term
    is at most (-f'''(n))/720. The logarithmic derivative values follow
    from (log(x)/x)^(m) = (-1)^m m! (log x-H_m) / x^(m+1).
    """
    assert n >= 256
    log_n = log_point(n)
    gamma_main = sum((F(1, k) for k in range(1, n+1)), F(0)) - log_n
    gamma_main += -F(1, 2*n) + F(1, 12*n*n) - F(1, 120*n**4)
    gamma_error = F(1, 120*n**4)

    weighted = sum((log_point(k) * F(1, k) for k in range(1, n+1)), interval(0))
    third = (11 - 6*log_n) * F(1, n**4)
    gamma1_main = weighted - F(1, 2)*log_n*log_n - F(1, 2*n)*log_n
    gamma1_main += (log_n-1) * F(1, 12*n*n) + third * F(1, 720)
    gamma1_error = -third.lo / 720
    return (outward(gamma_main + Bounds(-gamma_error, gamma_error)),
            outward(gamma1_main + Bounds(-gamma1_error, gamma1_error)))


def chebyshev(n, x):
    """Exact T_n(x), with each endpoint evaluated as a point."""
    previous, current = F(1), x
    for _ in range(1, n):
        previous, current = current, 2*x*current - previous
    return current


def certify(name, value, left, right):
    assert F(left) < value.lo <= value.hi < F(right), (name, value)
    print(f'{left} < {name} < {right}')


def main():
    if not __debug__:
        raise RuntimeError("Run Python without -O so all checks are enabled.")
    pi = 16*atan_reciprocal(5) - 4*atan_reciprocal(239)
    log4pi = Bounds(log_point(4*pi.lo).lo, log_point(4*pi.hi).hi)
    g, g1 = stieltjes_constants()
    first = 1 + F(1, 2)*(g - log4pi)
    second = 2*first - 1 + F(1, 8)*pi*pi - g*g - 2*g1
    tau = 4*first - second
    block_margin = 2*first - 35**2*tau
    assert first.lo > 0 and tau.lo > 0
    oscillation = Bounds(tau.lo / first.hi, tau.hi / first.lo)

    certify('lambda_1', first, '0.02309570896', '0.02309570898')
    certify('lambda_2', second, '0.0923457351', '0.0923457354')
    certify('4 lambda_1 - lambda_2', tau, '0.0000371005', '0.0000371010')
    certify('71-term block lower bound', block_margin, '0.0007430', '0.0007433')
    certify('negative excursion magnitude bound', oscillation, '0.00160638', '0.00160640')

    # 1-cos(pi/n) >= 2/n^2 for n>=2. Thus to order n<=40 the
    # argument is on the last interval of monotonicity of T_n.
    a = outward(1 - F(1, 2)*oscillation)
    assert a.lo > 1 - F(2, 40**2) and a.hi < 1
    for n, left, right in ((39, '0.0003500', '0.0003504'),
                            (40, '-0.0015012', '-0.0015008')):
        moment = 2*first * Bounds(chebyshev(n, a.lo), chebyshev(n, a.hi))
        certify(f'Chebyshev lower bound at j={n}', moment, left, right)


if __name__ == '__main__':
    main()
