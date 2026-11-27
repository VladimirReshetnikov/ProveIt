#!/usr/bin/env python3
"""Verify a zero-multiplicity difference between two biquadratic fields.

All interval endpoints represent integers divided by 2**80. The program uses
integer arithmetic and the standard-library Fraction class throughout.
Run with Python 3; no input files or third-party packages are required.
"""
from fractions import Fraction
from functools import lru_cache
from math import factorial

UNIT = 1 << 80
MESH = 512
LIMIT = 150
UPPER = 5


def ceil_div(a, b):
    return -((-a) // b)


def enclose_rational(a, b=1):
    return UNIT * a // b, ceil_div(UNIT * a, b)


def plus(x, y):
    return x[0] + y[0], x[1] + y[1]


def minus(x, y):
    return x[0] - y[1], x[1] - y[0]


def times(x, y):
    products = [s * t for s in x for t in y]
    return min(products) // UNIT, ceil_div(max(products), UNIT)


def times_positive_int(x, n):
    return x[0] * n, x[1] * n


def over_positive_int(x, n):
    return x[0] // n, ceil_div(x[1], n)


def widen(x, radius):
    return x[0] - radius, x[1] + radius


ZERO = (0, 0)
ONE = (UNIT, UNIT)


def pi_interval():
    # Machin's identity, pi = 16 atan(1/5) - 4 atan(1/239).
    def atan_bounds(q):
        s = sum(Fraction((-1)**k, (2*k + 1) * q**(2*k + 1))
                for k in range(16))
        return s, s + Fraction(1, 33 * q**33)
    a, b = atan_bounds(5)
    c, d = atan_bounds(239)
    lo, hi = 16*a - 4*d, 16*b - 4*c
    return (enclose_rational(lo.numerator, lo.denominator)[0],
            enclose_rational(hi.numerator, hi.denominator)[1])


PI = pi_interval()


def small_exp(x):
    assert 0 <= x[0] <= x[1] <= UNIT
    term, value = ONE, ONE
    for k in range(1, 22):
        term = over_positive_int(times(term, x), k)
        value = plus(value, term)
    # At 0 <= x <= 1, the omitted series is at most 2/22!.
    return value[0], value[1] + ceil_div(2 * UNIT, factorial(22))


def exp_negative(x):
    assert 0 <= x[0] <= x[1] <= 128 * UNIT
    y = small_exp(over_positive_int(x, 128))
    for _ in range(7):
        y = times(y, y)
    return UNIT**2 // y[1], ceil_div(UNIT**2, y[0])


def cosine(x):
    assert 0 <= x[0] <= x[1] <= 7 * UNIT
    midpoint = (x[0] + x[1]) // 2
    square = times((midpoint, midpoint), (midpoint, midpoint))
    term, value = ONE, ONE
    for k in range(1, 15):
        term = over_positive_int(times(term, square), (2*k-1) * (2*k))
        value = minus(value, term) if k % 2 else plus(value, term)
    # Taylor's theorem at the midpoint through degree 28, then |cos'| <= 1.
    taylor_error = ceil_div(7**29 * UNIT, factorial(29))
    return widen(value, taylor_error + max(midpoint - x[0], x[1] - midpoint))


def character(n, primes):
    # For these positive fundamental discriminants all prime factors are 1 mod 4.
    v = 1
    for p in primes:
        r = pow(n, (p - 1) // 2, p)
        v *= -1 if r == p-1 else r
    return v


def exp_grid(numerator, denominator):
    """Intervals for exp(j*numerator/denominator), j = 0,...,UPPER*MESH."""
    step = small_exp(enclose_rational(numerator, denominator))
    values = [ONE]
    for _ in range(UPPER * MESH):
        values.append(times(values[-1], step))
    return values


@lru_cache(maxsize=None)
def theta_weights(primes):
    conductor = 1
    for p in primes:
        conductor *= p
    assert conductor <= 1105
    signs = [character(n, primes) for n in range(LIMIT + 1)]
    heights = exp_grid(2, MESH)
    weights = exp_grid(1, 2*MESH)
    cells = []
    for j in range(UPPER*MESH):
        height = heights[j][0], heights[j+1][1]
        prefactor = weights[j][0], weights[j+1][1]
        scale = over_positive_int(times(PI, height), conductor)
        theta = ZERO
        for n in range(1, LIMIT + 1):
            exponent = times_positive_int(scale, n*n)
            if exponent[0] > 60 * UNIT:
                break
            if signs[n]:
                term = exp_negative(exponent)
                theta = plus(theta, term) if signs[n] == 1 else minus(theta, term)
        cells.append(times(theta, prefactor))
    return cells


def completed_value(primes, ta, tb):
    t = enclose_rational(ta, 100)[0], enclose_rational(tb, 100)[1]
    value = ZERO
    for j, weight in enumerate(theta_weights(primes)):
        cell = enclose_rational(j, MESH)[0], enclose_rational(j+1, MESH)[1]
        value = plus(value, times(weight, cosine(times(t, cell))))
    # On [0,5], all skipped terms with n<=150 total at most 150*exp(-60).
    # For n>150 the absolute sum is bounded by the Gaussian integral from 150
    # to infinity, at most 1105*exp(-3*150**2/1105)/(6*150). Multiply these
    # bounds by 20*exp(5/2) to cover the full weighted integral on [0,5].
    # For u=5+v, pi*exp(2*u)/d >= 40*(1+2*v). The infinite theta sum is
    # <= 2*exp(-40*(1+2*v)); the weighted integral tail is at most
    # 8*exp(5/2-40)/(80-1/2). The sum of all omitted errors is below 1e-9.
    return widen(over_positive_int(times_positive_int(value, 4), MESH),
                 ceil_div(UNIT, 10**9))


def decimal_thousandths(n):
    return f"{'-' if n < 0 else ''}{abs(n)//1000}.{abs(n)%1000:03d}"


if __name__ == '__main__':
    cases = [
        ((13, 17), 120, 120, 1),
        ((13, 17), 123, 123, -1),
        ((13,), 120, 123, 1),
        ((5, 17), 120, 123, 1),
        ((5, 13, 17), 120, 123, 1),
    ]
    for primes, a, b, sign in cases:
        lo, hi = completed_value(primes, a, b)
        assert lo > 0 if sign == 1 else hi < 0
        floored = decimal_thousandths(lo * 1000 // UNIT)
        ceiled = decimal_thousandths(ceil_div(hi * 1000, UNIT))
        d = 1
        for p in primes:
            d *= p
        print(f"d={d:3}, t=[{a}/100,{b}/100], value in [{floored}, {ceiled}]")

    # Euler--Maclaurin yields zeta(s) = 1/(s-1)+1/2+s/12+R,
    # |R| <= |s(s+1)|/(12*(sigma+1)), using max |B_2({x})| = 1/6.
    # These exact comparisons show nonvanishing of the last factor of zeta_L.
    sigma, left, right = Fraction(1, 2), Fraction(120, 100), Fraction(123, 100)
    imaginary_upper = -left / ((sigma - 1)**2 + right**2) + right / 12
    remainder_squared = ((sigma**2 + right**2) * ((sigma + 1)**2 + right**2)
                         / (12 * (sigma + 1))**2)
    assert imaginary_upper < Fraction(-57, 100)
    assert remainder_squared < Fraction(16, 100)**2
    print("Im zeta(1/2+it) < -0.41 throughout [120/100,123/100].")
