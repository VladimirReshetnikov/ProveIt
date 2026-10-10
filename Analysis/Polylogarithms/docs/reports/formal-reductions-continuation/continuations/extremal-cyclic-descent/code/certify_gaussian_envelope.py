#!/usr/bin/env python3
"""Exact rational certificates for the sharp Gaussian envelope.

Only Python's standard library is used. All interval endpoints are integers
on an outward-rounded decimal grid. No floating-point result is a premise.
See the article for the Euler value and differentiated-tail bounds.
"""
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import comb
from pathlib import Path
import json

DIGITS = 90
SCALE = 10 ** DIGITS


def ceildiv(a, b):
    assert b > 0
    return -((-a) // b)


@dataclass(frozen=True)
class I:
    lo: int
    hi: int

    def __post_init__(self):
        assert self.lo <= self.hi

    @classmethod
    def q(cls, value):
        f = Fraction(value)
        return cls(f.numerator * SCALE // f.denominator,
                   ceildiv(f.numerator * SCALE, f.denominator))

    def __add__(self, other):
        if not isinstance(other, I):
            other = I.q(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other if isinstance(other, I) else -I.q(other))

    def __rsub__(self, other):
        return I.q(other) - self

    def __mul__(self, other):
        if not isinstance(other, I):
            other = I.q(other)
        products = [self.lo * other.lo, self.lo * other.hi,
                    self.hi * other.lo, self.hi * other.hi]
        return I(min(products) // SCALE, ceildiv(max(products), SCALE))

    __rmul__ = __mul__

    def recip(self):
        assert self.lo > 0
        return I(SCALE * SCALE // self.hi,
                 ceildiv(SCALE * SCALE, self.lo))

    def __truediv__(self, other):
        if not isinstance(other, I):
            f = Fraction(other)
            assert f > 0
            return self * I.q(1 / f)
        return self * other.recip()

    def decimals(self, digits=45):
        assert 0 <= digits <= DIGITS
        divisor = 10 ** (DIGITS - digits)
        low = self.lo // divisor
        high = ceildiv(self.hi, divisor)

        def fmt(x):
            sign = '-' if x < 0 else ''
            x = abs(x)
            return sign + str(x // 10 ** digits) + '.' + str(x % 10 ** digits).zfill(digits)

        return [fmt(low), fmt(high)]


def log_ratio_1_to_2(r):
    """2 atanh((r-1)/(r+1)), with a proved geometric tail."""
    r = Fraction(r)
    assert 1 <= r <= 2
    v = I.q((r - 1) / (r + 1))
    square = v * v
    term, total = v, I.q(0)
    count = 160
    for j in range(count):
        total = total + term / (2 * j + 1)
        term = term * square
    tail = 2 * term / (2 * count + 1) / (1 - square)
    return 2 * total + I(0, tail.hi)


@lru_cache(None)
def log_integer(n):
    assert n >= 1
    k = n.bit_length() - 1
    return k * log_ratio_1_to_2(2) + log_ratio_1_to_2(Fraction(n, 2 ** k))


def exp_small_nonnegative(x):
    """Taylor enclosure on [0,1]; tail <= 2 times first omitted term."""
    assert 0 <= x.lo <= x.hi <= SCALE
    term, total = I.q(1), I.q(1)
    for k in range(1, 181):
        term = term * x / k
        total = total + term
    omitted = term * x / 181
    return total + I(0, 2 * omitted.hi)


def exp_negative(x):
    assert 0 <= x.lo <= x.hi <= 16 * SCALE
    result = exp_small_nonnegative(x / 16).recip()
    for _ in range(4):
        result = result * result
    return result


def euler_pair(w, step, count):
    """Euler finite value and w derivative for sum (-1)^j/(step*j+1)^w."""
    denominator = 2 ** count
    value, derivative = I.q(0), I.q(0)
    tail_binomial = denominator - 1
    for j in range(count):
        n = step * j + 1
        logarithm = log_integer(n)
        power = exp_negative(I.q(w) * logarithm)
        coefficient = Fraction((-1) ** j * tail_binomial, denominator)
        value = value + coefficient * power
        derivative = derivative - coefficient * power * logarithm
        if j + 1 < count:
            tail_binomial -= comb(count, j + 1)
    return value, derivative


def envelope(w, count=160):
    w = Fraction(w)
    assert 1 <= w <= 2
    beta, beta_prime = euler_pair(w, 2, count)
    eta, eta_prime = euler_pair(w, 1, count)
    log2 = log_integer(2)
    two_power = exp_negative(I.q(w) * log2)
    finite = beta + two_power * eta
    finite_prime = beta_prime + two_power * (eta_prime - log2 * eta)
    value_tail = (1 + two_power) * I.q(Fraction(1, 2 ** count))
    derivative_tail = I.q(Fraction(4, 2 ** count))
    value = finite + I(0, value_tail.hi)
    derivative = finite_prime + I(-derivative_tail.hi, derivative_tail.hi)
    return value, derivative


def main():
    # Endpoints are rational proposals, accepted only by proved derivative signs.
    lo = Fraction('1.30221658710124120959237170')
    hi = Fraction('1.30221658710124120959237171')
    c_lo, d_lo = envelope(lo)
    c_hi, d_hi = envelope(hi)
    assert d_lo.lo > 0
    assert d_hi.hi < 0
    assert c_lo.lo > SCALE
    # Strict log-concavity of C-1 supplies its tangent-line upper bound.
    slope_upper = I.q(Fraction(d_lo.hi, c_lo.lo - SCALE))
    correction = slope_upper * I.q(hi - lo)
    upper = 1 + (c_lo - 1) * exp_small_nonnegative(correction)
    maximum = I(c_lo.lo, upper.hi)
    first, d_first = envelope(Fraction(1))
    second, d_second = envelope(Fraction(2))
    assert d_first.lo > 0 and d_second.hi < 0
    result = {
        'arithmetic': 'integer fixed-point outward intervals; standard library only',
        'decimal_grid_digits': DIGITS,
        'euler_terms': 160,
        'root_proposal': [str(lo), str(hi)],
        'root_decimal_enclosure': ['1.30221658710124120959237170',
                                   '1.30221658710124120959237171'],
        'derivative_at_left': d_lo.decimals(60),
        'derivative_at_right': d_hi.decimals(60),
        'maximum_enclosure': maximum.decimals(45),
        'C_at_1': first.decimals(45),
        'C_prime_at_1': d_first.decimals(45),
        'C_at_2': second.decimals(45),
        'C_prime_at_2': d_second.decimals(45),
        'certified_sign_tests': 4,
        'scope': 'C is the sharp envelope for -2 Im F_ab(i); the all-N Euler constant is proved on a+b=1 only',
    }
    out = Path(__file__).resolve().parents[1] / 'results' / 'gaussian_envelope_certificate.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
