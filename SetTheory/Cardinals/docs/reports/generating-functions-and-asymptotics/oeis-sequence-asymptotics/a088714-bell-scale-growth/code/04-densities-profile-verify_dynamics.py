#!/usr/bin/env python3
"""Reproduce the nonzero oscillation certificate using rigorous intervals.

Only Python's standard library is used. All moment coefficients and the
Stieltjes seed bounds are exact integers/rationals. Decimal arithmetic is
outward rounded; correctly rounded transcendental results are enlarged by
one adjacent representable number. No data from the inherited manuscript
or from floating-point calculations is imported.
"""

from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction
from pathlib import Path
import json


PRECISION = 100


def directed(fn, rounding):
    with localcontext() as ctx:
        ctx.prec = PRECISION
        ctx.rounding = rounding
        return fn()


def trans(fn, upper):
    # Decimal.ln/exp/sqrt are correctly rounded. One neighboring value
    # covers the exact result regardless of the tie-breaking direction.
    with localcontext() as ctx:
        ctx.prec = PRECISION
        value = fn()
        return value.next_plus() if upper else value.next_minus()


class I:
    def __init__(self, lo, hi=None):
        self.lo = Decimal(lo)
        self.hi = Decimal(lo if hi is None else hi)
        assert self.lo <= self.hi

    @classmethod
    def rational(cls, value):
        value = Fraction(value)
        numerator, denominator = Decimal(value.numerator), Decimal(value.denominator)
        return cls(directed(lambda: numerator / denominator, ROUND_FLOOR),
                   directed(lambda: numerator / denominator, ROUND_CEILING))

    @staticmethod
    def coerce(value):
        return value if isinstance(value, I) else I(value)

    def __add__(self, other):
        other = self.coerce(other)
        return I(directed(lambda: self.lo + other.lo, ROUND_FLOOR),
                 directed(lambda: self.hi + other.hi, ROUND_CEILING))

    __radd__ = __add__

    def __neg__(self):
        # copy_negate is exact and does not round to the ambient context.
        return I(self.hi.copy_negate(), self.lo.copy_negate())

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        pairs = [(a, b) for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return I(min(directed(lambda a=a, b=b: a * b, ROUND_FLOOR) for a, b in pairs),
                 max(directed(lambda a=a, b=b: a * b, ROUND_CEILING) for a, b in pairs))

    __rmul__ = __mul__

    def reciprocal(self):
        assert not self.lo <= 0 <= self.hi
        return I(directed(lambda: Decimal(1) / self.hi, ROUND_FLOOR),
                 directed(lambda: Decimal(1) / self.lo, ROUND_CEILING))

    def __truediv__(self, other):
        return self * self.coerce(other).reciprocal()

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        answer = I(1)
        for _ in range(exponent):
            answer = answer * self
        return answer

    def ln(self):
        assert self.lo > 0
        return I(trans(lambda: self.lo.ln(), False), trans(lambda: self.hi.ln(), True))

    def exp(self):
        return I(trans(lambda: self.lo.exp(), False), trans(lambda: self.hi.exp(), True))

    def sqrt(self):
        assert self.lo >= 0
        return I(trans(lambda: self.lo.sqrt(), False), trans(lambda: self.hi.sqrt(), True))

    def serial(self):
        return [str(self.lo), str(self.hi)]


def moments(count):
    triangle = [[0] * (count + 3) for _ in range(count + 1)]
    triangle[0] = [1] * (count + 3)
    for n in range(1, count + 1):
        for k in range(1, count + 2 - n):
            triangle[n][k] = triangle[n][k - 1] + sum(
                triangle[i][k] * triangle[n - 1 - i][k + 1] for i in range(n))
    return [triangle[n][1] for n in range(count + 1)]


def r(x):
    return (1 + (-x).exp()).ln()


def inverse_step(previous, current):
    return current + (1 + previous.exp()).ln()


def main():
    a = moments(31)
    assert a[:9] == [1, 1, 3, 13, 69, 419, 2809, 20353, 157199]
    s = Fraction(1, 100)
    upper = sum(Fraction(a[n]) * (-s) ** n for n in range(31))
    lower = upper + Fraction(a[31]) * (-s) ** 31
    assert 0 < lower < upper
    f = I(I.rational(lower).lo, I.rational(upper).hi)
    root5 = I(5).sqrt()
    beta = (root5 - 1) / 2
    phi = (root5 + 1) / 2
    previous = (I.rational(s) * f).ln()
    current = I.rational(s).ln()
    for _ in range(115):
        previous, current = current, inverse_step(previous, current)
    assert previous.lo > 0 and current.lo > previous.hi
    d = previous - beta * current
    error_denominator = 1 - phi * (-previous).exp()
    assert error_denominator.lo > 0
    error_bound = (-previous).exp() + phi * (-current).exp() / error_denominator
    assert d.lo > error_bound.hi

    # Independently enclose the exact invariant series, through j=4.
    orbit = {-1: previous, 0: current}
    for n in range(4):
        orbit[n + 1] = inverse_step(orbit[n - 1], orbit[n])
    terms = 5
    D_partial = d
    psi_partial = current + d / root5
    for j in range(terms):
        force = r(orbit[j - 1])
        D_partial = D_partial + ((-phi) ** j) * force
        psi_partial = psi_partial + (beta ** j) * force / root5
    D_denominator = 1 - phi * (-orbit[terms - 2]).exp()
    psi_denominator = 1 - beta * (-orbit[terms - 2]).exp()
    assert D_denominator.lo > 0 and psi_denominator.lo > 0
    D_tail = (phi ** terms) * (-orbit[terms - 1]).exp() / D_denominator
    psi_tail = (beta ** terms) * (-orbit[terms - 1]).exp() / psi_denominator / root5
    D = D_partial + I(D_tail.hi.copy_negate(), D_tail.hi)
    psi = psi_partial + I(0, psi_tail.hi)
    profile = psi * D

    # Coarse decimal statements displayed in the paper are exact claims.
    assert Decimal('26.4807143957') < current.lo < current.hi < Decimal('26.4807143959')
    assert Decimal('16.366') < previous.lo < previous.hi < Decimal('16.367')
    assert Decimal('0.00003580') < d.lo < d.hi < Decimal('0.00003582')
    assert error_bound.hi < Decimal('0.000000079')
    assert Decimal('0.00095032738531560') < profile.lo
    assert profile.hi < Decimal('0.00095032738531562')

    result = {
        'method': 'Exact rational Stieltjes seed, outward-rounded Decimal intervals',
        'decimal_precision': PRECISION,
        'orbit_index': 115,
        'moment_count': len(a),
        'moments_a0_through_a31': a,
        'seed_lower_exact': str(lower),
        'seed_upper_exact': str(upper),
        'seed_F_interval': f.serial(),
        'x': current.serial(),
        'g_x': previous.serial(),
        'd_x': d.serial(),
        'bound_on_absolute_D_minus_d': error_bound.serial(),
        'D_interval': D.serial(),
        'Psi_interval': psi.serial(),
        'profile_P_interval': profile.serial(),
        'D_tail_bound': D_tail.serial(),
        'Psi_tail_bound': psi_tail.serial(),
        'all_assertions_passed': True,
    }
    destination = Path(__file__).resolve().parents[1] / 'data' / 'dynamics_certificate.json'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({key: result[key] for key in
                     ('orbit_index', 'x', 'g_x', 'd_x', 'bound_on_absolute_D_minus_d',
                      'profile_P_interval', 'all_assertions_passed')}, indent=2))
    print('Certificate:', destination)


if __name__ == '__main__':
    main()
