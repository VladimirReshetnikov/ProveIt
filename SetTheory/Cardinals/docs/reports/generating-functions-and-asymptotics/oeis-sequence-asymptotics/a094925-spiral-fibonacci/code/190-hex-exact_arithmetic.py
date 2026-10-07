"""Exact Q(phi) arithmetic and outward rational amplitude certificates.

All coefficients are integers/Fractions. No binary/decimal floating arithmetic
is used. The mathematical certificate inequality is proved in Report190.
"""
from __future__ import annotations
from fractions import Fraction
from math import isqrt
from spiral import integer


def rational(value):
    if type(value) not in (int, Fraction):
        raise TypeError('coefficient must be int or Fraction, not bool or float')
    return Fraction(value)


class Phi:
    __slots__ = ('a', 'b')

    def __init__(self, a=0, b=0):
        self.a, self.b = rational(a), rational(b)

    @staticmethod
    def cast(value):
        return value if type(value) is Phi else Phi(value)

    def __add__(self, other):
        other = self.cast(other)
        return Phi(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Phi(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        other = self.cast(other)
        return Phi(self.a * other.a + self.b * other.b,
                   self.a * other.b + self.b * other.a + self.b * other.b)

    __rmul__ = __mul__

    def inverse(self):
        norm = self.a * self.a + self.a * self.b - self.b * self.b
        if norm == 0:
            raise ZeroDivisionError('zero Q(phi) element')
        return Phi((self.a + self.b) / norm, -self.b / norm)

    def __truediv__(self, other):
        return self * self.cast(other).inverse()

    def __rtruediv__(self, other):
        return self.cast(other) * self.inverse()

    def __pow__(self, exponent):
        if type(exponent) is not int:
            raise TypeError('power must be an integer, not bool or float')
        if exponent < 0:
            return self.inverse() ** (-exponent)
        result, base = Phi(1), self
        while exponent:
            if exponent & 1:
                result = result * base
            base = base * base
            exponent //= 2
        return result

    def __eq__(self, other):
        other = self.cast(other)
        return self.a == other.a and self.b == other.b

    def enclosure(self, lower, upper):
        lower, upper = rational(lower), rational(upper)
        if lower > upper:
            raise ValueError('reversed rational endpoints')
        if self.b < 0:
            lower, upper = upper, lower
        return self.a + self.b * lower, self.a + self.b * upper


def phi_bracket(bits):
    integer(bits, 'bits', 1)
    denominator = 1 << bits
    root = isqrt(5 * denominator * denominator)
    if not root * root < 5 * denominator * denominator < (root + 1) ** 2:
        raise RuntimeError('integer square-root enclosure failed')
    return (Fraction(denominator + root, 2 * denominator),
            Fraction(denominator + root + 1, 2 * denominator))


def amplitude_certificate(stages, sequence):
    integer(stages, 'stages', 1)
    n = 3 * stages * stages + 4 * stages + 2
    if type(sequence) is not list or len(sequence) != n + 1:
        raise ValueError('sequence must terminate at the complete requested stage')
    if any(type(value) is not int or value < 0 for value in sequence):
        raise TypeError('sequence values must be nonnegative integers')
    if sequence[1] <= 0:
        raise ValueError('positive a1 is required')
    phi = Phi(0, 1)
    q = phi ** -6
    center = phi ** (-n) * (sequence[n] * phi + sequence[n - 1]) / (2 * phi - 1)
    tail = q ** (stages + 1) * (phi ** 7 * (stages + 1) - phi ** 6
                              + 2 * phi / (1 - q))
    bits = 2 * n + 512
    plo, phi_hi = phi_bracket(bits)
    cl, ch = center.enclosure(plo, phi_hi)
    tl, th = tail.enclosure(plo, phi_hi)
    if not 0 < cl <= ch or not 0 < tl <= th < 1:
        raise ValueError('certificate needs positive center and tail strictly below one')
    upper = ch / (1 - th)
    return {'n': n, 'bits': bits, 'phi': (plo, phi_hi), 'center': center,
            'tail': tail, 'tail_interval': (tl, th), 'interval': (cl, upper),
            'original_index_interval': (cl / phi_hi, upper / plo)}


def scaled_floor(value, places):
    value = rational(value)
    integer(places, 'places')
    return value.numerator * 10 ** places // value.denominator


def outward_decimal(value, places, upper=False):
    value = rational(value)
    integer(places, 'places', 1)
    if type(upper) is not bool:
        raise TypeError('upper must be a boolean')
    scale = 10 ** places
    z = -((-value.numerator * scale) // value.denominator) if upper else scaled_floor(value, places)
    sign = '-' if z < 0 else ''
    z = abs(z)
    return sign + str(z // scale) + '.' + str(z % scale).zfill(places)


def first_correction(stages):
    """Exact eta, future tail T, stable filter H and F1 on complete stages.

    Beyond U_R the eta tail is summed algebraically, so this is not a
    finite-cutoff approximation to F1. The stage argument must be positive.
    """
    from spiral import delay_table
    integer(stages, 'stages', 1)
    rows = delay_table(stages)
    phi = Phi(0, 1)
    q, rho = phi ** -6, -phi ** -2
    alpha, beta = phi / (2 * phi - 1), 1 / (phi * (2 * phi - 1))
    eta = [sum((phi ** (j - n) for j in row), Phi()) for n, row in enumerate(rows)]
    tail = q ** (stages + 1) * (phi ** 7 * (stages + 1) - phi ** 6 + 2 * phi / (1 - q))
    tails = [Phi()] * len(rows)
    for n in range(len(rows) - 1, -1, -1):
        tails[n] = tail
        tail = tail + eta[n]
    past, filters, corrections = Phi(), [], []
    for n in range(len(rows)):
        past = rho * past + eta[n]
        filters.append(past)
        corrections.append(-alpha * tails[n] + beta * past)
    return {'eta': eta, 'tail': tails, 'filter': filters, 'F1': corrections}
