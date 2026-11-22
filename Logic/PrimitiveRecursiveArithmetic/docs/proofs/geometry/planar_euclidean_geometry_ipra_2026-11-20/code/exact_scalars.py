"""Exact arithmetic on the derivative-certified real algebraic root records.

Uses rational univariate resultants and rational interval arithmetic. All
operands and outputs have finite records. No floating-point or external
computer-algebra library is used. Run this file to check the worked examples.
"""
from fractions import Fraction as Q
from functools import total_ordering
from math import comb, gcd, isqrt, lcm

from scalar_records import (
    Interval, Poly, Reader, RootRecord, divide, normalize, plus, poly,
    rational, resolution, scale, sign_annihilated, times, value,
)


def _monic(p: Poly) -> Poly:
    return scale(p, 1 / p[-1])


def _resultant(a: Poly, b: Poly) -> Q:
    """Ordinary univariate resultant of a nonzero a with b."""
    weight = Q(1)
    for _ in range(len(a) + len(b) + 2):
        if not b:
            return Q(0)
        m, n = len(a) - 1, len(b) - 1
        if n == 0:
            return weight * b[0] ** m
        _, remainder = divide(a, b)
        if not remainder:
            return Q(0)
        weight *= (-1) ** (m * n) * b[-1] ** (m - (len(remainder) - 1))
        a, b = b, remainder
    raise ArithmeticError("resultant degree bound exceeded")


def _binary_annihilator(p: Poly, q: Poly, *, product: bool) -> Poly:
    """Interpolate the norm polynomial on the integer grid 0,...,deg(p)deg(q)."""
    p, q = _monic(p), _monic(q)
    m, n = len(p) - 1, len(q) - 1
    samples = []
    for z in range(m * n + 1):
        if product:
            # T**n q(z/T). Its value at T=0 is defined polynomially.
            substituted = poly(q[n - i] * Q(z) ** (n - i) for i in range(n + 1))
        else:
            # q(z-T).
            substituted = poly((-1) ** i * sum(q[j] * comb(j, i) * Q(z) ** (j - i)
                                              for j in range(i, n + 1))
                               for i in range(n + 1))
        samples.append(_resultant(p, substituted))
    answer = ()
    binomial = poly([1])
    for j in range(m * n + 1):
        answer = plus(answer, scale(binomial, samples[0]))
        samples = [b - a for a, b in zip(samples, samples[1:])]
        binomial = scale(times(binomial, poly([-j, 1])), Q(1, j + 1))
    assert len(answer) == m * n + 1 and answer[-1] == 1
    return answer


def _rational_candidate(p: Poly, read: Reader):
    """Recover rational results without integer factorization."""
    denominator = lcm(*(c.denominator for c in p))
    coeffs = [int(c * denominator) for c in p]
    bound = abs(coeffs[-1]) // gcd(*coeffs)
    left, right = read(resolution(Q(1, 4 * bound * bound)))
    candidate = ((left + right) / 2).limit_denominator(bound)
    # All rational roots have denominator <= bound. Two such candidates have
    # separation >= 1/bound**2, but a nearby irrational root could also lie
    # in the reader interval. The isolation check below rules this out.
    return candidate if left <= candidate <= right and not value(p, candidate) else None


def _from_reader(p: Poly, read: Reader):
    record = normalize(p, read)
    candidate = _rational_candidate(record.p, record.read)
    if candidate is not None and record.left < candidate < record.right:
        return Scalar.rational(candidate)
    return Scalar.from_record(record)


def _to_scalar(x):
    if isinstance(x, Scalar):
        return x
    if isinstance(x, (int, Q)):
        return Scalar.rational(x)
    return NotImplemented


@total_ordering
class Scalar:
    """An exact real algebraic scalar, comparable by represented value."""

    __slots__ = ("record", "_rational")
    __hash__ = None

    def __init__(self, record: RootRecord):
        if not isinstance(record, RootRecord):
            raise TypeError("use Scalar.rational for rational inputs")
        self.record = record
        self._rational = -record.p[0] / record.p[1] if len(record.p) == 2 else None

    @classmethod
    def rational(cls, numerator, denominator=1):
        return cls(rational(Q(numerator) / Q(denominator)))

    @classmethod
    def from_record(cls, record: RootRecord):
        return cls(record)

    def read(self, n: int) -> Interval:
        if self._rational is not None:
            return self._rational, self._rational
        return self.record.read(n)

    def sign(self) -> int:
        return sign_annihilated(self.record.p, self.read)

    def _arithmetic(self, other, product):
        a, b = self, _to_scalar(other)
        if b is NotImplemented:
            return NotImplemented
        if a._rational is not None and b._rational is not None:
            x, y = a._rational, b._rational
            return Scalar.rational(x * y if product else x + y)
        if product:
            if a._rational == 0 or b._rational == 0:
                return Scalar.rational(0)
            if a._rational == 1:
                return b
            if b._rational == 1:
                return a
        else:
            if a._rational == 0:
                return b
            if b._rational == 0:
                return a
        shift = 1
        if product:
            bound = max(Q(1), *(abs(x) for x in (*a.read(0), *b.read(0))))
            shift = resolution(1 / (2 * bound))

        def read(n):
            l, r = a.read(n + shift)
            u, v = b.read(n + shift)
            if not product:
                return l + u, r + v
            corners = (l * u, l * v, r * u, r * v)
            return min(corners), max(corners)

        if product and a is b:
            # Write p(T) = e(T²) + T o(T²). Then e(Y)² - Y o(Y)²
            # vanishes at Y = a², without adjoining a duplicate generator.
            even, odd = a.record.p[::2], a.record.p[1::2]
            p = plus(times(even, even), (Q(0),) + scale(times(odd, odd), Q(-1)))
        else:
            p = _binary_annihilator(a.record.p, b.record.p, product=product)
        return _from_reader(p, read)

    def __add__(self, other):
        return self._arithmetic(other, False)

    __radd__ = __add__

    def __mul__(self, other):
        return self._arithmetic(other, True)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        if not isinstance(exponent, int):
            return NotImplemented
        if exponent < 0:
            return self.reciprocal() ** -exponent
        result = Scalar.rational(1)
        factor = self
        while exponent:
            if exponent & 1:
                result *= factor
            exponent //= 2
            if exponent:
                factor *= factor
        return result

    def __abs__(self):
        return -self if self.sign() < 0 else self

    def __bool__(self):
        return self.sign() != 0

    def __neg__(self):
        p = poly(c * (-1) ** i for i, c in enumerate(self.record.p))
        return Scalar.from_record(RootRecord(p, -self.record.right, -self.record.left))

    def __sub__(self, other):
        other = _to_scalar(other)
        return NotImplemented if other is NotImplemented else self + (-other)

    def __rsub__(self, other):
        return (-self) + other

    def reciprocal(self):
        if not self.sign():
            raise ZeroDivisionError("inverse of zero")
        if self._rational is not None:
            return Scalar.rational(1 / self._rational)
        p = self.record.p
        first = next(i for i, c in enumerate(p) if c)
        gap = min(Q(1, 4), abs(p[first]) / (8 * (1 + sum(map(abs, p[first + 1:])))))
        n0 = resolution(gap)
        l0, r0 = self.read(n0)
        bound = min(abs(l0), abs(r0))
        assert l0 * r0 > 0
        shift = resolution(bound * bound)

        def read(n):
            left, right = self.read(max(n0, n + shift))
            return 1 / right, 1 / left

        return _from_reader(poly(reversed(p)), read)

    def __truediv__(self, other):
        other = _to_scalar(other)
        return NotImplemented if other is NotImplemented else self * other.reciprocal()

    def __rtruediv__(self, other):
        return self.reciprocal() * other

    def sqrt(self):
        sign = self.sign()
        if sign < 0:
            raise ValueError("negative radicand")
        if not sign:
            return Scalar.rational(0)
        if self._rational is not None:
            a, b = self._rational.as_integer_ratio()
            s, t = isqrt(a), isqrt(b)
            if (s * s, t * t) == (a, b):
                return Scalar.rational(s, t)

        def read(n):
            left, right = self.read(2 * n + 6)
            denominator = 1 << (n + 3)

            def lower_index(x):
                x = max(Q(0), x) * denominator**2
                return isqrt(x.numerator // x.denominator)

            return Q(lower_index(left), denominator), Q(lower_index(right) + 1, denominator)

        substituted = poly(c for a in self.record.p for c in (a, Q(0)))
        return _from_reader(substituted, read)

    def _compare(self, other):
        other = _to_scalar(other)
        if other is NotImplemented:
            return NotImplemented
        if self is other:
            return 0
        l, r = self.read(0)
        u, v = other.read(0)
        if r < u:
            return -1
        if l > v:
            return 1
        if l == r == u == v:
            return 0
        negated = -other
        p = _binary_annihilator(self.record.p, negated.record.p, product=False)

        def read(n):
            l, r = self.read(n + 1)
            u, v = other.read(n + 1)
            return l - v, r - u

        return sign_annihilated(p, read)

    def __eq__(self, other):
        result = self._compare(other)
        return NotImplemented if result is NotImplemented else result == 0

    def __lt__(self, other):
        result = self._compare(other)
        return NotImplemented if result is NotImplemented else result < 0

    def __repr__(self):
        if self._rational is not None:
            return f"Scalar.rational({self._rational.numerator}, {self._rational.denominator})"
        return f"Scalar.from_record({self.record!r})"


def check_examples():
    a, b = Scalar.rational(2).sqrt(), Scalar.rational(3).sqrt()
    alias = Scalar.from_record(RootRecord(poly([-2, 0, 1]), Q(1), Q(3, 2)))
    assert a == alias and a < b and a >= alias
    assert a * alias == 2 and a - alias == 0 and a / alias == 1
    assert a**2 == 2 and a**-2 == Q(1, 2) and abs(-a) == a
    assert not (a - alias) and bool(b)
    assert (a + b) * (b - a) == 1
    assert (a * b).sqrt() * (a * b).sqrt() == a * b
    assert 3 / b == b and a + (-a) == 0
    assert Scalar.rational(9, 16).sqrt() == Q(3, 4)
    for fail, exception in [(lambda: a / (a - alias), ZeroDivisionError),
                            (lambda: (-a).sqrt(), ValueError)]:
        try:
            fail()
        except exception:
            pass
        else:
            raise AssertionError("invalid input failed to raise its guard")
    print("Passed: scalar arithmetic, order, shared annihilator, cancellation, "
          "nested radicals, rational recovery, and exceptional guards.")


if __name__ == "__main__":
    check_examples()
