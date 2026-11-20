"""Rational scalar records from the paper, using Python's standard library.

Polynomial coefficients are listed low degree first. The examples run with
python3 scalar_records.py. The program implements root records, normalizing a
reader with a supplied annihilator, exact signs, and listing rational-polynomial
real roots. A provisional reader must satisfy the mathematical preconditions.
"""

from dataclasses import dataclass
from fractions import Fraction as Q
from math import ceil
from typing import Callable

Poly = tuple[Q, ...]
Interval = tuple[Q, Q]
Reader = Callable[[int], Interval]


def poly(coefficients) -> Poly:
    terms = [Q(value) for value in coefficients]
    while terms and not terms[-1]:
        terms.pop()
    return tuple(terms)


def plus(a: Poly, b: Poly) -> Poly:
    n = max(len(a), len(b))
    return poly((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                for i in range(n))


def scale(a: Poly, c: Q) -> Poly:
    return poly(x * c for x in a)


def times(a: Poly, b: Poly) -> Poly:
    terms = [Q(0)] * (len(a) + len(b))
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            terms[i + j] += x * y
    return poly(terms)


def derivative(p: Poly) -> Poly:
    return poly(i * p[i] for i in range(1, len(p)))


def value(p: Poly, x: Q) -> Q:
    result = Q(0)
    for coefficient in reversed(p):
        result = result * x + coefficient
    return result


def magnitude(p: Poly, radius: Q) -> Q:
    return value(tuple(abs(c) for c in p), radius)


def divide(a: Poly, b: Poly) -> tuple[Poly, Poly]:
    if not b:
        raise ZeroDivisionError("zero polynomial divisor")
    quotient = [Q(0)] * max(0, len(a) - len(b) + 1)
    remainder = a
    for _ in range(len(quotient)):
        if len(remainder) < len(b):
            break
        shift = len(remainder) - len(b)
        coefficient = remainder[-1] / b[-1]
        quotient[shift] = coefficient
        subtrahend = (Q(0),) * shift + scale(b, -coefficient)
        remainder = plus(remainder, subtrahend)
    return poly(quotient), remainder


def bezout(a: Poly, b: Poly) -> tuple[Poly, Poly, Poly]:
    """Return monic gcd, u, v so that ua + vb = gcd."""
    one = poly([1])
    r, s, t = a, one, ()
    next_r, next_s, next_t = b, (), one
    for _ in range(len(b) + 1):
        if not next_r:
            break
        q, rem = divide(r, next_r)
        r, next_r = next_r, rem
        minus_q = scale(q, Q(-1))
        s, next_s = next_s, plus(s, times(minus_q, next_s))
        t, next_t = next_t, plus(t, times(minus_q, next_t))
    if not r:
        return (), (), ()
    multiplier = 1 / r[-1]
    return scale(r, multiplier), scale(s, multiplier), scale(t, multiplier)


def squarefree(p: Poly) -> Poly:
    if len(p) < 2:
        raise ValueError("a root record needs a nonconstant polynomial")
    gcd, _, _ = bezout(p, derivative(p))
    h, remainder = divide(p, gcd)
    assert not remainder
    return scale(h, 1 / h[-1])


def resolution(epsilon: Q) -> int:
    """Return n with 2**(-n) < epsilon, for a positive rational epsilon."""
    if epsilon <= 0:
        raise ValueError("positive precision bound required")
    return max(0, epsilon.denominator.bit_length() - epsilon.numerator.bit_length() + 2)


def crossing_reader(p: Poly, left: Q, right: Q, n: int) -> Interval:
    left_sign = value(p, left) > 0
    for _ in range(max(0, n) + ceil(right - left) + 1):
        midpoint = (left + right) / 2
        y = value(p, midpoint)
        if not y:
            return midpoint, midpoint
        if (y > 0) == left_sign:
            left = midpoint
        else:
            right = midpoint
    return left, right


@dataclass(frozen=True)
class RootRecord:
    p: Poly
    left: Q
    right: Q

    def __post_init__(self):
        object.__setattr__(self, "p", poly(self.p))
        object.__setattr__(self, "left", Q(self.left))
        object.__setattr__(self, "right", Q(self.right))
        l, r, p = self.left, self.right, self.p
        if l >= r or value(p, l) * value(p, r) >= 0:
            raise ValueError("endpoints must give a strict sign crossing")
        c, w = (l + r) / 2, (r - l) / 2
        radius = 1 + max(abs(l), abs(r))
        threshold = magnitude(derivative(derivative(p)), radius) * w
        if abs(value(derivative(p), c)) <= threshold:
            raise ValueError("interval fails the divided-difference test")

    def read(self, n: int) -> Interval:
        return crossing_reader(self.p, self.left, self.right, n)


def rational(x: Q) -> RootRecord:
    x = Q(x)
    return RootRecord(poly([-x, 1]), x - 1, x + 1)


def sign_annihilated(p: Poly, read: Reader) -> int:
    """The supplied nonzero p must annihilate the value of read."""
    if not p:
        raise ValueError("annihilator must be nonzero")
    first = next(i for i, coefficient in enumerate(p) if coefficient)
    bound = min(Q(1, 4), abs(p[first]) / (8 * (1 + sum(map(abs, p[first + 1:])))))
    left, right = read(resolution(bound))
    return int(left > 0) - int(right < 0)


def mesh(h: Poly, radius: Q) -> tuple[int, Q]:
    gcd, _, v = bezout(h, derivative(h))
    if gcd != poly([1]):
        raise ValueError("squarefree polynomial required")
    b = max(Q(1), magnitude(v, radius))
    lipschitz = 1 + magnitude(derivative(derivative(h)), radius)
    precision = resolution(1 / (32 * b * lipschitz))
    return precision, Q(1, 1 << precision)


def normalize(p: Poly, read: Reader) -> RootRecord:
    """The nonconstant p must annihilate the supplied provisional value."""
    h = squarefree(p)
    left, right = read(0)
    radius = 4 + ceil(max(abs(left), abs(right)))
    n, delta = mesh(h, Q(radius))
    left, right = read(n)
    centre = (left + right) / 2
    return RootRecord(h, centre - 2 * delta, centre + 2 * delta)


def roots(p: Poly) -> list[RootRecord]:
    if not p:
        raise ValueError("the zero polynomial has every scalar as a root")
    if len(p) == 1:
        return []
    h = squarefree(p)
    radius = 3 + ceil(sum(map(abs, h[:-1])))
    _, delta = mesh(h, Q(radius + 1))
    left, previous = Q(-radius), value(h, Q(-radius))
    result = []
    for _ in range(int(2 * radius / delta)):
        right = left + delta
        current = value(h, right)
        if not current:
            result.append(rational(right))
        elif previous * current < 0:
            # This sufficiently fine mesh already passes the record check.
            result.append(RootRecord(h, left, right))
        left, previous = right, current
    return result


def check_examples() -> None:
    h = poly([-2, 0, 1])
    positive = RootRecord(h, Q(1), Q(3, 2))
    repeated = times(times(h, h), poly([3, 1]))
    converted = normalize(repeated, positive.read)
    assert converted.p == times(h, poly([3, 1]))
    l, r = converted.read(60)
    a, b = positive.read(60)
    assert max(l, a) <= min(r, b)
    assert l * l < 2 < r * r
    assert sign_annihilated(converted.p, converted.read) == 1
    pair = roots(times(h, h))
    assert [sign_annihilated(t.p, t.read) for t in pair] == [-1, 1]
    grid_hits = roots(poly([-1, 0, 1]))
    assert [t.read(8) for t in grid_hits] == [(Q(-1), Q(-1)), (Q(1), Q(1))]
    tiny = rational(Q(1, 1 << 80))
    assert sign_annihilated(tiny.p, tiny.read) == 1

    def square_minus_two(n: int) -> Interval:
        a, b = positive.read(n + 3)
        return a * a - 2, b * b - 2

    assert sign_annihilated(poly([0, 0, 1]), square_minus_two) == 0
    try:
        RootRecord(poly([0, -1, 0, 1]), Q(-2), Q(2))
    except ValueError:
        pass
    else:
        raise AssertionError("accepted an interval with three roots")
    print("Passed: irrational root, repeated annihilator, crossing and grid roots, "
          "tiny positive scalar, exact zero, invalid record.")


if __name__ == "__main__":
    check_examples()
