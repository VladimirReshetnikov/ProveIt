#!/usr/bin/env python3
"""Finite odd dyadic-filter certificates using integer interval arithmetic.

Run `python3 code/verify_finite.py` from the archive directory. Standard output
reproduces data/finite_certificate.txt. There are no third-party dependencies.

The variable s lies in (0,1) and is the penultimate radius. Write
w=2 sin(b/2), where b is the last angular deviation from the negative axis.
The penultimate and last squared defects d_j=1-|1+z^(2^j)|^2 are equal when
s*w^2+w=3*s-s^3. We take the positive root of this quadratic. Set
v_last=s^2, C_last=1-w^2/2 and v_pen=s, C_pen=w/2, where C_j=cos(alpha_j).
Successive earlier entries are v_prev=sqrt(v), C_prev=sqrt((1-C)/2).
These steps select the left-half-plane branch. An endpoint sign change of
d_0-d_last gives an exact triple-contact parameter by continuity.

In coordinates (log(v_last), b), a gradient of d_j divided by a positive
factor is g_j=(C_j-v_j, -(-1)^j sqrt(1-C_j^2)). We verify that the three
ordered determinants det(g_0,g_pen), det(g_pen,g_last), det(g_last,g_0)
are strictly negative, and that every inactive defect is strictly larger.
The companion paper proves why these checks certify a global unique optimum
up to complex conjugation.
"""

from dataclasses import dataclass
from math import isqrt


WORK_BITS = 256
BRACKET_BITS = 24
UNIT = 1 << WORK_BITS


def ceil_div(a, b):
    return -((-a) // b)


@dataclass(frozen=True)
class Interval:
    """Closed [lo/UNIT, hi/UNIT]. Each operation rounds outwards."""

    lo: int
    hi: int

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError("empty enclosure")

    @classmethod
    def integer(cls, k):
        return cls(k * UNIT, k * UNIT)

    def __add__(self, other):
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other):
        return Interval(self.lo - other.hi, self.hi - other.lo)

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __mul__(self, other):
        endpoints = [x * y for x in (self.lo, self.hi)
                     for y in (other.lo, other.hi)]
        return Interval(min(endpoints) // UNIT, ceil_div(max(endpoints), UNIT))

    def __truediv__(self, other):
        if other.lo <= 0:
            raise ValueError("denominator must be strictly positive")
        endpoints = [(x * UNIT, y) for x in (self.lo, self.hi)
                     for y in (other.lo, other.hi)]
        return Interval(min(x // y for x, y in endpoints),
                        max(ceil_div(x, y) for x, y in endpoints))

    def sqrt(self):
        if self.lo < 0:
            raise ValueError("negative square-root lower endpoint")
        upper = isqrt(self.hi * UNIT)
        if upper * upper < self.hi * UNIT:
            upper += 1
        return Interval(isqrt(self.lo * UNIT), upper)


ONE = Interval.integer(1)
TWO = Interval.integer(2)
THREE = Interval.integer(3)
FOUR = Interval.integer(4)


def angular_data(n, s):
    """Return [(v_j, cos(alpha_j))] in exponent order 1,2,...,2^(n-1)."""
    s2 = s * s
    h = s * (THREE - s2)
    w = TWO * h / (ONE + (ONE + FOUR * s * h).sqrt())
    if not (0 < w.lo <= w.hi < TWO.lo):
        raise ArithmeticError("invalid angular parameter")
    data = [(s2, ONE - w * w / TWO), (s, w / TWO)]
    for _ in range(n - 2):
        v, c = data[-1]
        data.append((v.sqrt(), ((ONE - c) / TWO).sqrt()))
    return list(reversed(data))


def defect(entry):
    v, c = entry
    return v * (TWO * c - v)


def s_interval(left, right):
    shift = WORK_BITS - BRACKET_BITS
    return Interval(left << shift, right << shift)


def difference_at(n, k):
    data = angular_data(n, s_interval(k, k))
    return defect(data[0]) - defect(data[-1])


def gradient(j, entry):
    v, c = entry
    sine = (ONE - c * c).sqrt()
    return (c - v, sine if j % 2 else -sine)


def determinant(a, b):
    return a[0] * b[1] - a[1] * b[0]


def prove(n):
    left = 1 << (BRACKET_BITS - n)
    right = 3 << (BRACKET_BITS - 2)
    if difference_at(n, left).lo <= 0 or difference_at(n, right).hi >= 0:
        raise ArithmeticError("initial bracket failed")
    while right - left > 1:
        mid = (right + left) // 2
        difference = difference_at(n, mid)
        if difference.lo > 0:
            left = mid
        elif difference.hi < 0:
            right = mid
        else:
            raise ArithmeticError("sign unresolved at working precision")
    left_sign = difference_at(n, left)
    right_sign = -difference_at(n, right)
    s_bracket = s_interval(left, right)
    data = angular_data(n, s_bracket)
    r = data[0][0]
    if not (s_bracket.hi < UNIT // 2 and (TWO * r * r).lo > UNIT):
        raise ArithmeticError("root not in the stated search interval")
    if not all(0 < c.lo <= c.hi < ONE.lo for _, c in data):
        raise ArithmeticError("angular branch not certified")
    defects = list(map(defect, data))
    if defects[-1].lo <= 0 or defects[-1].hi >= ONE.lo:
        raise ArithmeticError("invalid contact defect")
    g0 = gradient(0, data[0])
    gp = gradient(n - 2, data[-2])
    gf = gradient(n - 1, data[-1])
    margins = [-determinant(g0, gp), -determinant(gp, gf), -determinant(gf, g0)]
    minimum_det = min(m.lo for m in margins)
    inactive = [d - defects[-1] for d in defects[1:-2]]
    minimum_slack = min(m.lo for m in inactive)
    if min(left_sign.lo, right_sign.lo, minimum_det) <= 0:
        raise ArithmeticError("endpoint sign or gradient determinant failed")
    if minimum_slack <= 0:
        raise ArithmeticError("inactive index failed")

    def log2_lower(k):
        # k/UNIT >= 2^(bit_length(k)-1-WORK_BITS).
        return k.bit_length() - 1 - WORK_BITS

    return (left, log2_lower(left_sign.lo), log2_lower(right_sign.lo),
            log2_lower(minimum_det),
            log2_lower(minimum_slack))


def main():
    print("Dyadic interval certificates for odd n from 5 through 19")
    print("Working precision: 256 binary fractional bits.")
    print("For each row, s is bracketed by [k, k+1]/2^24.")
    print("s=|z|^(2^(n-2)); d_j=1-|1+z^(2^j)|^2.")
    print("Each bracket also satisfies 2*s<1 and 2*|z|^2>1.")
    print("The last four columns give exponents e of certified lower bounds 2^e.")
    print("left: d_0-d_last at k; right: d_last-d_0 at k+1.")
    print("det: minimum of three negated oriented gradient determinants.")
    print("slack: minimum d_j-d_last over all inactive indices.")
    print()
    print(" n         k  left  right  det  slack")
    for n in range(5, 20, 2):
        k, left, right, det, slack = prove(n)
        print(f"{n:2}   {k:7} {left:5}  {right:5}  {det:3}  {slack:>5}")


if __name__ == "__main__":
    main()
