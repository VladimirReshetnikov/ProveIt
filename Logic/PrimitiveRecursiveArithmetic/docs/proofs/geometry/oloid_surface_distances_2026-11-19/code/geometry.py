"""Unit oloid geometry and outward rational boxes. Uses only Python integers.
The endpoints of every public box are integers in units of 1/SCALE.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt

SCALE = 10**14
UNIT = 10**42

# h = tan(t/2), ruling fraction s, sign of y, sign of z
POINTS = {
    "P1": (F(1, 5), F(1, 6), 1, 1),
    "P2": (F(9, 10), F(7, 10), 1, 1),
    "P3": (F(3, 2), F(2, 5), 1, -1),
    "P4": (F(1, 2), F(3, 11), 1, -1),
    "P5": (F(7, 6), F(1, 8), -1, 1),
    "P6": (F(2, 3), F(11, 13), -1, 1),
    "P7": (F(4, 3), F(8, 11), -1, -1),
    "P8": (F(1, 3), F(4, 7), -1, -1),
    "P9": (F(1), F(5, 9), 1, 1),
    "P10": (F(7, 8), F(19, 20), -1, 1),
}


def ceildiv(a, b):
    return -((-a) // b)


class I:
    """Closed interval with endpoints in units of 1/UNIT."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        assert lo <= hi
        self.lo, self.hi = lo, hi

    def __add__(self, other):
        other = iv(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-iv(other))

    def __rsub__(self, other):
        return iv(other) + (-self)

    def __mul__(self, other):
        other = iv(other)
        products = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return I(min(products) // UNIT, ceildiv(max(products), UNIT))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = iv(other)
        assert other.lo > 0
        rec = I(UNIT**2 // other.hi, ceildiv(UNIT**2, other.lo))
        return self * rec

    def __rtruediv__(self, other):
        return iv(other) / self

    def sqrt(self):
        # The expression being rooted is known to be nonnegative.
        assert self.hi >= 0
        return I(isqrt(max(0, self.lo) * UNIT), isqrt(self.hi * UNIT) + 1)

    def widen(self, e):
        return I(self.lo - e, self.hi + e)

    def export(self):
        return (self.lo * SCALE // UNIT, ceildiv(self.hi * SCALE, UNIT))


def iv(x):
    if isinstance(x, I):
        return x
    x = F(x)
    return I(x.numerator * UNIT // x.denominator, ceildiv(x.numerator * UNIT, x.denominator))


def arctan_small(x):
    # Alternating Taylor polynomial, with the first omitted term as remainder.
    assert 0 <= x.lo and 2 * x.hi <= UNIT
    square = x * x
    term, total = x, iv(0)
    for k in range(52):
        total += (-1)**k * term / (2*k + 1)
        term *= square
    return total.widen(ceildiv(term.hi, 105))


PI = 16 * arctan_small(iv(F(1, 5))) - 4 * arctan_small(iv(F(1, 239)))
ROOT2, ROOT3 = iv(2).sqrt(), iv(3).sqrt()
ANGLE = 2 * PI / 3


def arctan(x):
    # tan(alpha/2)=tan(alpha)/(1+sqrt(1+tan(alpha)^2)).
    return 2 * arctan_small(x / (1 + (1 + x*x).sqrt()))


def log_pos(x):
    # log x=2*atanh((x-1)/(x+1)); all applications have 1<=x<=4.
    y = (x - 1) / (x + 1)
    y = I(max(0, y.lo), y.hi)
    square = y * y
    term, total = y, iv(0)
    for k in range(85):
        total += term / (2*k + 1)
        term *= square
    rem = 2 * term / (171 * (1 - square))
    return 2*total + I(0, rem.hi)


def cosine(t):
    square = t*t
    term, total = iv(1), iv(0)
    for k in range(31):
        total += (-1)**k * term
        term = term * square / ((2*k + 1)*(2*k + 2))
    return total.widen(term.hi)


def lower_arc(c):
    """Planar boundary a in terms of the cosine of its natural arclength."""
    c = I(max(c.lo, -UNIT//2), min(c.hi, UNIT))
    rad = ((1 - c) * (1 + 2*c)).sqrt()
    absc = ROOT2 * c
    if c.lo + c.hi >= 0:
        angle = 2 * arctan(rad / ((1 + c).sqrt() + absc))
    else:
        angle = PI - 2 * arctan(rad / ((1 + c).sqrt() - absc))
    return (2 * ROOT3 / 9 * (ROOT2*rad + angle),
            ROOT3 / 9 * (4*(1-c) + log_pos(2/(1+c))))


W = 2 * ROOT3 * PI / 9
K = ROOT3 / 9 * (6 + log_pos(iv(4)))
H = K + ROOT3


def arc_fraction(f):
    if f == 0:
        return iv(0), iv(0)
    if f == 1:
        return W, K
    return lower_arc(cosine(iv(f)*ANGLE))


def gate(g, f):
    assert 0 <= f <= 1
    if g == "L":
        return iv(0), iv(f)*ROOT3
    if g == "R":
        return W, K + iv(f)*ROOT3
    x, y = arc_fraction(f)
    if g == "A":
        return x, y
    if g == "B":
        return W - x, H - y
    raise ValueError(g)


@lru_cache(maxsize=None)
def gate_box(g, f):
    return tuple(x.export() for x in gate(g, f))


@lru_cache(maxsize=None)
def point_box(label):
    h, s, _, _ = POINTS[label]
    c = (1-h*h)/(1+h*h)
    ax, ay = lower_arc(iv(c))
    bx, by = lower_arc(iv(-c/(1+c)))
    return tuple(v.export() for v in ((1-iv(s))*ax + iv(s)*(W-bx),
                                      (1-iv(s))*ay + iv(s)*(H-by)))


def xyz_box(label):
    h, s, sign_y, sign_z = POINTS[label]
    c = (1-h*h)/(1+h*h)
    u = 2*h/(1+h*h)
    a = -F(1, 2)-c
    b = F(1, 2)-c/(1+c)
    return tuple(v.export() for v in
                 (iv((1-s)*a + s*b), iv(sign_y*(1-s)*u),
                  iv(sign_z*s) * iv(1+2*c).sqrt() / iv(1+c)))


if __name__ == "__main__":
    for k in POINTS:
        print(k, xyz_box(k), point_box(k))
