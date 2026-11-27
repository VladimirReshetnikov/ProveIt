"""Exact rational certificate for the five-node phase-map Jacobian (Python 3)."""
from dataclasses import dataclass
from fractions import Fraction as Q
from math import isqrt


@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q

    @staticmethod
    def of(value):
        return value if isinstance(value, Interval) else Interval(Q(value), Q(value))

    def __add__(self, other):
        b = self.of(other)
        return Interval(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-self.of(other))

    def __rsub__(self, other):
        return self.of(other) + (-self)

    def __mul__(self, other):
        b = self.of(other)
        products = [x * y for x in (self.lo, self.hi) for y in (b.lo, b.hi)]
        return Interval(min(products), max(products))

    __rmul__ = __mul__

    def __truediv__(self, other):
        b = self.of(other)
        assert b.lo * b.hi > 0
        return self * Interval(1 / b.hi, 1 / b.lo)


def sqrt_bounds(a, scale=10**12):
    a = Interval.of(a)
    assert a.lo >= 0
    def lower(x):
        return isqrt(x.numerator * scale**2 // x.denominator)
    return Interval(Q(lower(a.lo), scale), Q(lower(a.hi) + 1, scale))


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def symbol(h):
    n = len(h)
    return [k**3 * sum(h[i] * h[i+k] for i in range(n-k)) for k in range(1,n)]


def derivative(h, g):
    n = len(h)
    return [k**3 * sum(h[i] * g[i+k] + g[i] * h[i+k] for i in range(n-k))
            for k in range(1,n)]


def jacobian():
    # Integer powers bound log(3)/log(2), without a transcendental routine.
    assert 2**15849 < 3**10000 < 2**15850
    alpha = Interval(Q(15849, 10000), Q(15850, 10000))
    h = [1, 6, -1, -20, 14]
    a, b, c, d = symbol(h)
    assert (a,b,c,d) == (-260,-1080,1728,896)
    da = [derivative(h, [0,1,-2,1,0]), derivative(h,[0,0,1,-2,1])]
    e, f, g = 4*a*d, 2*b*(a+d), (a-d)**2 + b*b - c*c
    delta = sqrt_bounds(f*f - 4*e*g)
    root_boxes = [(-895, -894), (-580, -579)]
    entry_boxes = [[(405,408), (-1290,-1280)], [(-161,-158),(-1440,-1420)]]
    rows = []
    for sign in [1,-1]:
        x = (-f + sign*delta)/(2*e)
        y = sqrt_bounds(1-x*x)
        z2r, z2i = 2*x*x-1, 2*x*y
        wr, wi = -(a+b*x+d*z2r)/c, -(b*y+d*z2i)/c
        u = (-b*y-2*d*z2i, b*x+2*d*z2r)
        v = (-c*wi, c*wr)
        low, high = root_boxes[len(rows)]
        assert Q(low,1000) < x.lo <= x.hi < Q(high,1000)
        row = []
        for aa, bb, cc, dd in da:
            deriv = (aa+bb*x+cc*wr+dd*z2r, bb*y+cc*wi+dd*z2i)
            row.append((-cross(u,deriv) + alpha*cross(deriv,v))/cross(u,v))
        for entry, (low, high) in zip(row, entry_boxes[len(rows)]):
            assert Q(low,10000) < entry.lo <= entry.hi < Q(high,10000)
        rows.append(row)
    determinant = cross(rows[0], rows[1])
    assert Q(-8,1000) < determinant.lo <= determinant.hi < Q(-7,1000)
    return determinant


if __name__ == "__main__":
    jacobian()
    print("Certified -0.008 < det(J) < -0.007 using rational arithmetic.")
