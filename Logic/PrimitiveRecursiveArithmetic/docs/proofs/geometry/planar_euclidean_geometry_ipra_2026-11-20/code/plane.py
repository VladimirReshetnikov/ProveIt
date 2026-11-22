"""Exact planar constructions in the real algebraic field.

Points and vectors carry exact Scalar components. Line stores a base point
and a nonzero direction. Circle stores a center and the squared radius.
Infinite intersections return the original locus.
"""
from dataclasses import dataclass
from fractions import Fraction

from exact_scalars import Scalar


def scalar(value):
    if isinstance(value, Scalar):
        return value
    if isinstance(value, (int, Fraction)):
        return Scalar.rational(value)
    raise TypeError("expected an exact scalar, integer or Fraction")


@dataclass(frozen=True)
class Point:
    x: Scalar
    y: Scalar

    def __post_init__(self):
        object.__setattr__(self, "x", scalar(self.x))
        object.__setattr__(self, "y", scalar(self.y))

    def __add__(self, v):
        return Point(self.x + v.x, self.y + v.y)

    def __sub__(self, v):
        return Point(self.x - v.x, self.y - v.y)

    def scaled(self, k):
        return Point(self.x * k, self.y * k)

    def normal(self):
        return Point(-self.y, self.x)


def dot(u, v):
    return u.x * v.x + u.y * v.y


def det(u, v):
    return u.x * v.y - u.y * v.x


def norm_sq(u):
    return dot(u, u)


def between(a, p, b):
    return det(b - a, p - a) == 0 and dot(p - a, p - b) <= 0


def congruent(a, b, c, d):
    return norm_sq(b - a) == norm_sq(d - c)


@dataclass(frozen=True)
class Line:
    base: Point
    direction: Point

    def __post_init__(self):
        if norm_sq(self.direction) == 0:
            raise ValueError("a line requires a nonzero direction")

    @classmethod
    def through(cls, a, b):
        return cls(a, b - a)

    def foot(self, p):
        u = self.direction
        return self.base + u.scaled(dot(p - self.base, u) / norm_sq(u))

    def contains(self, p):
        return det(p - self.base, self.direction) == 0


@dataclass(frozen=True)
class Circle:
    center: Point
    squared_radius: Scalar

    def __post_init__(self):
        s = scalar(self.squared_radius)
        if s < 0:
            raise ValueError("squared radius must be nonnegative")
        object.__setattr__(self, "squared_radius", s)

    def contains(self, p):
        return norm_sq(p - self.center) == self.squared_radius


def line_line(a, b):
    """A tuple of finite solutions, or a Line for an identical locus."""
    k = det(a.direction, b.direction)
    if k == 0:
        return a if a.contains(b.base) else ()
    t = det(b.base - a.base, b.direction) / k
    return (a.base + a.direction.scaled(t),)


def _offsets(center, direction, h_squared):
    if h_squared < 0:
        return ()
    if h_squared == 0:
        return (center,)
    offset = direction.scaled(h_squared.sqrt())
    return center - offset, center + offset


def line_circle(line, circle):
    f = line.foot(circle.center)
    d = circle.squared_radius - norm_sq(f - circle.center)
    return _offsets(f, line.direction, d / norm_sq(line.direction))


def circle_circle(a, b):
    """A tuple of finite solutions, or a Circle for coincident nonpoint circles."""
    u = b.center - a.center
    k = norm_sq(u)
    if k == 0:
        if a.squared_radius != b.squared_radius:
            return ()
        return (a.center,) if a.squared_radius == 0 else a
    t = (k + a.squared_radius - b.squared_radius) / (2 * k)
    return _offsets(a.center + u.scaled(t), u.normal(),
                    a.squared_radius / k - t * t)


def nine_point_circle(a, b, c):
    """Return the nine-point circle and the three triples of defining points."""
    if det(b - a, c - a) == 0:
        raise ValueError("a circumcenter requires a noncollinear triangle")
    vertices = (a, b, c)
    opp = ((b, c), (c, a), (a, b))
    midpoints = tuple((u + v).scaled(Fraction(1, 2)) for u, v in opp)
    bisectors = [Line(m, (v-u).normal()) for m, (u,v) in zip(midpoints, opp)]
    (o,) = line_line(bisectors[0], bisectors[1])
    h = a + b + c - o.scaled(2)
    center = (o + h).scaled(Fraction(1, 2))
    feet = tuple(Line.through(u, v).foot(p) for p, (u,v) in zip(vertices, opp))
    euler_points = tuple((p + h).scaled(Fraction(1, 2)) for p in vertices)
    return Circle(center, norm_sq(a-o) / 4), midpoints, feet, euler_points
