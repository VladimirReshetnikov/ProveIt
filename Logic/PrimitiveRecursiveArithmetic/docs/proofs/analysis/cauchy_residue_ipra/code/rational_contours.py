"""Exact finite arithmetic accompanying the constructive Cauchy/residue paper.

All arithmetic uses Python integers and Fraction.  These are reference algorithms,
not formal proofs and not a universal primitive-recursive-program interpreter.
Loops have explicit finite bounds.  Dyadic rounding prevents denominator growth
in numerical quadrature without concealing its error.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction as Q
from math import comb
from typing import Callable, Iterable


@dataclass(frozen=True, order=True)
class CQ:
    re: Q = Q(0)
    im: Q = Q(0)

    def __post_init__(self):
        object.__setattr__(self, "re", Q(self.re))
        object.__setattr__(self, "im", Q(self.im))

    @staticmethod
    def coerce(value):
        return value if isinstance(value, CQ) else CQ(Q(value))

    def __add__(self, other):
        other = self.coerce(other)
        return CQ(self.re + other.re, self.im + other.im)

    __radd__ = __add__

    def __neg__(self):
        return CQ(-self.re, -self.im)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        return CQ(self.re * other.re - self.im * other.im,
                  self.re * other.im + self.im * other.re)

    __rmul__ = __mul__

    def inv(self):
        denominator = self.re * self.re + self.im * self.im
        if denominator == 0:
            raise ZeroDivisionError("CQ inverse requires a nonzero point")
        return CQ(self.re / denominator, -self.im / denominator)

    def __truediv__(self, other):
        return self * self.coerce(other).inv()

    def __rtruediv__(self, other):
        return self.coerce(other) * self.inv()

    def __pow__(self, n: int):
        if n < 0:
            return self.inv() ** (-n)
        result, factor = CQ(1), self
        # This loop is bounded by n+1; the square-and-multiply version is faster.
        while n:
            if n & 1:
                result = result * factor
            factor = factor * factor
            n //= 2
        return result

    def norm1(self) -> Q:
        return abs(self.re) + abs(self.im)

    def rounded(self, bits: int):
        """Nearest dyadics, with total CQ taxicab error <= 2^-bits."""
        if bits < 0:
            raise ValueError("bits must be nonnegative")
        scale = 1 << bits

        def one(x: Q) -> Q:
            # floor(scale*x+1/2), including negative x; ties may round upwards.
            numerator = (2 * x.numerator * scale + x.denominator) // (2 * x.denominator)
            return Q(numerator, scale)

        return CQ(one(self.re), one(self.im))

    def json(self):
        return {"re": str(self.re), "im": str(self.im)}


Edge = tuple[CQ, CQ]
Triangle = tuple[CQ, CQ, CQ]
Function = Callable[[CQ], CQ]


def dyadic(n: int) -> Q:
    if n < 0:
        return Q(1 << (-n))
    return Q(1, 1 << n)


def triangle_edges(triangle: Triangle) -> list[Edge]:
    a, b, c = triangle
    return [(a, b), (b, c), (c, a)]


def split_triangle(triangle: Triangle) -> tuple[Triangle, ...]:
    a, b, c = triangle
    ab, bc, ca = (a + b) / 2, (b + c) / 2, (c + a) / 2
    return ((a, ab, ca), (ab, b, bc), (ca, bc, c), (ab, bc, ca))


def subdivide_triangles(triangles: Iterable[Triangle], depth: int) -> list[Triangle]:
    if depth < 0:
        raise ValueError("depth must be nonnegative")
    result = list(triangles)
    for _ in range(depth):
        result = [small for triangle in result for small in split_triangle(triangle)]
    return result


def split_edge(edge: Edge, depth: int) -> list[Edge]:
    if depth < 0:
        raise ValueError("depth must be nonnegative")
    a, b = edge
    count = 1 << depth
    step = (b - a) / count
    return [(a + step * j, a + step * (j + 1)) for j in range(count)]


def edge_chain(edges: Iterable[Edge], coefficient: int = 1) -> dict[Edge, int]:
    """Canonical signed unoriented-edge dictionary; discard zero edges."""
    counts = defaultdict(int)
    for a, b in edges:
        if a < b:
            counts[(a, b)] += coefficient
        elif b < a:
            counts[(b, a)] -= coefficient
    return {edge: n for edge, n in counts.items() if n != 0}


def add_chains(*chains: dict[Edge, int]) -> dict[Edge, int]:
    counts = defaultdict(int)
    for chain in chains:
        for edge, n in chain.items():
            counts[edge] += n
    return {edge: n for edge, n in counts.items() if n != 0}


def triangles_boundary(triangles: Iterable[Triangle]) -> dict[Edge, int]:
    return edge_chain(edge for triangle in triangles for edge in triangle_edges(triangle))


def trap_edge(f: Function, edge: Edge, depth: int = 0, bits: int | None = None) -> CQ:
    """Finite trapezoidal quadrature, with 2^depth subedges."""
    if depth < 0:
        raise ValueError("depth must be nonnegative")
    a, b = edge
    count = 1 << depth
    step = (b - a) / count

    def value(z: CQ) -> CQ:
        exact = f(z)
        return exact if bits is None else exact.rounded(bits)

    total = (value(a) + value(b)) / 2
    for j in range(1, count):
        total += value(a + step * j)
    return step * total


def trap_chain(f: Function, edges: Iterable[Edge], depth: int = 0,
               bits: int | None = None) -> CQ:
    return sum((trap_edge(f, edge, depth, bits) for edge in edges), CQ())


def diameter(triangle: Triangle) -> Q:
    return max((b - a).norm1() for a, b in triangle_edges(triangle))


def perimeter(edges: Iterable[Edge]) -> Q:
    return sum(((b - a).norm1() for a, b in edges), Q())


def triangle_bound(triangle: Triangle, depth: int, k: int, bits: int) -> Q:
    """The paper's finite bound, conditional on its UD sample inequalities."""
    d = diameter(triangle)
    p = perimeter(triangle_edges(triangle))
    return d * p * dyadic(k) + p * dyadic(bits) * ((1 << (depth + 1)) + d)


@dataclass(frozen=True)
class Rectangle:
    xmin: Q
    xmax: Q
    ymin: Q
    ymax: Q

    def __post_init__(self):
        for name in ("xmin", "xmax", "ymin", "ymax"):
            object.__setattr__(self, name, Q(getattr(self, name)))
        if not (self.xmin < self.xmax and self.ymin < self.ymax):
            raise ValueError("a rectangle must have positive side lengths")

    def strictly_contains(self, other: Rectangle) -> bool:
        return (self.xmin < other.xmin < other.xmax < self.xmax
                and self.ymin < other.ymin < other.ymax < self.ymax)

    def interior_contains(self, z: CQ) -> bool:
        return self.xmin < z.re < self.xmax and self.ymin < z.im < self.ymax

    def disjoint(self, other: Rectangle) -> bool:
        # Strict separation prevents touching holes as well as overlapping ones.
        return (self.xmax < other.xmin or other.xmax < self.xmin
                or self.ymax < other.ymin or other.ymax < self.ymin)


def rectangle_boundary(rect: Rectangle, xs: Iterable[Q] = (),
                       ys: Iterable[Q] = ()) -> list[Edge]:
    """CCW boundary split at every supplied grid coordinate on that side."""
    xvals = sorted({rect.xmin, rect.xmax} | {x for x in xs if rect.xmin < x < rect.xmax})
    yvals = sorted({rect.ymin, rect.ymax} | {y for y in ys if rect.ymin < y < rect.ymax})
    bottom = [(CQ(x, rect.ymin), CQ(xx, rect.ymin)) for x, xx in zip(xvals, xvals[1:])]
    right = [(CQ(rect.xmax, y), CQ(rect.xmax, yy)) for y, yy in zip(yvals, yvals[1:])]
    top = [(CQ(xx, rect.ymax), CQ(x, rect.ymax)) for x, xx in reversed(list(zip(xvals, xvals[1:])))]
    left = [(CQ(rect.xmin, yy), CQ(rect.xmin, y)) for y, yy in reversed(list(zip(yvals, yvals[1:])))]
    return bottom + right + top + left


def rectangle_with_holes(outer: Rectangle, holes: list[Rectangle]):
    """Produce a finite rational filling and its identically split boundaries.

    The common rectangular coordinate grid ensures no T-junctions.  Every cell
    is split into two positive triangles.  Hole cells are omitted.
    """
    if any(not outer.strictly_contains(hole) for hole in holes):
        raise ValueError("all holes must be strictly inside the outer rectangle")
    if any(not holes[i].disjoint(holes[j]) for i in range(len(holes))
           for j in range(i + 1, len(holes))):
        raise ValueError("holes must be pairwise positively separated")
    xs = sorted({outer.xmin, outer.xmax} | {x for h in holes for x in (h.xmin, h.xmax)})
    ys = sorted({outer.ymin, outer.ymax} | {y for h in holes for y in (h.ymin, h.ymax)})
    triangles = []
    for x0, x1 in zip(xs, xs[1:]):
        for y0, y1 in zip(ys, ys[1:]):
            center = CQ((x0 + x1) / 2, (y0 + y1) / 2)
            if any(hole.interior_contains(center) for hole in holes):
                continue
            a, b, c, d = CQ(x0, y0), CQ(x1, y0), CQ(x1, y1), CQ(x0, y1)
            triangles.extend(((a, b, c), (a, c, d)))
    outer_edges = rectangle_boundary(outer, xs, ys)
    hole_edges = [rectangle_boundary(hole, xs, ys) for hole in holes]
    return triangles, outer_edges, hole_edges


def distance_to_axis_edge(point: CQ, edge: Edge) -> Q:
    a, b = edge

    def gap(value: Q, x: Q, y: Q) -> Q:
        lo, hi = min(x, y), max(x, y)
        return lo - value if value < lo else value - hi if value > hi else Q()

    if a.re == b.re:
        return abs(point.re - a.re) + gap(point.im, a.im, b.im)
    if a.im == b.im:
        return abs(point.im - a.im) + gap(point.re, a.re, b.re)
    raise ValueError("this clearance routine is for axis-parallel edges")


def reciprocal_lipschitz_bound(edges: list[Edge], poles: list[tuple[CQ, CQ]]) -> Q:
    """L for f(z)=sum residue/(z-pole), using explicit positive clearances.

    |u^-1|_1 <= 2/|u|_1 and the inverse-difference identity imply
    |f(z)-f(w)|_1 <= L |z-w|_1 on each contour edge.
    """
    result = Q()
    for center, residue in poles:
        clearance = min(distance_to_axis_edge(center, edge) for edge in edges)
        if clearance <= 0:
            raise ValueError("pole lies on a contour edge")
        result += residue.norm1() * (Q(2) / clearance) ** 2
    return result


def reciprocal_derivative_lipschitz_bound(edges: list[Edge],
                                        poles: list[tuple[CQ, CQ]]) -> Q:
    """K=2*sum |residue|*U^3 for the derivative, U=2/clearance.

    Both the derivative difference and the Taylor remainder follow from
    exact rational identities for reciprocals.  In particular, with h=v-u,
    1/v-1/u+h/u^2=h^2/(u^2*v), so the Taylor remainder coefficient is K/2.
    """
    result = Q()
    for center, residue in poles:
        clearance = min(distance_to_axis_edge(center, edge) for edge in edges)
        if clearance <= 0:
            raise ValueError("pole lies on a contour edge")
        result += 2 * residue.norm1() * (Q(2) / clearance) ** 3
    return result


def quadrature_error_bound(edges: list[Edge], lipschitz: Q, depth: int, bits: int) -> Q:
    """Error to the named integral: Lipschitz interpolation + rounding.

    A coarse cell of length h has interpolation error <= L*h/2.  Thus
    |T_m-I|_1 <= L*sum_e |e|_1^2/2^(m+1).  Evaluation adds P*2^-bits.
    This bound is intentionally conservative and uses no floating point.
    """
    squares = sum(((b - a).norm1() ** 2 for a, b in edges), Q())
    return lipschitz * squares * dyadic(depth + 1) + perimeter(edges) * dyadic(bits)


def quadrature_derivative_error_bound(edges: list[Edge], derivative_lipschitz: Q,
                                     depth: int, bits: int) -> Q:
    """Reciprocal-sum error K*sum |e|^3/(12*4^m)+P*2^-bits.

    In this package this bound is used only for a supplied sum c_j/(z-a_j),
    with K = 2*sum_j |c_j|_1*U_j^3 and each U_j bounding all inverse
    factors along the contour. The caller supplies these certified bounds.

    The exact reciprocal interpolation identity is
      (1-t)/u+t/v-1/((1-t)*u+t*v)
        = t*(1-t)*(v-u)^2/(u*v*((1-t)*u+t*v)).
    Bounding its three inverse factors by U gives interpolation error
    at most (K/2)*t*(1-t)*h^2.  The normalized trapezoidal average of
    t*(1-t) over N equal pieces is (N^2-1)/(6*N^2)<=1/6.
    Thus the same bound holds against every finer quadrature, and hence
    against the regular name defined in the paper.
    """
    cubes = sum(((b - a).norm1() ** 3 for a, b in edges), Q())
    return derivative_lipschitz * cubes * dyadic(2 * depth) / 12 + perimeter(edges) * dyadic(bits)


def binomial_integral(j: int) -> Q:
    """Exact integral of (1-t^2)^j on [0,1], by finite expansion."""
    return sum((Q((-1) ** k * comb(j, k), 2 * k + 1) for k in range(j + 1)), Q())


def pi_interval(terms: int) -> tuple[Q, Q]:
    """Rational enclosure 4*A_N <= pi <= 4*A_N+4*2^-N.

    A_N integrates sum_{j<N} 2^(-j-1)(1-t^2)^j.  The positive
    geometric remainder is at most 2^-N on [0,1].  The recurrence
    integral_j = (2j/(2j+1))*integral_(j-1) avoids cancellation.
    The identification pi=4*integral_0^1 1/(1+t^2) is proved in the paper.
    """
    if terms < 0:
        raise ValueError("terms must be nonnegative")
    integral, total = Q(1), Q()
    for j in range(terms):
        if j:
            integral *= Q(2 * j, 2 * j + 1)
        total += dyadic(j + 1) * integral
    return 4 * total, 4 * (total + dyadic(terms))


def distance_to_imaginary_interval(z: CQ, lower: Q, upper: Q) -> Q:
    if lower > upper:
        raise ValueError("interval endpoints are reversed")
    imaginary_gap = lower - z.im if z.im < lower else z.im - upper if z.im > upper else Q()
    return abs(z.re) + imaginary_gap


def residue_example():
    outer = Rectangle(-2, 3, -2, 2)
    holes = [Rectangle(Q(-1, 4), Q(1, 4), Q(-1, 4), Q(1, 4)),
             Rectangle(Q(3, 4), Q(5, 4), Q(-1, 4), Q(1, 4))]
    poles = [(CQ(0), CQ(1)), (CQ(1), CQ(2))]
    triangles, outer_edges, hole_edges = rectangle_with_holes(outer, holes)

    def f(z: CQ) -> CQ:
        return sum((residue / (z - center) for center, residue in poles), CQ())

    return f, poles, triangles, outer_edges, hole_edges

