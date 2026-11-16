#!/usr/bin/env python3
"""Exact finite certificates accompanying the iPRA pentagonal-tiling report.

The core Euclidean computations use Q(sqrt(d)) arithmetic implemented with
fractions only.  SymPy is used only for the nested-radical Type 14 local patch;
Matplotlib/Shapely are optional validation and rendering companions.

This file is a reference checker, not an iPRA proof checker.  Its loops and
arithmetic are deliberately finite and primitive-recursive in shape, so that
its predicates can be mirrored by the ProveIt `PR`/`PRAAx` object language.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cmp_to_key
from itertools import combinations, product
from pathlib import Path
from typing import Iterable, Sequence
import argparse
import json
import math
import sys

ROOT = Path(__file__).resolve().parents[1]
FIG = ROOT / "figures"
CERT = ROOT / "certificates"
VERIFY = ROOT / "verification"


def F(x=0, den=1) -> Fraction:
    if isinstance(x, Fraction):
        return x
    return Fraction(x, den)


@dataclass(frozen=True)
class Quad:
    """a + b*sqrt(d), with a,b rational and fixed positive nonsquare d."""

    a: Fraction
    b: Fraction
    d: int

    def __init__(self, a=0, b=0, d: int = 3):
        object.__setattr__(self, "a", F(a))
        object.__setattr__(self, "b", F(b))
        object.__setattr__(self, "d", int(d))
        if self.d <= 0:
            raise ValueError("d must be positive")

    def _coerce(self, other) -> "Quad":
        if isinstance(other, Quad):
            if other.d != self.d:
                raise TypeError(f"quadratic fields differ: {self.d}, {other.d}")
            return other
        return Quad(other, 0, self.d)

    def __add__(self, other):
        o = self._coerce(other)
        return Quad(self.a + o.a, self.b + o.b, self.d)

    __radd__ = __add__

    def __neg__(self):
        return Quad(-self.a, -self.b, self.d)

    def __sub__(self, other):
        return self + (-self._coerce(other))

    def __rsub__(self, other):
        return self._coerce(other) - self

    def __mul__(self, other):
        o = self._coerce(other)
        return Quad(self.a * o.a + self.b * o.b * self.d,
                    self.a * o.b + self.b * o.a, self.d)

    __rmul__ = __mul__

    def conjugate(self):
        return Quad(self.a, -self.b, self.d)

    def norm(self) -> Fraction:
        return self.a * self.a - self.d * self.b * self.b

    def inverse(self):
        n = self.norm()
        if n == 0:
            raise ZeroDivisionError
        c = self.conjugate()
        return Quad(c.a / n, c.b / n, self.d)

    def __truediv__(self, other):
        o = self._coerce(other)
        return self * o.inverse()

    def __rtruediv__(self, other):
        return self._coerce(other) / self

    def __pow__(self, n: int):
        if n < 0:
            return (self.inverse()) ** (-n)
        r = Quad(1, 0, self.d)
        x = self
        while n:
            if n & 1:
                r = r * x
            x = x * x
            n //= 2
        return r

    def sign(self) -> int:
        """Exact sign, using one rational square comparison."""
        a, b, d = self.a, self.b, self.d
        if a == 0:
            return (b > 0) - (b < 0)
        if b == 0:
            return (a > 0) - (a < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        cmpv = a * a - d * b * b
        if a > 0 and b < 0:
            return (cmpv > 0) - (cmpv < 0)
        # a < 0 < b
        return -((cmpv > 0) - (cmpv < 0))

    def __lt__(self, other):
        return (self - other).sign() < 0

    def __le__(self, other):
        return (self - other).sign() <= 0

    def __gt__(self, other):
        return (self - other).sign() > 0

    def __ge__(self, other):
        return (self - other).sign() >= 0

    def __float__(self):
        return float(self.a) + float(self.b) * math.sqrt(self.d)

    def is_integer(self) -> bool:
        return self.b == 0 and self.a.denominator == 1

    def as_int(self) -> int:
        if not self.is_integer():
            raise ValueError(f"not an integer: {self}")
        return self.a.numerator

    def to_json(self):
        return {"a": frac_str(self.a), "b": frac_str(self.b), "d": self.d}

    def __str__(self):
        if self.b == 0:
            return frac_str(self.a)
        if self.a == 0:
            return f"{frac_str(self.b)}*sqrt({self.d})"
        sign = "+" if self.b > 0 else "-"
        return f"{frac_str(self.a)}{sign}{frac_str(abs(self.b))}*sqrt({self.d})"



@dataclass(frozen=True)
class Quartic57:
    """a + b*t over Q(sqrt(57)), where t^2=(6*sqrt(57)-2)/64.

    The positive generator t is cos(C/2) for the Type 14 tile.  This
    degree-four ordered field is sufficient because
    sin(C)=((sqrt(57)-3)/4)*t.  Its sign test is again one exact square
    comparison, now in the already ordered quadratic base field.
    """

    a: Quad
    b: Quad

    @staticmethod
    def base_c() -> Quad:
        return Quad(F(-1, 32), F(3, 32), 57)

    def __init__(self, a=0, b=0):
        def as_base(x):
            if isinstance(x, Quad):
                if x.d != 57:
                    raise TypeError("Quartic57 base must be Q(sqrt(57))")
                return x
            return Quad(x, 0, 57)
        object.__setattr__(self, "a", as_base(a))
        object.__setattr__(self, "b", as_base(b))

    @property
    def d(self) -> int:
        return 57

    def _coerce(self, other) -> "Quartic57":
        if isinstance(other, Quartic57):
            return other
        return Quartic57(other, 0)

    def __add__(self, other):
        o = self._coerce(other)
        return Quartic57(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __neg__(self):
        return Quartic57(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-self._coerce(other))

    def __rsub__(self, other):
        return self._coerce(other) - self

    def __mul__(self, other):
        o = self._coerce(other)
        c = self.base_c()
        return Quartic57(self.a * o.a + self.b * o.b * c,
                         self.a * o.b + self.b * o.a)

    __rmul__ = __mul__

    def conjugate_t(self):
        return Quartic57(self.a, -self.b)

    def inverse(self):
        den = self.a * self.a - self.b * self.b * self.base_c()
        if den == Quad(0, 0, 57):
            raise ZeroDivisionError
        return Quartic57(self.a / den, -self.b / den)

    def __truediv__(self, other):
        return self * self._coerce(other).inverse()

    def __rtruediv__(self, other):
        return self._coerce(other) / self

    def __pow__(self, n: int):
        if n < 0:
            return self.inverse() ** (-n)
        r = Quartic57(1)
        x = self
        while n:
            if n & 1:
                r = r * x
            x = x * x
            n //= 2
        return r

    def sign(self) -> int:
        sa, sb = self.a.sign(), self.b.sign()
        if sb == 0:
            return sa
        if sa == 0:
            return sb  # t is the designated positive root
        if sa == sb:
            return sa
        delta = self.a * self.a - self.b * self.b * self.base_c()
        sd = delta.sign()
        return sd if sa > 0 else -sd

    def __lt__(self, other):
        return (self - other).sign() < 0

    def __le__(self, other):
        return (self - other).sign() <= 0

    def __gt__(self, other):
        return (self - other).sign() > 0

    def __ge__(self, other):
        return (self - other).sign() >= 0

    def __float__(self):
        return float(self.a) + float(self.b) * math.sqrt(float(self.base_c()))

    def to_json(self):
        return {
            "basis": "1,sqrt(57),t,sqrt(57)*t",
            "a": self.a.to_json(),
            "b": self.b.to_json(),
            "t_squared": self.base_c().to_json(),
        }

    def __str__(self):
        if self.b == Quad(0, 0, 57):
            return str(self.a)
        if self.a == Quad(0, 0, 57):
            return f"({self.b})*t"
        sign = "+" if self.b.sign() > 0 else "-"
        bb = self.b if self.b.sign() > 0 else -self.b
        return f"({self.a}){sign}({bb})*t"

def frac_str(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def q(d: int, a=0, b=0) -> Quad:
    return Quad(a, b, d)


Point = tuple[Quad, Quad]
PolygonQ = list[Point]


def pt(d: int, x=0, y=0) -> Point:
    return (q(d, x), q(d, y))


def addp(p: Point, r: Point) -> Point:
    return (p[0] + r[0], p[1] + r[1])


def subp(p: Point, r: Point) -> Point:
    return (p[0] - r[0], p[1] - r[1])


def scalep(a: Quad, p: Point) -> Point:
    return (a * p[0], a * p[1])


def dot(u: Point, v: Point) -> Quad:
    return u[0] * v[0] + u[1] * v[1]


def cross(u: Point, v: Point) -> Quad:
    return u[0] * v[1] - u[1] * v[0]


def dist2(p: Point, r: Point) -> Quad:
    v = subp(p, r)
    return dot(v, v)


def area2(poly: Sequence[Point]):
    s = poly[0][0] * 0
    for p, r in zip(poly, poly[1:] + poly[:1]):
        s += cross(p, r)
    return s


def absq(x: Quad) -> Quad:
    return -x if x.sign() < 0 else x


def polygon_convex(poly: Sequence[Point]) -> bool:
    signs = []
    n = len(poly)
    for i in range(n):
        a, b, c = poly[i - 1], poly[i], poly[(i + 1) % n]
        s = cross(subp(b, a), subp(c, b)).sign()
        if s:
            signs.append(s)
    return bool(signs) and all(s == signs[0] for s in signs)


def distance_matrix(poly: Sequence[Point]) -> tuple[tuple[Quad, ...], ...]:
    return tuple(tuple(dist2(poly[i], poly[j]) for j in range(len(poly)))
                 for i in range(len(poly)))


def congruent_cyclic(p: Sequence[Point], r: Sequence[Point]) -> bool:
    if len(p) != len(r):
        return False
    n = len(p)
    Dp = distance_matrix(p)
    Dr = distance_matrix(r)
    for rev in (False, True):
        for k in range(n):
            def idx(i):
                return (k - i) % n if rev else (k + i) % n
            if all(Dp[i][j] == Dr[idx(i)][idx(j)] for i in range(n) for j in range(n)):
                return True
    return False


def project(poly: Sequence[Point], axis: Point) -> tuple[Quad, Quad]:
    vals = [dot(p, axis) for p in poly]
    lo = hi = vals[0]
    for x in vals[1:]:
        if x < lo:
            lo = x
        if x > hi:
            hi = x
    return lo, hi


def separating_axis_witness(p: Sequence[Point], r: Sequence[Point]) -> dict | None:
    """Return a finite exact separating-axis witness, or ``None``."""
    for source, poly in enumerate((p, r)):
        for edge, (a, b) in enumerate(zip(poly, poly[1:] + poly[:1])):
            e = subp(b, a)
            axis = (-e[1], e[0])
            p0, p1 = project(p, axis)
            r0, r1 = project(r, axis)
            if p1 <= r0:
                return {"source_polygon": source, "source_edge": edge,
                        "projection_order": "first_before_second",
                        "axis": serialize_quad_point(axis)}
            if r1 <= p0:
                return {"source_polygon": source, "source_edge": edge,
                        "projection_order": "second_before_first",
                        "axis": serialize_quad_point(axis)}
    return None


def separated_convex(p: Sequence[Point], r: Sequence[Point]) -> bool:
    """Closed interiors are disjoint if an edge normal separates intervals."""
    return separating_axis_witness(p, r) is not None


def translate(poly: Sequence[Point], v: Point) -> PolygonQ:
    return [addp(p, v) for p in poly]


def lincomb(m: int, L1: Point, n: int, L2: Point) -> Point:
    d = L1[0].d
    return addp(scalep(q(d, m), L1), scalep(q(d, n), L2))


def lattice_coords(v: Point, L1: Point, L2: Point) -> tuple[Quad, Quad]:
    det = cross(L1, L2)
    return cross(v, L2) / det, cross(L1, v) / det


def on_segment(v: Point, p: Point, r: Point) -> tuple[bool, Quad | None]:
    e = subp(r, p)
    w = subp(v, p)
    if cross(e, w) != q(e[0].d, 0):
        return False, None
    if e[0] != q(e[0].d, 0):
        t = w[0] / e[0]
    elif e[1] != q(e[0].d, 0):
        t = w[1] / e[1]
    else:
        return False, None
    return (q(e[0].d, 0) <= t <= q(e[0].d, 1)), t


def cmp_quad(a: Quad, b: Quad) -> int:
    return (a > b) - (a < b)


@dataclass
class PeriodicCertificate:
    name: str
    d: int
    polygons: list[PolygonQ]
    L1: Point
    L2: Point
    convex: bool = True
    metadata: dict | None = None

    def to_json(self):
        return {
            "name": self.name,
            "field": f"Q(sqrt({self.d}))",
            "lattice": [[x.to_json() for x in self.L1], [x.to_json() for x in self.L2]],
            "polygons": [[[x.to_json() for x in p] for p in poly] for poly in self.polygons],
            "convex": self.convex,
            "metadata": self.metadata or {},
        }


def split_directed_edges(cert: PeriodicCertificate, shift_radius: int = 2):
    verts = [v for poly in cert.polygons for v in poly]
    shifted = []
    for v in verts:
        for m in range(-shift_radius, shift_radius + 1):
            for n in range(-shift_radius, shift_radius + 1):
                shifted.append(addp(v, lincomb(m, cert.L1, n, cert.L2)))
    segments = []
    for pi, poly in enumerate(cert.polygons):
        for ei, (p, r) in enumerate(zip(poly, poly[1:] + poly[:1])):
            ts = {q(cert.d, 0), q(cert.d, 1)}
            for v in shifted:
                ok, t = on_segment(v, p, r)
                if ok and t is not None:
                    ts.add(t)
            ordered = sorted(ts, key=cmp_to_key(cmp_quad))
            e = subp(r, p)
            for t0, t1 in zip(ordered, ordered[1:]):
                if t0 == t1:
                    continue
                s0 = addp(p, scalep(t0, e))
                s1 = addp(p, scalep(t1, e))
                segments.append({"p": s0, "q": s1, "poly": pi, "edge": ei})
    return segments


def pair_segments_mod_lattice(segments, L1: Point, L2: Point):
    used = [False] * len(segments)
    pairs = []
    for i, s in enumerate(segments):
        if used[i]:
            continue
        found = None
        for j in range(i + 1, len(segments)):
            if used[j]:
                continue
            t = segments[j]
            v1 = subp(s["p"], t["q"])
            v2 = subp(s["q"], t["p"])
            if v1 != v2:
                continue
            m, n = lattice_coords(v1, L1, L2)
            if m.is_integer() and n.is_integer():
                found = (j, m.as_int(), n.as_int())
                break
        if found is None:
            raise AssertionError(f"unpaired subsegment {i}: {s}")
        j, m, n = found
        used[i] = used[j] = True
        pairs.append((i, j, m, n))
    return pairs


def ceil_quad_nonneg(x: Quad) -> int:
    """Least natural n with x <= n; finite-search form mirrors bounded iPRA."""
    assert x.sign() >= 0
    n = 0
    while x > n:
        n += 1
    return n


def lattice_coordinate_widths(cert: PeriodicCertificate) -> tuple[Quad, Quad, int]:
    """A proof-producing finite bound on all lattice translates that can overlap.

    If a tile and a translate by (m,n) overlap, their intervals under each
    dual lattice coordinate overlap.  Thus |m| and |n| are no larger than
    the global coordinate widths of the finite cell.
    """
    coords = [lattice_coords(v, cert.L1, cert.L2)
              for poly in cert.polygons for v in poly]
    xs = [c[0] for c in coords]
    ys = [c[1] for c in coords]
    wx = max(xs) - min(xs)
    wy = max(ys) - min(ys)
    radius = max(ceil_quad_nonneg(wx), ceil_quad_nonneg(wy))
    return wx, wy, radius


def segment_json(s):
    return {
        "polygon": s["poly"], "edge": s["edge"],
        "start": serialize_quad_point(s["p"]),
        "end": serialize_quad_point(s["q"]),
    }


def verify_periodic(cert: PeriodicCertificate, overlap_radius: int | None = None,
                    details: dict | None = None) -> dict:
    assert len(cert.polygons) > 0
    assert all(len(p) == 5 for p in cert.polygons)
    assert all(congruent_cyclic(cert.polygons[0], p) for p in cert.polygons)
    if cert.convex:
        assert all(polygon_convex(p) for p in cert.polygons)

    det = absq(cross(cert.L1, cert.L2))
    area = sum((absq(area2(p)) for p in cert.polygons), q(cert.d, 0)) / 2
    assert area == det, (area, det)

    wx, wy, derived_radius = lattice_coordinate_widths(cert)
    if overlap_radius is None:
        overlap_radius = derived_radius
    assert overlap_radius >= derived_radius

    sat_count = 0
    separators = []
    if cert.convex:
        for i, p in enumerate(cert.polygons):
            for j, r in enumerate(cert.polygons):
                for m in range(-overlap_radius, overlap_radius + 1):
                    for n in range(-overlap_radius, overlap_radius + 1):
                        if i == j and m == 0 and n == 0:
                            continue
                        # Avoid duplicate ordered checks.
                        key1 = (i, 0, 0)
                        key2 = (j, m, n)
                        if key2 < key1:
                            continue
                        shifted = translate(r, lincomb(m, cert.L1, n, cert.L2))
                        witness = separating_axis_witness(p, shifted)
                        assert witness is not None, (cert.name, i, j, m, n)
                        separators.append({"first_polygon": i, "second_polygon": j,
                                           "lattice_m": m, "lattice_n": n,
                                           "witness": witness})
                        sat_count += 1

    segs = split_directed_edges(cert, shift_radius=max(2, derived_radius))
    pairs = pair_segments_mod_lattice(segs, cert.L1, cert.L2)
    if details is not None:
        details.update({
            "name": cert.name,
            "lattice_coordinate_widths": [str(wx), str(wy)],
            "derived_overlap_radius": derived_radius,
            "segments": [segment_json(s) for s in segs],
            "edge_pairings": [
                {"first": i, "second": j, "lattice_m": m, "lattice_n": n}
                for i, j, m, n in pairs
            ],
            "separator_instances": separators,
        })
    return {
        "name": cert.name,
        "field": f"Q(sqrt({cert.d}))",
        "tile_count": len(cert.polygons),
        "convex": cert.convex,
        "cell_area": str(det),
        "tile_area_sum": str(area),
        "lattice_coordinate_widths": [str(wx), str(wy)],
        "derived_overlap_radius": derived_radius,
        "directed_subsegments": len(segs),
        "subsegment_pairs": len(pairs),
        "separating_axis_checks": sat_count,
        "boundary_pairing_complete": True,
        "congruence_complete": True,
    }


def type1_rational_certificate() -> PeriodicCertificate:
    d = 3
    p = pt(d, 1, 0)
    qv = pt(d, 1, 2)
    A, B, C, D, E, G = [pt(d, *xy) for xy in
                         [(0, 0), (2, 0), (3, 1), (2, 2), (0, 2), (-1, 1)]]
    P = [p, B, C, D, qv]
    Q = [p, qv, E, G, A]
    return PeriodicCertificate(
        "Type 1 rational two-pentagon cell", d, [P, Q],
        pt(d, 3, 1), pt(d, 0, 2), True,
        {"angle_degrees": [90, 135, 90, 135, 90],
         "hexagon_vertices": [[0,0],[2,0],[3,1],[2,2],[0,2],[-1,1]]})


def regular_hex_vertices() -> list[Point]:
    d = 3
    s = q(d, 0, 1)
    return [
        (q(d,1),q(d,0)), (q(d,F(1,2)),s/2),
        (q(d,F(-1,2)),s/2), (q(d,-1),q(d,0)),
        (q(d,F(-1,2)),-s/2), (q(d,F(1,2)),-s/2),
    ]


def regular_hex_lattice() -> tuple[Point, Point]:
    d = 3
    s = q(d, 0, 1)
    return (q(d,F(3,2)),s/2), (q(d,0),s)


def type1_regular_hex_bisection() -> PeriodicCertificate:
    d = 3
    V = regular_hex_vertices()
    p = scalep(q(d,F(1,2)), addp(V[5], V[0]))
    r = scalep(q(d,F(1,2)), addp(V[2], V[3]))
    P = [p, V[0], V[1], V[2], r]
    Q = [p, r, V[3], V[4], V[5]]
    L1, L2 = regular_hex_lattice()
    return PeriodicCertificate(
        "Regular hexagon bisected into two Type 1 pentagons", d, [P,Q], L1,L2,True,
        {"overlay":"regular hexagon", "tile_count_per_hexagon":2})


def type3_regular_hex_trisection() -> PeriodicCertificate:
    d = 3
    V = regular_hex_vertices()
    O = pt(d,0,0)
    M = [scalep(q(d,F(1,2)), addp(V[i], V[(i+1)%6])) for i in (0,2,4)]
    polys=[]
    for k in range(3):
        i=2*k
        polys.append([O,M[k],V[(i+1)%6],V[(i+2)%6],M[(k+1)%3]])
    L1,L2=regular_hex_lattice()
    return PeriodicCertificate(
        "Regular hexagon trisected into three Type 3 pentagons", d, polys,L1,L2,True,
        {"angle_degrees":[120,90,120,120,90],
         "side_lengths":["sqrt(3)/2","1/2","1","1/2","sqrt(3)/2"]})


def type15_certificate() -> PeriodicCertificate:
    d0=3
    H=q(d0,0,1)
    a=[
        (q(d0,0),q(d0,0)),
        (H,q(d0,1)),
        (2*H,q(d0,0)),
        (2*H+1,H),
        (2*H+2,q(d0,0)),
        (3*H+2,q(d0,1)),
        (3*H+4,q(d0,1)),
        (3*H+6,q(d0,1)),
        (5*H+6,q(d0,3)),
        (5*H+6,q(d0,1)),
        (2*H+3,-H),
        (3*H+5,-H+1),
    ]
    b=[]; c=[]; dd=[]
    for ax,ay in a:
        dx=10*H+12-ax
        dy=4-ay
        b.append((dx-H-1,dy-H-3))
        c.append((ax-H-1,ay-H-3))
        dd.append((dx,dy))
    def six(x,y):
        return [
            [x[0],x[1],y[3],y[2],y[1]],
            [x[1],x[2],y[5],y[4],y[3]],
            [x[2],x[3],x[10],y[6],y[5]],
            [x[4],x[5],x[7],x[11],x[10]],
            [x[10],x[11],y[8],y[7],y[6]],
            [x[7],x[8],x[9],y[8],x[11]],
        ]
    polys=six(a,c)+six(b,dd)
    L1=(9*H+12,q(d0,3))
    L2=(H+1,H+3)
    return PeriodicCertificate(
        "Type 15 exact twelve-pentagon cell",d0,polys,L1,L2,True,
        {"angles_degrees":[150,60,135,105,90],
         "side_lengths":[2,4,2,2,"sqrt(6)+sqrt(2)"],
         "source_coordinate_scheme":"Jolu Mij JSFiddle, rewritten exactly"})


def rotation60(p: Point, k: int) -> Point:
    d=3; H=q(d,0,1)
    # Repeated exact multiplication by exp(i*pi/3) = 1/2 + i*sqrt(3)/2.
    x,y=p
    for _ in range(k%6):
        x,y=x/2-H*y/2,H*x/2+y/2
    return x,y


def rotation90_rat(p: Point,k:int) -> Point:
    x,y=p
    for _ in range(k%4):
        x,y=-y,x
    return x,y


def nonconvex_subdivision(n: int) -> tuple[list[PolygonQ], PolygonQ]:
    if n==3:
        d=3; H=q(d,0,1)
        V=[rotation60((q(d,1),q(d,0)),2*k) for k in range(3)]
        W0=(H/4,q(d,F(-1,4)))  # radius 1/2, angle -30 degrees
        W=[rotation60(W0,2*k) for k in range(3)]
    elif n==4:
        d=3
        V=[rotation90_rat(pt(d,1,0),k) for k in range(4)]
        W0=pt(d,F(1,3),F(-1,3))
        W=[rotation90_rat(W0,k) for k in range(4)]
    elif n==6:
        d=3; H=q(d,0,1)
        V=regular_hex_vertices()
        W0=(H/4,q(d,F(-1,4)))
        W=[rotation60(W0,k) for k in range(6)]
    else:
        raise ValueError(n)
    O=pt(d,0,0)
    tiles=[]
    for i in range(n):
        tiles.append([V[i],V[(i+1)%n],W[(i+1)%n],O,W[i]])
    return tiles,V


def point_less(p: Point, r: Point) -> bool:
    """Exact lexicographic order, used only to canonicalize finite edges."""
    return p[0] < r[0] or (p[0] == r[0] and p[1] < r[1])


def canonical_segment(p: Point, r: Point) -> tuple[tuple[Point, Point], int]:
    """Return an unoriented segment key and the original orientation (+/-1)."""
    assert p != r
    if point_less(p, r):
        return (p, r), 1
    return (r, p), -1


def orient(a: Point, b: Point, c: Point) -> int:
    return cross(subp(b, a), subp(c, a)).sign()


def strict_on_segment(v: Point, p: Point, r: Point) -> bool:
    ok, t = on_segment(v, p, r)
    if not ok or t is None:
        return False
    zero, one = q(p[0].d, 0), q(p[0].d, 1)
    return zero < t < one


def forbidden_segment_intersection(a: Point, b: Point, c: Point, d: Point) -> bool:
    """Exact test for an intersection beyond a common endpoint.

    It catches proper crossings, T-junctions, and positive-length collinear
    overlap.  Touching at a shared endpoint is allowed.
    """
    o1, o2 = orient(a, b, c), orient(a, b, d)
    o3, o4 = orient(c, d, a), orient(c, d, b)
    if o1 * o2 < 0 and o3 * o4 < 0:
        return True
    return (strict_on_segment(a, c, d) or strict_on_segment(b, c, d) or
            strict_on_segment(c, a, b) or strict_on_segment(d, a, b))


def point_in_convex_closed(v: Point, poly: Sequence[Point]) -> bool:
    signs = []
    for a, b in zip(poly, poly[1:] + poly[:1]):
        s = orient(a, b, v)
        if s:
            signs.append(s)
    return not signs or all(s == signs[0] for s in signs)


def verify_subdivision(n:int) -> dict:
    tiles,container=nonconvex_subdivision(n)
    assert polygon_convex(container)
    assert all(len(set(p)) == 5 for p in tiles)
    assert all(congruent_cyclic(tiles[0],p) for p in tiles)
    assert all(not polygon_convex(p) for p in tiles)
    expected_concave = {3: q(3, F(-1, 4)), 4: q(3, F(-1, 3)),
                        6: q(3, F(-1, 4))}[n]
    concave_turns = []
    for poly in tiles:
        turns = [cross(subp(poly[(i+1) % 5], poly[i]),
                       subp(poly[(i+2) % 5], poly[(i+1) % 5]))
                 for i in range(5)]
        assert turns[1] == expected_concave
        assert turns[1].sign() < 0 and all(turns[i].sign() > 0 for i in (0,2,3,4))
        concave_turns.append(str(turns[1]))
    assert all(point_in_convex_closed(v, container) for p in tiles for v in p)

    # Exact planar-complex certificate.  Boundary edges occur once; every
    # internal edge occurs twice with opposite directions.  Distinct edges
    # have no proper crossing, T-junction, or positive-length overlap.
    multiplicity: dict[tuple[Point, Point], list[int]] = {}
    for poly in tiles:
        for a, b in zip(poly, poly[1:] + poly[:1]):
            key, direction = canonical_segment(a, b)
            multiplicity.setdefault(key, []).append(direction)
    boundary = {canonical_segment(a, b)[0]
                for a, b in zip(container, container[1:] + container[:1])}
    assert len(boundary) == n
    for key, directions in multiplicity.items():
        if key in boundary:
            assert len(directions) == 1
        else:
            assert len(directions) == 2 and sum(directions) == 0
    assert all(key in multiplicity for key in boundary)
    unique_edges = list(multiplicity)
    for (a, b), (c, d) in combinations(unique_edges, 2):
        assert not forbidden_segment_intersection(a, b, c, d), ((a, b), (c, d))

    total=sum((absq(area2(p)) for p in tiles),q(3,0))/2
    outer=absq(area2(container))/2
    assert total==outer

    # Shapely is only an independent numerical sanity check; no theorem
    # depends on its availability.
    try:
        from shapely.geometry import Polygon
        spols=[Polygon([(float(x),float(y)) for x,y in p]) for p in tiles]
        union=spols[0]
        overlap=0.0
        for p in spols[1:]:
            overlap += union.intersection(p).area
            union=union.union(p)
        cont=Polygon([(float(x),float(y)) for x,y in container])
        assert overlap < 1e-10 and union.symmetric_difference(cont).area < 1e-10
        numeric=True
    except Exception:
        numeric=False
    return {"name":f"regular {n}-gon into {n} congruent nonconvex pentagons",
            "tile_count":n,"exact_area_match":True,"all_congruent":True,
            "all_nonconvex":True,"concave_vertex":"W_(i+1)",
            "concave_turn":str(expected_concave),
            "all_vertices_in_container":True,"exact_planar_complex_check":True,
            "boundary_edges":len(boundary),
            "internal_edge_pairs":len(unique_edges)-len(boundary),
            "unique_edges":len(unique_edges),
            "numeric_union_check":numeric,"area":str(outer)}


def type15_invariants(cert: PeriodicCertificate) -> dict:
    p=cert.polygons[0]
    sides=[dist2(p[i],p[(i+1)%5]) for i in range(5)]
    # This coordinate order is 135,60,150,90,105 degrees.  Rotate/reverse to
    # the article's A,B,C,D,E order.
    vertex=[]
    for i in range(5):
        u=subp(p[i-1],p[i]); v=subp(p[(i+1)%5],p[i])
        vertex.append({"dot":str(dot(u,v)),"cross":str(cross(u,v)),
                       "cos2":str((dot(u,v)**2)/(dot(u,u)*dot(v,v)))})
    expected=[q(3,4),q(3,16),q(3,4),q(3,4),q(3,8,4)]
    assert sides==expected
    return {"side_squares":[str(x) for x in sides],
            "side_lengths":[2,4,2,2,"sqrt(6)+sqrt(2)"],
            "coordinate_order_angles_degrees":[135,60,150,90,105],
            "vertex_invariants":vertex}


def _lin_eq(coeffs: Sequence[int | Fraction], rhs: int | Fraction) -> tuple[Fraction, ...]:
    """Encode sum coeffs[i]*x_i = rhs as a homogeneous 6-vector."""
    assert len(coeffs) == 5
    return tuple(F(c) for c in coeffs) + (-F(rhs),)


def _solve_span(rows: Sequence[Sequence[Fraction]], target: Sequence[Fraction]) -> list[Fraction]:
    """Find exact rational multipliers with sum lambda_i rows_i = target."""
    # Solve the transposed system (six equations, len(rows) unknowns).
    m, n = 6, len(rows)
    aug = [[F(rows[j][i]) for j in range(n)] + [F(target[i])] for i in range(m)]
    pivot_cols = []
    r = 0
    for c in range(n):
        pivot = next((i for i in range(r, m) if aug[i][c] != 0), None)
        if pivot is None:
            continue
        aug[r], aug[pivot] = aug[pivot], aug[r]
        z = aug[r][c]
        aug[r] = [x / z for x in aug[r]]
        for i in range(m):
            if i != r and aug[i][c] != 0:
                z = aug[i][c]
                aug[i] = [aug[i][j] - z * aug[r][j] for j in range(n + 1)]
        pivot_cols.append(c)
        r += 1
        if r == m:
            break
    for i in range(r, m):
        assert any(aug[i][j] != 0 for j in range(n)) or aug[i][n] == 0
    sol = [F(0) for _ in range(n)]
    for i, c in enumerate(pivot_cols):
        sol[c] = aug[i][n]
    assert all(sum((sol[j] * rows[j][i] for j in range(n)), F(0)) == target[i]
               for i in range(6))
    return sol


def angle_table_identities() -> dict:
    """Exact rational linear certificates for all fifteen angle rows."""
    A=(1,0,0,0,0); B=(0,1,0,0,0); C=(0,0,1,0,0); D=(0,0,0,1,0); E=(0,0,0,0,1)
    S=_lin_eq((1,1,1,1,1),540)
    rows={
      1: ([ _lin_eq((0,1,1,0,0),180) ],
          [("A+D+E=360",_lin_eq((1,0,0,1,1),360))]),
      2: ([ _lin_eq((0,1,0,1,0),180) ],
          [("A+C+E=360",_lin_eq((1,0,1,0,1),360))]),
      3: ([ _lin_eq(A,120),_lin_eq(C,120),_lin_eq(D,120) ],
          [("B+E=180",_lin_eq((0,1,0,0,1),180))]),
      4: ([ _lin_eq(B,90),_lin_eq(D,90) ],
          [("A+C+E=360",_lin_eq((1,0,1,0,1),360))]),
      5: ([ _lin_eq(A,60),_lin_eq(D,120) ],
          [("B+C+E=360",_lin_eq((0,1,1,0,1),360))]),
      6: ([ _lin_eq((0,1,0,1,0),180),_lin_eq((0,-2,0,0,1),0) ],
          [("A+C+E=360",_lin_eq((1,0,1,0,1),360)),
           ("A+C+2B=360",_lin_eq((1,2,1,0,0),360))]),
      7: ([ _lin_eq((0,1,0,0,2),360),_lin_eq((0,0,2,1,0),360) ],
          [("A+180=C+E",_lin_eq((1,0,-1,0,-1),-180))]),
      8: ([ _lin_eq((0,2,1,0,0),360),_lin_eq((0,0,0,1,2),360) ],
          [("A+180=B+E",_lin_eq((1,-1,0,0,-1),-180))]),
      9: ([ _lin_eq((2,0,1,0,0),360),_lin_eq((0,0,0,1,2),360) ],
          [("A+E=B+180",_lin_eq((1,-1,0,0,1),180))]),
      10: ([ _lin_eq(A,90),_lin_eq((0,1,0,0,1),180),_lin_eq((0,1,2,0,0),360) ],
           [("C+D=270",_lin_eq((0,0,1,1,0),270))]),
      11: ([ _lin_eq(A,90),_lin_eq((0,0,1,0,1),180),_lin_eq((0,2,1,0,0),360) ],
           [("B+D=270",_lin_eq((0,1,0,1,0),270))]),
      12: ([ _lin_eq(A,90),_lin_eq((0,0,1,0,1),180),_lin_eq((0,2,1,0,0),360) ],
           [("B+D=270",_lin_eq((0,1,0,1,0),270))]),
      13: ([ _lin_eq(B,90),_lin_eq(E,90),_lin_eq((2,0,0,1,0),360) ],
           [("A=C",_lin_eq((1,0,-1,0,0),0))]),
      14: ([ _lin_eq(A,90),_lin_eq((0,2,1,0,0),360),_lin_eq((0,0,1,0,1),180) ],
           [("B+D=270",_lin_eq((0,1,0,1,0),270))]),
      15: ([ _lin_eq(A,150),_lin_eq(B,60),_lin_eq(C,135),
              _lin_eq(D,105),_lin_eq(E,90) ],
           [("A+B+C+D+E=540",S)]),
    }
    out={}
    for k,(hyps,targets) in rows.items():
        # Types 1-14 use the universal pentagon angle sum.  Type 15 is
        # deliberately checked by direct addition of its five fixed angles.
        basis=hyps if k == 15 else [S]+hyps
        basis_label="hypotheses_only" if k == 15 else "angle_sum_and_hypotheses"
        certs=[]
        for text,target in targets:
            multipliers=_solve_span(basis,target)
            certs.append({"target":text, "basis":basis_label,
                          "multipliers":[frac_str(z) for z in multipliers],
                          "verified":True})
        out[str(k)]={"hypothesis_count":len(hyps),"certificates":certs}
    assert len(out)==15 and all(all(c["verified"] for c in v["certificates"]) for v in out.values())
    return out


def type14_local_patch() -> dict:
    """Exact Type 14 algebra and six-copy local configuration.

    All decisive geometry is checked in the explicit ordered quartic field
    Q(sqrt(57), t), t^2=(6*sqrt(57)-2)/64, t>0.  No floating-point or
    computer-algebra sign oracle is used here.
    """
    r = Quad(0, 1, 57)
    base = lambda z: Quartic57(z, 0)
    t = Quartic57(0, 1)                         # cos(C/2)
    y1b = (r - 3) / 8                           # sin(C/2)=sin(B)
    y2b = (3 * r - 17) / 16                     # cos(C)
    y1, y2 = base(y1b), base(y2b)
    x1 = t
    x2 = Quartic57(0, (r - 3) / 4)              # sin(C)=2 sin(C/2)t

    zero = Quartic57(0)
    P = lambda x, y: (x if isinstance(x, Quartic57) else base(x),
                      y if isinstance(y, Quartic57) else base(y))
    A1 = P(0, 0)
    B1 = P(2*x2+x1, 0)
    C1 = P(2*x2+2*x1, -y1)
    D1 = P(2*x2, -3*y1)
    E1 = P(0, -1)
    p1 = [A1, B1, C1, D1, E1]
    p2 = [P(z[0], -z[1]) for z in p1]
    X1 = 4*x2 + 3*x1
    p3 = [P(X1-z[0], -y1+z[1]) for z in p1]
    p4 = [P(p3[i][0], -y1+p2[i][1]) for i in range(5)]
    A5, B5, C5 = p4[3], p2[2], p2[3]
    D5 = P(C5[0], C5[1]+2)
    E5 = P(D5[0]+x2, D5[1]-y2)
    p5 = [A5, B5, C5, D5, E5]
    A6, B6 = E5, A5
    C6 = P(B6[0]+x2, B6[1]-y2)
    D6 = P(C6[0], C6[1]+2)
    E6 = P(D6[0]-2*x1, D6[1]+2*y1)
    p6 = [A6, B6, C6, D6, E6]
    polys = [p1, p2, p3, p4, p5, p6]

    # Defining algebra and positivity.
    assert Quartic57.base_c().sign() > 0
    assert x1.sign() > 0 and x2.sign() > 0 and y1.sign() > 0 and y2.sign() > 0
    assert 4*y1*y1 + 3*y1 - 3 == zero
    assert 2*y2 + 1 - 3*y1 == zero
    assert x1*x1 + y1*y1 == Quartic57(1)
    assert x2*x2 + y2*y2 == Quartic57(1)
    assert x2 == 2*y1*x1

    # Full Euclidean congruence (all 25 squared distances), convexity, and
    # exact pairwise interior separation of the six placed copies.
    assert all(congruent_cyclic(p1, p) for p in polys)
    assert all(polygon_convex(p) for p in polys)
    separation_pairs = []
    for i, j in combinations(range(6), 2):
        assert separated_convex(polys[i], polys[j]), (i, j)
        separation_pairs.append([i, j])

    # The shared-vertex graph is connected, so these are one local patch
    # rather than six unrelated placements.
    shared = []
    graph = {i: set() for i in range(6)}
    for i, j in combinations(range(6), 2):
        pairs = [[a, b] for a in range(5) for b in range(5)
                 if polys[i][a] == polys[j][b]]
        if pairs:
            shared.append({"tiles": [i, j], "vertex_pairs": pairs})
            graph[i].add(j); graph[j].add(i)
    seen, stack = {0}, [0]
    while stack:
        i = stack.pop()
        for j in graph[i] - seen:
            seen.add(j); stack.append(j)
    assert len(seen) == 6

    sides = [dist2(p1[i], p1[(i+1) % 5]) for i in range(5)]
    target = [base((11*r-25)/8), Quartic57(1), Quartic57(4),
              Quartic57(4), Quartic57(1)]
    assert sides == target

    # Angle invariants in article order A,B,C,D,E.  A is right; C and E
    # have equal sine and opposite cosine; B has sine y1 and negative cosine
    # -x1.  These algebraic ray invariants prove A=90, C+E=180, and
    # 2B+C=360 for convex angles.
    def angle_data(poly, i):
        u = subp(poly[i-1], poly[i])
        v = subp(poly[(i+1) % 5], poly[i])
        return dot(u, v), absq(cross(u, v)), dist2(poly[i-1], poly[i]), dist2(poly[(i+1)%5], poly[i])
    ad = [angle_data(p1, i) for i in range(5)]
    assert ad[0][0] == zero
    # B: dot<0 and normalized sine/cosine squares match y1 and x1.
    assert ad[1][0].sign() < 0
    assert ad[1][1]**2 == ad[1][2]*ad[1][3]*(y1**2)
    assert ad[1][0]**2 == ad[1][2]*ad[1][3]*(x1**2)
    # C and E: same positive sine, opposite cosine.
    assert ad[2][0].sign() > 0 and ad[4][0].sign() < 0
    assert ad[2][1]**2 == ad[2][2]*ad[2][3]*(x2**2)
    assert ad[4][1]**2 == ad[4][2]*ad[4][3]*(x2**2)
    assert ad[2][0]**2 == ad[2][2]*ad[2][3]*(y2**2)
    assert ad[4][0]**2 == ad[4][2]*ad[4][3]*(y2**2)

    return {
        "name": "Type 14 exact six-tile local patch",
        "field": "Q(sqrt(57),t), t>0, t^2=(6*sqrt(57)-2)/64",
        "basis_encoding": "a0+a1*sqrt(57)+(b0+b1*sqrt(57))*t",
        "parameters": {
            "sin_C_over_2": str(y1), "cos_C": str(y2),
            "cos_C_over_2": str(x1), "sin_C": str(x2),
        },
        "polynomial_certificates": [
            "4*sin(C/2)^2+3*sin(C/2)-3=0",
            "2*cos(C)+1=3*sin(C/2)",
            "cos(C/2)^2+sin(C/2)^2=1",
            "sin(C)^2+cos(C)^2=1",
            "sin(C)=2*sin(C/2)*cos(C/2)",
        ],
        "side_squares": [str(x) for x in sides],
        "type_relations": ["2a=2c=d=e", "A=90 degrees",
                           "2B+C=360 degrees", "C+E=180 degrees"],
        "all_six_full_distance_congruent": True,
        "all_six_convex": True,
        "all_fifteen_pairs_exactly_separated": True,
        "separation_pairs": separation_pairs,
        "shared_vertex_graph_connected": True,
        "shared_vertices": shared,
        "polygons": [[[z.to_json() for z in point] for point in poly]
                     for poly in polys],
        "status": "exact local patch and tile algebra; no torus boundary certificate claimed",
    }


# --- Dodecahedron over Q(sqrt(5)) -----------------------------------------
Point3=tuple[Quad,Quad,Quad]

def d3(p:Point3,r:Point3)->Quad:
    return sum(((p[i]-r[i])**2 for i in range(3)),q(5,0))

def cross3(u:Point3,v:Point3)->Point3:
    return (u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0])

def dot3(u:Point3,v:Point3)->Quad:
    return sum((u[i]*v[i] for i in range(3)),q(5,0))

def sub3(p:Point3,r:Point3)->Point3:
    return tuple(p[i]-r[i] for i in range(3))  # type: ignore

def dodecahedron_data() -> dict:
    d=5; S=q(d,0,1); phi=(q(d,1)+S)/2; invphi=phi-1
    vals=[]
    for x,y,z in product((-1,1),repeat=3):
        vals.append((q(d,x),q(d,y),q(d,z)))
    for sy,sz in product((-1,1),repeat=2):
        vals.append((q(d,0),sy*invphi,sz*phi))
    for sx,sy in product((-1,1),repeat=2):
        vals.append((sx*invphi,sy*phi,q(d,0)))
    for sx,sz in product((-1,1),repeat=2):
        vals.append((sx*phi,q(d,0),sz*invphi))
    assert len(vals)==20 and len(set(vals))==20
    radii=[sum((c*c for c in v),q(d,0)) for v in vals]
    assert all(r==q(d,3) for r in radii)
    ds=sorted({d3(vals[i],vals[j]) for i in range(20) for j in range(i+1,20)},key=float)
    edge2=ds[0]
    edges={(i,j) for i in range(20) for j in range(i+1,20) if d3(vals[i],vals[j])==edge2}
    nbr={i:set() for i in range(20)}
    for i,j in edges:
        nbr[i].add(j); nbr[j].add(i)
    assert len(edges)==30 and all(len(nbr[i])==3 for i in range(20))
    seen={0}; stack=[0]
    while stack:
        i=stack.pop()
        for j in nbr[i]-seen:
            seen.add(j); stack.append(j)
    assert len(seen)==20

    cycles=set()
    def canon(c):
        c=list(c); n=len(c)
        reps=[]
        for seq in (c,list(reversed(c))):
            for k in range(n):
                reps.append(tuple(seq[k:]+seq[:k]))
        return min(reps)
    for start in range(20):
        def dfs(path):
            if len(path)==5:
                if start in nbr[path[-1]]:
                    cycles.add(canon(path))
                return
            for v in nbr[path[-1]]:
                if v not in path:
                    dfs(path+[v])
        dfs([start])
    faces=sorted(cycles)
    assert len(faces)==12
    counts={e:0 for e in edges}
    for face in faces:
        for i in range(5):
            e=tuple(sorted((face[i],face[(i+1)%5])))
            counts[e]+=1
        # coplanarity and regular diagonal check
        a,b,c=vals[face[0]],vals[face[1]],vals[face[2]]
        normal=cross3(sub3(b,a),sub3(c,a))
        assert all(dot3(normal,sub3(vals[k],a))==q(d,0) for k in face)
        outside=[dot3(normal,sub3(vals[k],a)).sign() for k in range(20) if k not in face]
        assert all(z != 0 for z in outside) and all(z == outside[0] for z in outside)
        ed=[d3(vals[face[i]],vals[face[(i+1)%5]]) for i in range(5)]
        di=[d3(vals[face[i]],vals[face[(i+2)%5]]) for i in range(5)]
        assert len(set(ed))==1 and len(set(di))==1
    assert all(v==2 for v in counts.values())
    assert set().union(*(set(f) for f in faces)) == set(range(20))
    face_nbr={i:set() for i in range(12)}
    face_edges=[]
    for face in faces:
        face_edges.append({tuple(sorted((face[i],face[(i+1)%5]))) for i in range(5)})
    for i,j in combinations(range(12),2):
        if face_edges[i] & face_edges[j]:
            face_nbr[i].add(j); face_nbr[j].add(i)
    fseen={0}; stack=[0]
    while stack:
        i=stack.pop()
        for j in face_nbr[i]-fseen:
            fseen.add(j); stack.append(j)
    assert len(fseen)==12
    assert 20-30+12==2
    return {"name":"regular dodecahedron exact coordinate certificate",
            "field":"Q(sqrt(5))","vertices":20,"edges":30,"faces":12,
            "degree":3,"edge_squared":str(edge2),"sphere_radius_squared":"3",
            "five_cycles":12,"vertex_edge_graph_connected":True,
            "face_adjacency_graph_connected":True,"all_vertices_used_by_faces":True,
            "each_edge_in_two_faces":True,"euler":2,
            "all_faces_coplanar_regular_pentagons":True,"each_face_supports_convex_hull":True,
            "vertices_data":[[[x.to_json() for x in v] for v in vals][i] for i in range(20)],
            "faces_data":[list(f) for f in faces]}


def hyperbolic_order_check(max_n=30) -> dict:
    valid=[]
    for n in range(2,max_n+1):
        # 1/2+1/5+1/n < 1 iff 10 < 3n.
        if 10 < 3*n:
            valid.append(n)
    assert valid[0]==4 and valid==list(range(4,max_n+1))
    return {"coxeter_triangle":"(pi/2, pi/5, pi/n)",
            "inequality":"1/2+1/5+1/n<1 iff 10<3n",
            "finite_orders_checked":valid,
            "first_valid_order":4,
            "ideal_limit":"n=infinity gives zero vertex angle"}


def serialize_quad_point(p:Point):
    return [p[0].to_json(),p[1].to_json()]


def write_certificates(certs:list[PeriodicCertificate], dodec:dict, subdivisions:dict, type14:dict):
    CERT.mkdir(parents=True,exist_ok=True)
    for c in certs:
        (CERT/(c.name.lower().replace(" ","_").replace("-","_")+".json")).write_text(
            json.dumps(c.to_json(),indent=2)+"\n",encoding="utf-8")
    dcopy=dict(dodec)
    (CERT/"dodecahedron_qsqrt5.json").write_text(json.dumps(dcopy,indent=2)+"\n",encoding="utf-8")
    (CERT/"nonconvex_subdivisions.json").write_text(json.dumps(subdivisions,indent=2)+"\n",encoding="utf-8")
    (CERT/"type_14_exact_local_patch.json").write_text(json.dumps(type14,indent=2)+"\n",encoding="utf-8")


def plot_polygon_collection(polys:Sequence[Sequence[Point]], path:Path, title:str, lattice:tuple[Point,Point]|None=None):
    import matplotlib.pyplot as plt
    fig,ax=plt.subplots(figsize=(7,5))
    for i,p in enumerate(polys):
        xs=[float(x) for x,y in p]+[float(p[0][0])]
        ys=[float(y) for x,y in p]+[float(p[0][1])]
        ax.plot(xs,ys,marker="o",linewidth=1.25,label=str(i+1) if len(polys)<=12 else None)
        cx=sum(xs[:-1])/len(p); cy=sum(ys[:-1])/len(p)
        ax.text(cx,cy,str(i+1),ha="center",va="center",fontsize=8)
    if lattice:
        O=(0.0,0.0); a=(float(lattice[0][0]),float(lattice[0][1])); b=(float(lattice[1][0]),float(lattice[1][1]))
        ax.plot([O[0],a[0],a[0]+b[0],b[0],O[0]],[O[1],a[1],a[1]+b[1],b[1],O[1]],linestyle="--",linewidth=1)
    ax.set_aspect("equal",adjustable="box")
    ax.set_title(title)
    ax.axis("off")
    fig.tight_layout()
    fig.savefig(path,bbox_inches="tight")
    plt.close(fig)


def plot_type15_periodic(cert:PeriodicCertificate,path:Path):
    import matplotlib.pyplot as plt
    fig,ax=plt.subplots(figsize=(9,6))
    for m in range(-1,2):
        for n in range(-1,2):
            t=lincomb(m,cert.L1,n,cert.L2)
            for i,p in enumerate(cert.polygons):
                pp=translate(p,t)
                xs=[float(x) for x,y in pp]+[float(pp[0][0])]
                ys=[float(y) for x,y in pp]+[float(pp[0][1])]
                ax.plot(xs,ys,linewidth=.65)
    ax.set_aspect("equal",adjustable="box")
    ax.set_title("Type 15: exact 12-tile lattice cell and neighboring translates")
    ax.axis("off")
    fig.tight_layout()
    fig.savefig(path,bbox_inches="tight")
    plt.close(fig)


def plot_subdivisions(path:Path):
    import matplotlib.pyplot as plt
    # One figure, arranged horizontally; this is a geometric diagram rather than a data chart.
    fig,axes=plt.subplots(1,3,figsize=(12,4))
    for ax,n in zip(axes,(3,4,6)):
        tiles,_=nonconvex_subdivision(n)
        for i,p in enumerate(tiles):
            xs=[float(x) for x,y in p]+[float(p[0][0])]
            ys=[float(y) for x,y in p]+[float(p[0][1])]
            ax.plot(xs,ys,marker="o",linewidth=1)
        ax.set_aspect("equal",adjustable="box"); ax.axis("off"); ax.set_title(f"{n} congruent nonconvex pentagons")
    fig.tight_layout(); fig.savefig(path,bbox_inches="tight"); plt.close(fig)


def plot_type14(path:Path):
    import sympy as sp
    import matplotlib.pyplot as plt
    s=sp.sqrt(57); y1=(s-3)/8; y2=(3*s-17)/16
    x1=sp.sqrt(6*s-2)/8; x2=sp.sqrt(102*s-546)/16
    P=lambda x,y:(float(sp.N(x)),float(sp.N(y)))
    p1=[P(0,0),P(2*x2+x1,0),P(2*x2+2*x1,-y1),P(2*x2,-3*y1),P(0,-1)]
    p2=[(x,-y) for x,y in p1]
    X1=float(sp.N(4*x2+3*x1)); yy=float(sp.N(y1))
    p3=[(X1-x,-yy+y) for x,y in p1]
    p4=[(p3[i][0],-yy+p2[i][1]) for i in range(5)]
    A5=p4[3]; B5=p2[2]; C5=p2[3]; D5=(C5[0],C5[1]+2); E5=(D5[0]+float(x2),D5[1]-float(y2))
    p5=[A5,B5,C5,D5,E5]
    A6=E5; B6=A5; C6=(B6[0]+float(x2),B6[1]-float(y2)); D6=(C6[0],C6[1]+2); E6=(D6[0]-2*float(x1),D6[1]+2*float(y1))
    polys=[p1,p2,p3,p4,p5,[A6,B6,C6,D6,E6]]
    fig,ax=plt.subplots(figsize=(7,5))
    for i,p in enumerate(polys):
        xs=[x for x,y in p]+[p[0][0]]; ys=[y for x,y in p]+[p[0][1]]
        ax.plot(xs,ys,marker="o",linewidth=1.2)
        ax.text(sum(xs[:-1])/5,sum(ys[:-1])/5,str(i+1),ha="center",va="center",fontsize=8)
    ax.set_aspect("equal",adjustable="box"); ax.axis("off")
    ax.set_title("Type 14 exact nested-radical six-tile local patch")
    fig.tight_layout(); fig.savefig(path,bbox_inches="tight"); plt.close(fig)


def plot_dodecahedron(data:dict,path:Path):
    import matplotlib.pyplot as plt
    # Reconstruct floats from JSON coordinate pairs.
    def val(z):
        a=Fraction(z["a"]); b=Fraction(z["b"]); return float(a)+float(b)*math.sqrt(z["d"])
    V=[tuple(val(c) for c in p) for p in data["vertices_data"]]
    edges=set()
    for f in data["faces_data"]:
        for i in range(5): edges.add(tuple(sorted((f[i],f[(i+1)%5]))))
    # Generic oblique projection.
    def proj(p):
        x,y,z=p; return x+.28*z,y+.18*z
    fig,ax=plt.subplots(figsize=(6,6))
    for i,j in edges:
        a=proj(V[i]); b=proj(V[j]); ax.plot([a[0],b[0]],[a[1],b[1]],linewidth=1)
    xs,ys=zip(*(proj(p) for p in V)); ax.scatter(xs,ys,s=12)
    ax.set_aspect("equal",adjustable="box"); ax.axis("off")
    ax.set_title("Dodecahedral {5,3} incidence certificate")
    fig.tight_layout(); fig.savefig(path,bbox_inches="tight"); plt.close(fig)


def main(argv=None):
    parser=argparse.ArgumentParser()
    parser.add_argument("--no-figures",action="store_true")
    args=parser.parse_args(argv)
    FIG.mkdir(parents=True,exist_ok=True); VERIFY.mkdir(parents=True,exist_ok=True)

    certs=[type1_rational_certificate(),type1_regular_hex_bisection(),
           type3_regular_hex_trisection(),type15_certificate()]
    periodic=[]
    witness_payload=[]
    for c in certs:
        detail={}
        periodic.append(verify_periodic(c, details=detail))
        witness_payload.append(detail)
    periodic[-1]["invariants"]=type15_invariants(certs[-1])
    (VERIFY/"periodic_witnesses.json").write_text(
        json.dumps(witness_payload, indent=2)+"\n", encoding="utf-8")
    subdivisions={str(n):verify_subdivision(n) for n in (3,4,6)}
    t14=type14_local_patch()
    dodec=dodecahedron_data()
    hyp=hyperbolic_order_check()
    angles=angle_table_identities()

    results={"periodic_certificates":periodic,"nonconvex_subdivisions":subdivisions,
             "type14":t14,"dodecahedron":{k:v for k,v in dodec.items() if not k.endswith("_data")},
             "hyperbolic":hyp,"angle_table":angles,
             "checker_status":"all assertions passed"}
    (VERIFY/"results.json").write_text(json.dumps(results,indent=2)+"\n",encoding="utf-8")
    write_certificates(certs,dodec,subdivisions,t14)

    if not args.no_figures:
        plot_polygon_collection(certs[0].polygons,FIG/"type1_rational_cell.pdf",certs[0].name,(certs[0].L1,certs[0].L2))
        plot_polygon_collection(certs[2].polygons,FIG/"type3_hexagon.pdf",certs[2].name,(certs[2].L1,certs[2].L2))
        plot_type15_periodic(certs[3],FIG/"type15_periodic.pdf")
        plot_subdivisions(FIG/"nonconvex_subdivisions.pdf")
        plot_type14(FIG/"type14_patch.pdf")
        plot_dodecahedron(dodec,FIG/"dodecahedron.pdf")

    print(json.dumps(results,indent=2))
    return 0


if __name__=="__main__":
    raise SystemExit(main())
