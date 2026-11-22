"""Sharp distortion of a rational polygonal circle, using only exact arithmetic.

Breakpoints include 0 and 1. Vertices include the repeated endpoint. Output
witnesses are rational parameters (the quotient identifies 0 and 1).
Run this file directly to reproduce the checks in the report.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations


def rat(x):
    if isinstance(x, float):
        raise TypeError('use integer, rational string or Fraction')
    return Q(x)


@dataclass(frozen=True)
class Aff:
    s: Q = Q(0)
    t: Q = Q(0)
    c: Q = Q(0)

    def __call__(self, p):
        return self.s * p[0] + self.t * p[1] + self.c

    def __sub__(self, rhs):
        return Aff(self.s-rhs.s, self.t-rhs.t, self.c-rhs.c)

    def __neg__(self):
        return Aff(-self.s, -self.t, -self.c)


def vertices(rows):
    """Rows denote affine forms >= 0, on a bounded 2D polyhedron."""
    found = set()
    for a, b in combinations(rows, 2):
        det = a.s*b.t - a.t*b.s
        if det:
            p = ((a.t*b.c-a.c*b.t)/det, (a.c*b.s-a.s*b.c)/det)
            if p not in found and all(row(p) >= 0 for row in rows):
                found.add(p)
                yield p


@dataclass(frozen=True)
class Distortion:
    lower: Q
    lower_pair: tuple
    upper: Q
    upper_pair: tuple


def distortion(breaks, points):
    breaks = tuple(map(rat, breaks))
    points = tuple(tuple(map(rat, point)) for point in points)
    if len(breaks) < 2 or len(points) != len(breaks):
        raise ValueError('breakpoint and vertex tables must have the same length >= 2')
    if breaks[0] != 0 or breaks[-1] != 1 or any(a >= b for a,b in zip(breaks, breaks[1:])):
        raise ValueError('breakpoints must increase from 0 to 1')
    if not points[0] or points[-1] != points[0] or any(len(p) != len(points[0]) for p in points):
        raise ValueError('a closed polygon in a positive fixed dimension is required')
    lines = []
    for a, b, p, q in zip(breaks, breaks[1:], points, points[1:]):
        slope = [(y-x)/(b-a) for x,y in zip(p,q)]
        lines.append([(v,x-v*a) for x,v in zip(p,slope)])
    s, t = Aff(s=Q(1)), Aff(t=Q(1))
    diff = t-s
    half = Aff(c=Q(1,2))
    short_arcs = [(half-diff, diff), (diff-half, Aff(c=Q(1))-diff)]
    low = high = None
    for i, left in enumerate(lines):
        for j in range(i, len(lines)):
            right = lines[j]
            box = [s-Aff(c=breaks[i]), Aff(c=breaks[i+1])-s,
                   t-Aff(c=breaks[j]), Aff(c=breaks[j+1])-t, diff]
            signed = []
            for (a,b), (v,w) in zip(left, right):
                delta = Aff(a, -v, b-w)
                signed.extend([delta, -delta])
            for arc_test, arc in short_arcs:
                for target in signed:
                    rows = box + [arc_test] + [target-other for other in signed]
                    for pair in vertices(rows):
                        if arc(pair) == 0:
                            continue
                        ratio = target(pair)/arc(pair)
                        if low is None or ratio < low[0]:
                            low = (ratio, pair)
                        if high is None or ratio > high[0]:
                            high = (ratio, pair)
    assert low is not None and high is not None
    return Distortion(*low, *high)


def check_case(breaks, points, expect_lower=None, expect_upper=None):
    breaks = tuple(map(rat, breaks))
    pts = tuple(tuple(map(rat, p)) for p in points)
    bounds = distortion(breaks, pts)

    def evaluate(t):
        i = next(i for i,b in enumerate(breaks[1:]) if t <= b)
        f = (t-breaks[i])/(breaks[i+1]-breaks[i])
        return tuple((1-f)*x+f*y for x,y in zip(pts[i], pts[i+1]))

    def ratio(s, t):
        dx = abs(t-s)
        return max(abs(x-y) for x,y in zip(evaluate(s), evaluate(t))) / min(dx, 1-dx)

    assert ratio(*bounds.lower_pair) == bounds.lower
    assert ratio(*bounds.upper_pair) == bounds.upper
    if expect_lower is not None:
        assert bounds.lower == expect_lower, bounds
    if expect_upper is not None:
        assert bounds.upper == expect_upper, bounds
    grid = sorted(set(breaks[:-1]) | {Q(j,24) for j in range(24)})
    for s,t in combinations(grid,2):
        assert bounds.lower <= ratio(s,t) <= bounds.upper
    print(f'[{bounds.lower}, {bounds.upper}] witnesses {bounds.lower_pair} and {bounds.upper_pair}')
    return bounds


if __name__ == '__main__':
    uniform = [Q(i,4) for i in range(5)]
    square = [(0,0),(1,0),(1,1),(0,1),(0,0)]
    check_case(uniform, square, 2, 4)
    check_case(uniform, [(x,Q(1,16)*y) for x,y in square], Q(1,8), 4)
    check_case(uniform, [(x*3-4,y*3+7) for x,y in square], 6, 12)
    check_case(uniform, [(x,y,x+y) for x,y in square], 2, 4)
    check_case(uniform, [(0,0),(1,1),(0,1),(1,0),(0,0)], 0, 4)
    check_case([0,Q(1,3),1], [(0,), (1,), (0,)], 0, 3)
    check_case([0,1], [(0,), (0,)], 0, 0)
    w = check_case([0,Q(1,8),Q(1,2),Q(3,4),1], square)
    assert w.lower > 0
    print('8 exact cases passed, each with independent checks on rational samples and both extrema.')
