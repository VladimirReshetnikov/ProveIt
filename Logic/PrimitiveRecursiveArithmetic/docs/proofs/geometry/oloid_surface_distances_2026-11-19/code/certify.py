"""Certified shortest lengths on four symmetry copies of a convex planar chamber.

All comparisons and bounds in the search use integers. The geometry module
supplies rigorously enclosed coordinates in units of 1/SCALE. A printed
crossing parameter describes the exhibited upper-bound path.
"""
from __future__ import annotations

import argparse
import csv
import heapq
import sys
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, count, product
from math import isqrt
from pathlib import Path

from geometry import POINTS, SCALE, gate_box, point_box


def ceildiv(a, b):
    return -((-a) // b)


def upnorm(a, b):
    square = a * a + b * b
    n = isqrt(square)
    return n + (n * n != square)


@dataclass(frozen=True)
class Ball:
    x: int
    y: int
    r: int


def enclose(box):
    (x0, x1), (y0, y1) = box
    assert x0 <= x1 and y0 <= y1
    x, y = (x0 + x1) // 2, (y0 + y1) // 2
    return Ball(x, y, upnorm(x1-x, y1-y))


@lru_cache(maxsize=None)
def gate(g, t):
    return enclose(gate_box(g, t))


@lru_cache(maxsize=None)
def fixed(label):
    return enclose(point_box(label))


def unit_support(a, b):
    """An integer vector of norm at most SCALE along the center displacement."""
    dx, dy = b.x - a.x, b.y - a.y
    d = upnorm(dx, dy)
    if not d:
        return (0, 0)
    # Truncate each component toward zero, preserving the norm bound.
    return ((1 if dx >= 0 else -1) * (abs(dx) * SCALE // d),
            (1 if dy >= 0 else -1) * (abs(dy) * SCALE // d))


def path_upper(stops):
    return sum(upnorm(b.x-a.x, b.y-a.y) + a.r + b.r
               for a, b in zip(stops, stops[1:]))


@dataclass(frozen=True)
class Range:
    lo: Fraction
    hi: Fraction

    @property
    def mid(self):
        return (self.lo + self.hi) / 2

    def split(self):
        return (Range(self.lo, self.mid), Range(self.mid, self.hi))

    def clamp(self, x):
        return min(self.hi, max(self.lo, x))


UNIT = Range(Fraction(0), Fraction(1))


def edge_tube(g, span):
    """Every gate point over span belongs to the chord plus a radius-r disk."""
    a, b = gate(g, span.lo), gate(g, span.hi)
    h = span.hi - span.lo
    # Normalized circular arcs have second derivative norm <= (2*pi/3)^2 < 5.
    # Straight gates have zero second derivative.
    defect = ceildiv(5*SCALE*h.numerator**2, 8*h.denominator**2) if g in 'AB' else 0
    return a, b, max(a.r, b.r) + defect


def routes(a, b):
    ya, za = POINTS[a][-2:]
    yb, zb = POINTS[b][-2:]
    # At a zero coordinate either sign label can be used. geometry.py assigns
    # signs +/-1 to chart representatives. A required crossing can be at the
    # endpoint of the path, which accommodates every such assignment.
    ys = ('B', 'L')
    zs = ('A', 'R')
    if ya != yb and za != zb:
        return list(product(ys, zs)) + list(product(zs, ys))
    if ya != yb:
        return [(g,) for g in ys]
    if za != zb:
        return [(g,) for g in zs]
    return [()]


def lower_from_directions(tubes, dirs):
    """Minimize the affine support lower bound over independent gate chords."""
    total = 0
    extended = [(0, 0), *dirs, (0, 0)]
    for (a, b, r), (px, py), (qx, qy) in zip(tubes, extended, extended[1:]):
        vx, vy = px-qx, py-qy
        lowdot = min(vx*a.x + vy*a.y, vx*b.x + vy*b.y)
        total += lowdot - upnorm(vx, vy)*r
    return max(0, total // SCALE)


class PairSearch:
    def __init__(self, start, finish, allowed=None):
        self.start, self.finish = fixed(start), fixed(finish)
        self.words = routes(start, finish) if allowed is None else allowed
        self.upper = None
        self.winner = None
        self.witness = None
        self.wordbest = {}
        self.heap = []
        self.ids = count()
        self.cells = 0

    def sample(self, word, ts):
        stops = [self.start, *(gate(g,t) for g,t in zip(word,ts)), self.finish]
        value = path_upper(stops)
        if word not in self.wordbest or value < self.wordbest[word][0]:
            self.wordbest[word] = value, ts
        if self.upper is None or value < self.upper:
            self.upper, self.winner, self.witness = value, word, ts
        return tuple(unit_support(a, b) for a,b in zip(stops,stops[1:]))

    def seed(self):
        # This finite grid only proposes feasible upper-bound paths.
        grid = [Fraction(i, 8) for i in range(9)]
        for word in self.words:
            for ts in product(grid, repeat=len(word)):
                self.sample(word, ts)
        # Refine the best few words. Search correctness is independent of
        # these guesses. All proposed paths are checked with the same integer
        # upper bound. Diagonal steps help when the two crossings are coupled.
        promising = sorted(self.words, key=lambda w: self.wordbest[w][0])[:2]
        for word in promising:
            n = len(word)
            if not n:
                continue
            directions = list(product((-1,0,1), repeat=n))
            for k in range(4, 17):
                h = Fraction(1, 2**k)
                for _ in range(3):
                    origin = self.wordbest[word][1]
                    for step in directions:
                        ts = tuple(UNIT.clamp(t+v*h) for t,v in zip(origin, step))
                        self.sample(word, ts)
                    if origin == self.wordbest[word][1]:
                        break

    def bound(self, word, spans):
        self.cells += 1
        tubes = [(self.start, self.start, self.start.r),
                 *(edge_tube(g, span) for g, span in zip(word, spans)),
                 (self.finish, self.finish, self.finish.r)]
        center = tuple(s.mid for s in spans)
        nearbest = tuple(s.clamp(t) for s,t in zip(spans, self.wordbest[word][1]))
        points = [nearbest, center] if nearbest != center else [center]
        low = max(lower_from_directions(tubes, self.sample(word, ts)) for ts in points)
        if low < self.upper:
            heapq.heappush(self.heap, (low, next(self.ids), word, spans))

    def run(self, tolerance):
        self.seed()
        for word in self.words:
            self.bound(word, (UNIT,)*len(word))
        while self.heap and self.upper-self.heap[0][0] > tolerance:
            low, _, word, spans = heapq.heappop(self.heap)
            if not spans:
                raise ValueError('Input-coordinate uncertainty exceeds the requested tolerance.')
            # Splitting the longest parameter interval forces convergence.
            i = max(range(len(spans)), key=lambda j: spans[j].hi-spans[j].lo)
            for part in spans[i].split():
                self.bound(word, spans[:i]+(part,)+spans[i+1:])
        low = min(self.upper, self.heap[0][0]) if self.heap else self.upper
        return low, self.upper, self.winner, self.witness, self.cells


def dec(x):
    digits = len(str(SCALE))-1
    assert 10**digits == SCALE
    return f'{x//SCALE}.{x%SCALE:0{digits}d}'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--tolerance', type=Fraction, default=Fraction(1,10**10),
                    help='maximum width of a certificate in unit-radius coordinates')
    ap.add_argument('--compare-routes', action='store_true',
                    help='certify a lower bound for every other gate word')
    ap.add_argument('--pair', nargs=2, metavar=('P','Q'), help='restrict to one pair')
    ap.add_argument('--output', type=Path, help='CSV path (default: standard output)')
    args = ap.parse_args()
    tol = int(args.tolerance*SCALE)
    if tol <= 0:
        ap.error('tolerance is below one coordinate unit')
    pairs = [args.pair] if args.pair else combinations(POINTS, 2)
    out = args.output.open('w', newline='', encoding='utf-8') if args.output else sys.stdout
    try:
        writer = csv.writer(out, lineterminator='\n')
        columns = ['from','to','lower','upper','upper_route','upper_gate_parameters','cells']
        if args.compare_routes:
            columns += ['other_routes_lower','route_gap_lower','other_cells']
        writer.writerow(columns)
        for a,b in pairs:
            low, upper, word, witness, cells = PairSearch(a,b).run(tol)
            row = [a,b,dec(low),dec(upper),''.join(word) or 'direct',
                   ' '.join(map(str,witness)),cells]
            if args.compare_routes:
                others = [w for w in routes(a,b) if w != word]
                if others:
                    alt_low, _, _, _, alt_cells = PairSearch(a,b,others).run(SCALE//10**5)
                    row += [dec(alt_low), dec(alt_low-upper) if alt_low>upper else '', alt_cells]
                else:
                    row += ['', '', 0]
            writer.writerow(row)
            out.flush()
    finally:
        if args.output:
            out.close()


if __name__ == '__main__':
    main()
