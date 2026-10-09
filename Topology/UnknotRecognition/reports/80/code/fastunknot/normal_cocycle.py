"""Exact rank-one integral cocycle seeds on validated finite triangulations.

A maximal-tree gauge removes vertex coboundaries. Sparse rational elimination
finds the remaining kernel; in dimension one, clearing denominators and the
coordinate gcd gives a primitive integral generator. This constructs one
coherent normal surface, not a complete normal-surface search.
"""
from fractions import Fraction
from itertools import combinations
from math import gcd, lcm

from .normal_surface_geometry import _prepare, _EDGES, _edge, _quad, NormalOrbitError


class CocycleLimit(RuntimeError):
    """A local cocycle/seed work allowance was exhausted."""


class _Budget:
    def __init__(self, check, maximum):
        if maximum is not None and (type(maximum) is not int or maximum < 0):
            raise ValueError('max_work must be a nonnegative integer or None')
        self.check, self.maximum, self.work = check, maximum, 0

    def tick(self):
        self.check()
        self.work += 1
        if self.maximum is not None and self.work > self.maximum:
            raise CocycleLimit('normal-cocycle work allowance exhausted')


def local_coordinates(heights):
    order = sorted(range(4), key=lambda v: (heights[v], v))
    a, b, c, d = order
    row = [0] * 7
    row[a], row[d] = heights[b]-heights[a], heights[d]-heights[c]
    row[4+_quad(a, b)] = heights[c]-heights[b]
    return row


def _rank_one_cocycle_seed_details(triangulation, *, max_work=None, check=lambda: None):
    """Return primitive local heights and coordinates, or reject other ranks.

    Global edge orientation is recovered from the manifold validator's signed
    edge equivalences; its unoriented endpoint dictionary is not reused.
    """
    budget = _Budget(check, max_work)
    p = _prepare(triangulation, budget.tick)
    n = len(p['tetrahedra'])
    parents = {v: v for v in p['vertex_roots']}
    sizes = {v: 1 for v in parents}

    def find(v):
        while parents[v] != v:
            parents[v] = parents[parents[v]]
            v = parents[v]
        return v

    endpoints = {}
    for t in range(n):
        budget.tick()
        for j, (a, b) in enumerate(_EDGES):
            e = 6*t+j
            pair = (p['vertex_roots'][4*t+a], p['vertex_roots'][4*t+b])
            if p['edge_orientations'][e]:
                pair = pair[::-1]
            root = p['edge_roots'][e]
            if root in endpoints and endpoints[root] != pair:
                raise ArithmeticError('signed global edge endpoints disagree')
            endpoints[root] = pair
    chords = []
    for edge, (a, b) in sorted(endpoints.items()):
        budget.tick()
        a, b = find(a), find(b)
        if a == b:
            chords.append(edge)
        else:
            if sizes[a] < sizes[b]:
                a, b = b, a
            parents[b] = a
            sizes[a] += sizes[b]
    index = {edge: i for i, edge in enumerate(chords)}

    def oriented_edge(t, a, b):
        e = _edge(t, a, b)
        return index.get(p['edge_roots'][e]), -1 if p['edge_orientations'][e] else 1

    rows = []
    for t in range(n):
        for a, b, c in combinations(range(4), 3):
            budget.tick()
            row = {}
            for left, right, sign in ((a, b, 1), (b, c, 1), (a, c, -1)):
                i, orientation = oriented_edge(t, left, right)
                if i is not None:
                    row[i] = row.get(i, 0) + sign*orientation
            rows.append({i: value for i, value in row.items() if value})
    values, kernel_stats = _rank_one_kernel(rows, len(chords), budget)
    denominator = 1
    for value in values:
        budget.tick()
        denominator = lcm(denominator, value.denominator)
    integers, common = [], 0
    for value in values:
        budget.tick()
        value = int(value*denominator)
        integers.append(value)
        common = gcd(common, value)
    # The old left-to-right echelon form sets its last nonzero coordinate
    # positive. Preserve that orientation regardless of the sparse pivot order.
    if next(value for value in reversed(integers) if value) < 0:
        common = -common
    integers = [value//common for value in integers]
    heights, coordinates = [], []
    for t in range(n):
        budget.tick()
        row = [0]
        for v in range(1, 4):
            i, sign = oriented_edge(t, 0, v)
            row.append(0 if i is None else sign*integers[i])
        heights.append(row)
        coordinates.append(local_coordinates(row))
    seed = dict(vertices=[p['vertex_roots'][4*t:4*t+4] for t in range(n)],
                heights=heights, coordinates=coordinates,
                stats=dict(work=budget.work, chords=len(chords), **kernel_stats,
                           height_bits=max(abs(x).bit_length() for row in heights for x in row)))

    return seed, p


def rank_one_cocycle_seed(triangulation, *, max_work=None, check=lambda: None):
    """Return primitive local heights and coordinates, or reject other ranks."""
    return _rank_one_cocycle_seed_details(triangulation, max_work=max_work, check=check)[0]


def _rank_one_kernel(rows, dimension, budget):
    """Sparse exact elimination, prioritizing short rows and unit pivots.

    Each eliminated variable is stored in terms of still-live variables.
    Reverse elimination order, rather than column order, reconstructs the
    kernel. Column incidence limits updates to rows containing the pivot.
    """
    columns = [set() for _ in range(dimension)]
    buckets = [set() for _ in range(dimension+1)]
    for r, row in enumerate(rows):
        budget.tick()
        if row:
            buckets[len(row)].add(r)
        for i in row:
            budget.tick()
            columns[i].add(r)
    basis, eliminations, nonunit_pivots = {}, 0, 0
    shortest = 1
    peak_row = max(map(len, rows), default=0)
    while True:
        while shortest <= dimension and not buckets[shortest]:
            budget.tick()
            shortest += 1
        if shortest > dimension:
            break
        budget.tick()
        r = min(buckets[shortest])
        buckets[shortest].remove(r)
        row = rows[r]
        pivot = min(row, key=lambda i: (abs(row[i]) != 1, len(columns[i]), i))
        coefficient = row[pivot]
        nonunit_pivots += abs(coefficient) != 1
        normalized = {}
        for i, value in row.items():
            budget.tick()
            normalized[i] = (value/coefficient if isinstance(value, Fraction)
                              or isinstance(coefficient, Fraction) else
                              value//coefficient if abs(coefficient) == 1 else
                              Fraction(value, coefficient))
            columns[i].remove(r)
        basis[pivot] = normalized
        rows[r] = {}
        # Updates only remove entries from columns[pivot], so take a snapshot.
        for other in sorted(columns[pivot]):
            budget.tick()
            target = rows[other]
            buckets[len(target)].remove(other)
            factor = target[pivot]
            for i, value in normalized.items():
                budget.tick()
                old = target.get(i, 0)
                new = old-factor*value
                if new:
                    target[i] = new
                    if not old:
                        columns[i].add(other)
                else:
                    del target[i]
                    columns[i].remove(other)
                eliminations += 1
            if target:
                size = len(target)
                buckets[size].add(other)
                shortest = min(shortest, size)
                peak_row = max(peak_row, size)
    free = set(range(dimension))-basis.keys()
    if len(free) != 1:
        raise NormalOrbitError('cocycle seed requires first Betti number one')
    values = [0]*dimension
    values[free.pop()] = 1
    for pivot, row in reversed(basis.items()):
        total = 0
        for i, value in row.items():
            budget.tick()
            if i != pivot:
                total += value*values[i]
        values[pivot] = -total
    return values, dict(pivots=len(basis), eliminations=eliminations,
                        nonunit_pivots=nonunit_pivots, peak_row=peak_row)


def _height_summary(prepared, heights, *, potential=None, check=lambda: None):
    """Linear discovery-only cell count for an internally coherent cocycle.

    Edge intersections are absolute height differences; face arcs and local
    normal discs are the corresponding height spans. This is a prefilter,
    not matching, primitive-class, connectedness or source verification.
    Every possible positive is independently checked from its full vector.
    """
    rows, weights, pieces = [], {}, 0
    for t, hs in enumerate(heights):
        check()
        row = hs if potential is None else [h+potential[prepared['vertex_roots'][4*t+i]]
                                            for i, h in enumerate(hs)]
        rows.append(row)
        pieces += max(row)-min(row)
        for j, (a, b) in enumerate(_EDGES):
            weights[prepared['edge_roots'][6*t+j]] = abs(row[a]-row[b])
    arcs = 0
    faces = prepared['boundary_faces']+[(t,f) for t,f,_,_,_ in prepared['pairs']]
    for t,f in faces:
        check()
        hs = [rows[t][v] for v in range(4) if v != f]
        arcs += max(hs)-min(hs)
    return dict(euler_characteristic=sum(weights.values())-arcs+pieces,
                normal_pieces=pieces)
