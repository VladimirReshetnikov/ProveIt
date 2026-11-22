"""Finite rational Helly certificates. Only Python's standard library is needed.

Index the n sets by 0,...,n-1. For h=min(n,d+1), local maps each increasing
h-tuple of indices to one length-d point. Its incidence with the original
sets is a premise. The verifier checks the conclusion about convex hulls of
the supplied points. Coordinates and weights use int or fractions.Fraction.
"""

from collections.abc import Mapping
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations

Subset = tuple[int, ...]
Point = tuple[Fraction, ...]
Row = dict[Subset, Fraction]


@dataclass
class Certificate:
    point: Point
    rows: tuple[Row, ...]


def _q(value):
    if type(value) is int or isinstance(value, Fraction):
        return Fraction(value)
    raise ValueError("a coordinate or weight must be an int or Fraction")


def _point(d, coords):
    result = tuple(_q(t) for t in coords)
    if len(result) != d:
        raise ValueError("point dimension differs from d")
    return result


def _prepare(d, n, local):
    if type(d) is not int or type(n) is not int or min(d, n) < 0:
        raise ValueError("d and n must be natural numbers")
    if not isinstance(local, Mapping):
        raise ValueError("local must be a mapping")
    if n == 0 and not local:
        return {}
    keys = list(combinations(range(n), min(n, d + 1)))
    if set(keys) != set(local):
        raise ValueError("local must have one point for every required subset")
    return {key: _point(d, local[key]) for key in keys}


def _det(matrix):
    """Compute a square determinant by reversible rational row operations."""
    a = [list(row) for row in matrix]
    size = len(a)
    total = Fraction(1)
    for col in range(size):
        pivot = next((i for i in range(col, size) if a[i][col]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            total = -total
        total *= a[col][col]
        for i in range(col + 1, size):
            factor = a[i][col] / a[col][col]
            for j in range(col + 1, size):
                a[i][j] -= factor * a[col][j]
    return total


def _dependence(points):
    """Find a signed affine dependence by the largest nonzero minor."""
    d = len(points[0])
    a = [[point[k] for point in points] for k in range(d)]
    a.append([Fraction(1)] * len(points))
    for rank in range(d + 1, 0, -1):
        for cols in combinations(range(len(points)), rank):
            for rows in combinations(range(d + 1), rank):
                block = [[a[i][j] for j in cols] for i in rows]
                det = _det(block)
                if not det:
                    continue
                outside = next(j for j in range(len(points)) if j not in cols)
                c = [Fraction(0)] * len(points)
                c[outside] = det
                for pos, col in enumerate(cols):
                    changed = [list(row) for row in block]
                    for k, row in enumerate(rows):
                        changed[k][pos] = a[row][outside]
                    c[col] = -_det(changed)
                return c
    raise ArithmeticError("the row of ones guarantees a nonzero minor")


def radon_weights(points):
    """Return two disjoint convex coefficient vectors with equal barycentres."""
    if len(points) < 2 or len(points) != len(points[0]) + 2:
        raise ValueError("Radon requires exactly d+2 points in dimension d")
    points = [_point(len(points[0]), p) for p in points]
    c = _dependence(points)
    zero = Fraction(0)
    mass = sum((v for v in c if v > 0), zero)
    return (tuple(max(v, zero) / mass for v in c),
            tuple(max(-v, zero) / mass for v in c))


def sparsify(d, points, row):
    """Prune one convex coefficient row to at most d+1 terms at the same point."""
    if type(d) is not int or d < 0:
        raise ValueError("d must be a natural number")
    weights = {}
    for k, value in row.items():
        weight = _q(value)
        if weight:
            weights[k] = weight
    if any(w < 0 for w in weights.values()) or sum(weights.values()) != 1:
        raise ValueError("a convex row must be nonnegative and sum to one")
    used = {k: _point(d, points[k]) for k in weights}
    while len(weights) > d + 1:
        keys = list(weights)[:d + 2]
        c = _dependence([used[k] for k in keys])
        step = min(weights[k] / v for k, v in zip(keys, c) if v > 0)
        for k, v in zip(keys, c):
            weights[k] -= step * v
            if weights[k] == 0:
                del weights[k]
    return weights


@dataclass
class _Node:
    point: Point
    rows: dict[int, Row]


def helly(d, n, local, compact=False):
    """Build a certificate. With compact=True each final row has ≤d+1 terms."""
    seeds = _prepare(d, n, local)
    if n == 0:
        return Certificate((Fraction(0),) * d, ())
    indices = range(n)
    h = min(n, d + 1)
    previous = {
        t: _Node(p, {i: {t: Fraction(1)} for i in t})
        for t, p in seeds.items()
    }
    for k in range(h + 1, n + 1):
        current = {}
        for subset in combinations(indices, k):
            omitted = subset[:d + 2]
            children = [previous[tuple(i for i in subset if i != j)]
                        for j in omitted]
            plus, minus = radon_weights([child.point for child in children])
            point = tuple(sum(w * child.point[q] for w, child in zip(plus, children))
                          for q in range(d))
            rows = {}
            for i in subset:
                active = minus if i in omitted and plus[omitted.index(i)] else plus
                row = {}
                for w, child in zip(active, children):
                    if w:
                        for t, v in child.rows[i].items():
                            row[t] = row.get(t, Fraction(0)) + w * v
                rows[i] = row
            current[subset] = _Node(point, rows)
        previous = current
    final = previous[tuple(indices)]
    rows = tuple(final.rows[i] for i in indices)
    if compact:
        rows = tuple(sparsify(d, seeds, row) for row in rows)
    return Certificate(final.point, rows)


def verify(d, n, local, certificate):
    """Check only the input dimensions and final barycentric identities."""
    try:
        seeds = _prepare(d, n, local)
        point = _point(d, certificate.point)
        if len(certificate.rows) != n:
            return False
        for i, row in enumerate(certificate.rows):
            if not isinstance(row, Mapping):
                return False
            total = Fraction(0)
            barycentre = [Fraction(0)] * d
            for t, value in row.items():
                w = _q(value)
                if t not in seeds or w < 0 or (w and i not in t):
                    return False
                total += w
                for q, coordinate in enumerate(seeds[t]):
                    barycentre[q] += w * coordinate
            if total != 1 or tuple(barycentre) != point:
                return False
        return True
    except (AttributeError, TypeError, ValueError):
        return False
