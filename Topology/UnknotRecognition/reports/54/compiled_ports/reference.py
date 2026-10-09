"""Bounded literal oracles for testing only. Never used for huge inputs.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations
from bisect import bisect_right
from collections import Counter
from .profiles import Profiles, cuts_and_lengths


def literal_components(size, pairings, *, cones=(), cuts=None, point_cap=10000):
    if type(size) is not int or not 0 <= size <= point_cap:
        raise ValueError('literal oracle point cap exceeded or invalid size')
    parent = list(range(size))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(x, y):
        parent[find(x)] = find(y)
    for row in pairings:
        if not isinstance(row, (tuple, list)) or len(row) != 5:
            raise ValueError('pairing requires a,b,c,d,reverse')
        a, b, c, d, reverse = row
        if (any(type(x) is not int for x in row[:4]) or type(reverse) is not bool
                or not 0 <= a <= b < size or not 0 <= c <= d < size or b-a != d-c):
            raise ValueError('invalid interval pairing')
        for x in range(a, b + 1):
            union(x, a + d - x if reverse else x + c - a)
    if cones:
        if cuts is None:
            raise ValueError('literal cones require atom cuts')
        cuts, _ = cuts_and_lengths(size, cuts)
        m = len(cuts) - 1
        for atoms in cones:
            atoms = tuple(atoms)
            if any(type(j) is not int or not 0 <= j < m for j in atoms):
                raise ValueError('invalid cone atom')
            points = [x for j in set(atoms) for x in range(cuts[j], cuts[j+1])]
            if points:
                for x in points[1:]:
                    union(points[0], x)
    groups = {}
    for x in range(size):
        groups.setdefault(find(x), []).append(x)
    return tuple(tuple(v) for v in groups.values())


def literal_profiles(size, pairings, cuts, *, cones=(), point_cap=10000):
    cuts, lengths = cuts_and_lengths(size, cuts)
    histogram = Counter()
    for group in literal_components(size, pairings, cones=cones, cuts=cuts,
                                    point_cap=point_cap):
        counts = [0] * len(lengths)
        for x in group:
            counts[bisect_right(cuts, x) - 1] += 1
        histogram[tuple(counts)] += 1
    return Profiles.from_histogram(lengths, histogram)


def literal_weighted_backend(size, pairings, intervals, *, dimension=None, **kwargs):
    """API-shaped TEST oracle; not the maintained weighted AHT implementation."""
    groups = literal_components(size, pairings)
    dimension = dimension or (len(intervals[0][2]) if intervals else 1)
    point_weights = [[0] * dimension for _ in range(size)]
    for lo, hi, vector in intervals:
        for x in range(lo, hi):
            for j in range(dimension):
                point_weights[x][j] += vector[j]
    hist = Counter(tuple(sum(point_weights[x][j] for x in group) for j in range(dimension))
                   for group in groups)
    return dict(status='COMPLETE', orbit_count=len(groups),
                histogram=[dict(weight=list(v), orbits=c) for v, c in sorted(hist.items())],
                stats=dict(backend='literal-test-only'))
