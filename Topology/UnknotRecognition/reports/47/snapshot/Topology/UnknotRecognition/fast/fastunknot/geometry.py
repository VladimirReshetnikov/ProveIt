"""Combinatorial geometry shared by the scanners: matchings and gluing a crossing.

A matching is a frozenset of frozenset({p, q}) pairs of boundary edge labels.
"""
from __future__ import annotations

from collections import defaultdict
from functools import lru_cache

SMOOTHINGS = (((0, 1), (2, 3)), ((0, 3), (1, 2)))  # 0: (a,b),(c,d)   1: (a,d),(b,c)

Matching = frozenset  # frozenset of frozenset({p, q}) pairs of boundary labels
Morphism = set        # set of frozenset(circle keys); F2 coefficients


class ScanLimit(RuntimeError):
    """A user-selected ceiling was reached; this is never a knot verdict."""


def dsu_find(parent: dict, x):
    root = x
    while parent[root] != root:
        root = parent[root]
    while parent[x] != root:
        parent[x], x = root, parent[x]
    return root


@lru_cache(maxsize=None)
def circles(a: Matching, b: Matching) -> dict:
    """Map each boundary label to the key (frozenset of labels) of its circle in a u b~."""
    parent: dict = {}
    for pair in a | b:
        for p in pair:
            parent.setdefault(p, p)
    for pair in a | b:
        p, q = tuple(pair)
        rp, rq = dsu_find(parent, p), dsu_find(parent, q)
        if rp != rq:
            parent[rp] = rq
    groups: dict = defaultdict(list)
    for p in parent:
        groups[dsu_find(parent, p)].append(p)
    keys = {root: frozenset(members) for root, members in groups.items()}
    return {p: keys[dsu_find(parent, p)] for p in parent}


class Glued:
    """Result of attaching one smoothing of a crossing to a matching."""

    def __init__(self, points: frozenset, matching: Matching, closed: int, arc_of: dict | None = None):
        self.points = points
        self.matching = matching
        self.closed = closed                                   # number of closed circles created
        self.arc_of = {} if arc_of is None else arc_of         # arc id -> ('new', pair) | ('closed', index)

    def _fields(self):
        return (self.points, self.matching, self.closed, self.arc_of)

    def __eq__(self, other):
        return self._fields() == other._fields() if other.__class__ is self.__class__ else NotImplemented

    __hash__ = None

    def __repr__(self):
        return (f"Glued(points={self.points!r}, matching={self.matching!r}, closed={self.closed!r}, "
                f"arc_of={self.arc_of!r})")


def glue_uncached(m: Matching, smoothing_index: int, points: frozenset, slots: tuple) -> Glued:
    """Attach the crossing with edge labels `slots` (counterclockwise) to the region.

    Arc ids are ('m', pair) for arcs of m and ('s', j) for the two smoothing arcs.
    """
    adjacency: dict = defaultdict(list)
    for pair in m:
        p, q = tuple(pair)
        adjacency[('P', p)].append((('P', q), ('m', pair)))
        adjacency[('P', q)].append((('P', p), ('m', pair)))
    for j, (s, t) in enumerate(SMOOTHINGS[smoothing_index]):
        adjacency[('S', s)].append((('S', t), ('s', j)))
        adjacency[('S', t)].append((('S', s), ('s', j)))
    first_slot: dict = {}
    for j, label in enumerate(slots):
        if label in points:
            adjacency[('S', j)].append((('P', label), None))
            adjacency[('P', label)].append((('S', j), None))
        elif label in first_slot:
            j0 = first_slot[label]
            adjacency[('S', j)].append((('S', j0), None))
            adjacency[('S', j0)].append((('S', j), None))
        else:
            first_slot[label] = j

    def label_of(node):
        return node[1] if node[0] == 'P' else slots[node[1]]

    visited: set = set()
    new_pairs, arc_of, closed = [], {}, 0
    ends = [node for node, nbrs in adjacency.items() if len(nbrs) == 1]
    for start in ends:
        if start in visited:
            continue
        node, prev, arcs = start, None, []
        visited.add(node)
        while True:
            step = next(((nbr, arc) for nbr, arc in adjacency[node] if nbr != prev), None)
            if step is None:
                break
            nbr, arc = step
            if arc is not None:
                arcs.append(arc)
            prev, node = node, nbr
            visited.add(node)
            if len(adjacency[node]) == 1:
                break
        pair = frozenset((label_of(start), label_of(node)))
        if len(pair) != 2:
            raise ArithmeticError("degenerate boundary arc")
        new_pairs.append(pair)
        for arc in arcs:
            arc_of[arc] = ('new', pair)
    for start in adjacency:
        if start in visited:
            continue
        node, prev, arcs = start, None, []
        visited.add(node)
        while True:
            options = [(nbr, arc) for nbr, arc in adjacency[node] if nbr != prev]
            if not options:
                break
            nbr, arc = options[0]
            if arc is not None:
                arcs.append(arc)
            prev, node = node, nbr
            if node == start:
                break
            visited.add(node)
        for arc in arcs:
            arc_of[arc] = ('closed', closed)
        closed += 1
    new_points = frozenset(p for pair in new_pairs for p in pair)
    return Glued(new_points, frozenset(new_pairs), closed, arc_of)




glue = lru_cache(maxsize=1 << 16)(glue_uncached)
_dsu_find = dsu_find
