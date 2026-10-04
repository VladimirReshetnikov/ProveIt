"""Exact Khovanov scanning over F2, with compiled bitset morphisms.

The algorithm remains exponential in general. It is not a reconstruction of
Lackenby's announced quasi-polynomial hierarchy algorithm. Public set-based
algebra helpers remain available for compatibility; the scanner uses integers.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from heapq import heappop, heappush
from itertools import product
from time import monotonic
from typing import Any, Iterable

from .algebra import Algebra
from .geometry import (Matching, Morphism, ScanLimit, compose, circles, glue,
                       identity, is_unit, crossing_entries)
from .ordering import best_scan_order, order_profile, scan_order, validate_order


def inverse(f: Morphism, m: Matching) -> Morphism:
    """In End(m) over F2, every unit is its own inverse: (1 + nu)^2 = 1."""
    if not is_unit(f):
        raise ValueError("not a unit")
    return set(f)


@dataclass(frozen=True)
class Object:
    matching: Matching
    h: int


class ScanComplex:
    """Partial complex with bounded-lifetime topology caches and sparse elimination."""
    def __init__(self, max_objects: int | None = None, deadline: float | None = None,
                 pivot: str = "markowitz", cache_entries: int = 32768):
        if pivot not in ("markowitz", "lifo"):
            raise ValueError("pivot must be markowitz or lifo")
        if max_objects is not None and (type(max_objects) is not int or max_objects < 0):
            raise ValueError("max_objects must be a nonnegative integer")
        self.objects = {}
        self.out, self.inc = defaultdict(dict), defaultdict(set)
        self.points = frozenset()
        self.next_id = 0
        self.deadline, self.max_objects, self.pivot = deadline, max_objects, pivot
        self.stats = {'max_objects_before_elimination': 0, 'max_objects_after_elimination': 0,
                      'eliminations': 0, 'max_boundary': 0, 'compositions': 0,
                      'max_morphism_bits': 0, 'max_differential_entries': 0}
        self.algebra = Algebra(self._check, cache_entries)
        self._new_object(frozenset(), 0)

    def _new_object(self, matching, h):
        i = self.next_id
        self.next_id += 1
        self.objects[i] = Object(matching, h)
        return i

    def _check(self):
        if self.deadline is not None and monotonic() >= self.deadline:
            raise ScanLimit("time budget exhausted")

    def _set(self, a, b, value):
        if value:
            self.out[a][b] = value
            self.inc[b].add(a)
            self.stats['max_morphism_bits'] = max(self.stats['max_morphism_bits'], value.bit_length())
        else:
            self.out[a].pop(b, None)
            self.inc[b].discard(a)

    def add_crossing(self, slots):
        self._check()
        self.algebra.clear()
        points, old_objects, old_out = self.points, self.objects, self.out
        new_id, glued = {}, {}
        for o, obj in old_objects.items():
            self._check()
            for i in (0, 1):
                g = self.algebra.gluing(obj.matching, i, points, slots)
                glued[o, i] = g
                for labels in product((0, 1), repeat=g.closed):
                    new_id[o, i, labels] = None
                    if self.max_objects is not None and len(new_id) > self.max_objects:
                        raise ScanLimit(f"object ceiling {self.max_objects} would be exceeded")
        self.objects = {}
        for o, i, labels in new_id:
            new_id[o, i, labels] = self._new_object(glued[o, i].matching, old_objects[o].h + i)
        self.out, self.inc = defaultdict(dict), defaultdict(set)
        for o, obj in old_objects.items():
            self._check()
            _, _, entries = self.algebra.crossing_entries(obj.matching, obj.matching, 1,
                                                         0, 1, points, slots)
            for ls, lt, value in entries:
                self._set(new_id[o, 0, ls], new_id[o, 1, lt], value)
            for o2, f in old_out.get(o, {}).items():
                self._check()
                for i in (0, 1):
                    _, _, entries = self.algebra.crossing_entries(
                        obj.matching, old_objects[o2].matching, f, i, i, points, slots)
                    for ls, lt, value in entries:
                        self._set(new_id[o, i, ls], new_id[o2, i, lt], value)
        self.points = next(iter(glued.values())).points if glued else frozenset()
        self.stats['max_objects_before_elimination'] = max(
            self.stats['max_objects_before_elimination'], len(self.objects))
        self.stats['max_boundary'] = max(self.stats['max_boundary'], len(self.points))
        self.stats['max_differential_entries'] = max(
            self.stats['max_differential_entries'], sum(map(len, self.out.values())))
        self.eliminate()
        self.stats['max_objects_after_elimination'] = max(
            self.stats['max_objects_after_elimination'], len(self.objects))

    def _invertible(self, a, b):
        return bool(self.out.get(a, {}).get(b, 0) & 1) and \
            self.objects[a].matching == self.objects[b].matching

    def _cost(self, a, b):
        return (len(self.out[a]) - 1) * (len(self.inc[b]) - 1)

    def eliminate(self):
        """Sparse Schur complements; lazy Markowitz-style priorities reduce fill-in.

        Priorities may be stale after unrelated degree changes. They affect only
        performance; every unit is reconsidered, including newly created units.
        """
        queue = []
        def push(a, b):
            if self.pivot == "lifo":
                queue.append((a, b))
            else:
                heappush(queue, (self._cost(a, b), a, b))
        for a in list(self.out):
            for b in self.out[a]:
                if self._invertible(a, b):
                    push(a, b)
        while queue:
            self._check()
            if self.pivot == "lifo":
                b, c = queue.pop()
            else:
                cost, b, c = heappop(queue)
            if b not in self.objects or c not in self.objects or not self._invertible(b, c):
                continue
            if self.pivot != "lifo" and cost != self._cost(b, c):
                push(b, c)
                continue
            phi_inv = self.out[b][c]  # All units are involutions over F2.
            m = self.objects[b].matching
            ins = [(a, self.out[a][c]) for a in sorted(self.inc[c]) if a != b]
            outs = [(f, value) for f, value in self.out[b].items() if f != c]
            for a, delta in ins:
                self._check()
                ma = self.objects[a].matching
                half = self.algebra.compose(delta, phi_inv, ma, m, m)
                self.stats['compositions'] += 1
                if not half:
                    continue
                for f, gamma in outs:
                    self._check()
                    term = self.algebra.compose(half, gamma, ma, m, self.objects[f].matching)
                    self.stats['compositions'] += 1
                    if term:
                        current = self.out[a].get(f, 0) ^ term
                        self._set(a, f, current)
                        if current and self._invertible(a, f):
                            push(a, f)
            for x in (b, c):
                for y in list(self.out[x]):
                    self._set(x, y, 0)
                for y in list(self.inc[x]):
                    self._set(y, x, 0)
                del self.objects[x]
                self.out.pop(x, None)
                self.inc.pop(x, None)
            self.stats['eliminations'] += 1

    def total_rank(self):
        if self.points:
            raise ValueError("diagram is not closed")
        if any(self.out.values()):
            raise ArithmeticError("nonzero differential in minimal closed complex")
        return len(self.objects)

    def ranks_by_degree(self):
        result = defaultdict(int)
        for obj in self.objects.values():
            result[obj.h] += 1
        return dict(sorted(result.items()))

    def check_d_squared(self):
        for a in list(self.out):
            self._check()
            acc = defaultdict(int)
            for b, f in self.out[a].items():
                for c, g in self.out[b].items():
                    acc[c] ^= self.algebra.compose(f, g, self.objects[a].matching,
                                                  self.objects[b].matching, self.objects[c].matching)
            if any(acc.values()):
                raise ArithmeticError(f"d^2 != 0 from object {a}")


def khovanov_rank(pd: Iterable[Iterable[int]], *, order: list[int] | None = None,
                  max_objects: int | None = None, seconds: float | None = None,
                  check_d_squared: bool = False, pivot: str = "markowitz",
                  factor: bool = True) -> dict[str, Any]:
    """F2 ranks of a validated one-component PD code; no grading normalization.

    Explicit orders disable connected-sum factorization, for controlled replay.
    Resource ceilings never turn an unfinished computation into a knot verdict.
    """
    if seconds is not None and seconds < 0:
        raise ValueError("seconds must be nonnegative")
    deadline = None if seconds is None else monotonic() + seconds
    def check():
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted")
    check()
    pd = [tuple(row) for row in pd]
    if order is not None:
        order = validate_order(len(pd), order)
    if not pd:
        return {'rank': 2, 'reduced_rank': 1, 'by_degree': {0: 2}, 'stats': {}, 'order': []}
    if factor and order is None:
        from .decompose import factor_rank
        value = factor_rank(pd, max_objects=max_objects, deadline=deadline,
                            check_d_squared=check_d_squared, pivot=pivot)
        if value is not None:
            return value
    order = best_scan_order(pd, tries=min(len(pd), 12), check=check) if order is None else order
    complex_ = ScanComplex(max_objects, deadline, pivot)
    for index in order:
        complex_.add_crossing(pd[index])
        if check_d_squared:
            complex_.check_d_squared()
    rank = complex_.total_rank()
    if rank % 2:
        raise ArithmeticError("unexpected odd unreduced knot rank over F2")
    complex_.stats.update(complex_.algebra.stats)
    return {'rank': rank, 'reduced_rank': rank // 2, 'by_degree': complex_.ranks_by_degree(),
            'stats': complex_.stats, 'order': order, 'backend': 'compiled-bitset-scan',
            'pivot': pivot, 'factorized': False}
