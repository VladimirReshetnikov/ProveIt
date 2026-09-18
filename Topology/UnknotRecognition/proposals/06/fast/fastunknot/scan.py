"""Exact Bar-Natan scanning over F2 with cached cobordism arithmetic.

The complete recognizer still has exponential worst-case complexity.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from itertools import product
from time import monotonic
from typing import Any, Iterable
from .ordering import best_scan_order, scan_order, order_profile, validate_order
from .optimized_algebra import (Matching, Morphism, ScanLimit, glue, compose,
                                crossing_entries, identity, inverse, is_unit,
                                clear_caches, cache_statistics)

@dataclass
class Object:
    matching: Matching
    h: int


class ScanComplex:
    """The partial Khovanov complex of the processed part of a diagram."""

    def __init__(self, max_objects: int | None = None, deadline: float | None = None):
        self.objects: dict[int, Object] = {}
        self.out: dict[int, dict[int, Morphism]] = defaultdict(dict)
        self.inc: dict[int, set[int]] = defaultdict(set)
        self.points: frozenset = frozenset()
        self.closed_counts: dict[int, int] | None = None
        self.next_id = 0
        self.max_objects = max_objects
        self.deadline = deadline
        self.stats = {'max_objects_before_elimination': 0, 'max_objects_after_elimination': 0,
                      'eliminations': 0, 'max_boundary': 0, 'compositions': 0}
        self._new_object(frozenset(), 0)

    def _new_object(self, matching: Matching, h: int) -> int:
        i = self.next_id
        self.next_id += 1
        self.objects[i] = Object(matching, h)
        return i

    def _check(self) -> None:
        if self.deadline is not None and monotonic() > self.deadline:
            raise ScanLimit("time budget exhausted")

    def _set(self, a: int, b: int, morphism: Morphism) -> None:
        if morphism:
            self.out[a][b] = frozenset(morphism)
            self.inc[b].add(a)
        else:
            self.out[a].pop(b, None)
            self.inc[b].discard(a)

    def add_crossing(self, slots: tuple, *, reduce_now: bool = True,
                     verify_d_squared: bool = False) -> None:
        if self.closed_counts is not None:
            raise ValueError("cannot extend a completed closed complex")
        self._check()
        clear_caches()
        points, old_objects = self.points, self.objects
        new_id: dict = {}
        glued: dict = {}
        for o, obj in old_objects.items():
            self._check()
            for i in (0, 1):
                g = glue(obj.matching, i, points, slots)
                glued[o, i] = g
                for labels in product((0, 1), repeat=g.closed):
                    new_id[o, i, labels] = None
        if self.max_objects is not None and len(new_id) > self.max_objects:
            raise ScanLimit(f"{len(new_id)} objects would exceed the ceiling {self.max_objects}")
        objects: dict[int, Object] = {}
        self.objects = objects
        for (o, i, labels) in list(new_id):
            new_id[o, i, labels] = self._new_object(glued[o, i].matching, old_objects[o].h + i)
        old_out = self.out
        self.out, self.inc = defaultdict(dict), defaultdict(set)
        for o, obj in old_objects.items():
            self._check()
            _, _, entries = crossing_entries(obj.matching, obj.matching, identity(obj.matching),
                                             0, 1, points, slots)
            for (ls, lt), morphism in entries.items():
                self._set(new_id[o, 0, ls], new_id[o, 1, lt], morphism)
            for o2, f in old_out[o].items():
                m2 = old_objects[o2].matching
                for i in (0, 1):
                    _, _, entries = crossing_entries(obj.matching, m2, f, i, i, points, slots)
                    for (ls, lt), morphism in entries.items():
                        self._set(new_id[o, i, ls], new_id[o2, i, lt], morphism)
        self.points = next(iter(glued.values())).points if glued else frozenset()
        self.stats['max_objects_before_elimination'] = max(
            self.stats['max_objects_before_elimination'], len(objects))
        self.stats['max_boundary'] = max(self.stats['max_boundary'], len(self.points))
        if self.points:
            if reduce_now:
                self.eliminate()
            else:
                self.stats['deferred_crossings'] = self.stats.get('deferred_crossings', 0) + 1
            after = len(self.objects)
        else:
            if verify_d_squared:
                self.check_d_squared()
            self.eliminate_closed()
            after = sum(self.closed_counts.values())
        self.stats['max_objects_after_elimination'] = max(
            self.stats['max_objects_after_elimination'], after)

    def _invertible(self, a: int, b: int) -> bool:
        f = self.out[a].get(b)
        return (f is not None and is_unit(f)
                and self.objects[a].matching == self.objects[b].matching)

    def eliminate(self) -> None:
        """Cancel invertible entries until the complex is minimal (Bar-Natan's lemma)."""
        queue = [(a, b) for a in list(self.out) for b in list(self.out[a]) if self._invertible(a, b)]
        while queue:
            self._check()
            b, c = queue.pop()
            if b not in self.objects or c not in self.objects or not self._invertible(b, c):
                continue
            phi = self.out[b][c]
            m = self.objects[b].matching
            phi_inv = inverse(phi, m)
            ins = [(a, self.out[a][c]) for a in self.inc[c] if a != b]
            outs = [(f, self.out[b][f]) for f in self.out[b] if f != c]
            for a, delta in ins:
                ma = self.objects[a].matching
                half = compose(delta, phi_inv, ma, m, m)
                self.stats['compositions'] += 1
                for f, gamma in outs:
                    self._check()
                    mf = self.objects[f].matching
                    term = compose(half, gamma, ma, m, mf)
                    self.stats['compositions'] += 1
                    if term:
                        current = self.out[a].get(f, frozenset()) ^ term
                        self._set(a, f, current)
                        if current and self._invertible(a, f):
                            queue.append((a, f))
            for x in (b, c):
                for y in list(self.out[x]):
                    self._set(x, y, set())
                for y in list(self.inc[x]):
                    self._set(y, x, set())
                del self.objects[x]
                self.out.pop(x, None)
                self.inc.pop(x, None)
            self.stats['eliminations'] += 1

    def eliminate_closed(self) -> None:
        """At an empty boundary every differential coefficient is a scalar.

        Use Python integers as packed GF(2) columns instead of doing Schur
        updates in the cobordism category. Only dimensions of homology are
        retained, never a list of indistinguishable final generators.
        """
        by_h = defaultdict(list)
        for identifier, obj in self.objects.items():
            if obj.matching:
                raise ArithmeticError("nonempty matching at a closed boundary")
            by_h[obj.h].append(identifier)
        ranks = {}
        xors = 0
        for h, sources in by_h.items():
            targets = {identifier: i for i, identifier in enumerate(by_h.get(h + 1, []))}
            pivots = {}
            for a in sources:
                self._check()
                column = 0
                for b, coefficient in self.out.get(a, {}).items():
                    if coefficient != identity(frozenset()) or b not in targets:
                        raise ArithmeticError("invalid scalar differential at closure")
                    column ^= 1 << targets[b]
                while column:
                    pivot = column.bit_length() - 1
                    other = pivots.get(pivot)
                    if other is None:
                        pivots[pivot] = column
                        break
                    column ^= other
                    xors += 1
                    if xors & 1023 == 0:
                        self._check()
            ranks[h] = len(pivots)
        counts = {h: len(ids) - ranks.get(h, 0) - ranks.get(h - 1, 0)
                  for h, ids in by_h.items()}
        if any(value < 0 for value in counts.values()):
            raise ArithmeticError("negative homology dimension")
        self.closed_counts = dict(sorted((h, k) for h, k in counts.items() if k))
        self.stats['eliminations'] += sum(ranks.values())
        self.stats['closed_bitset_xors'] = xors
        self.stats['closed_generators'] = len(self.objects)
        self.objects.clear()
        self.out.clear()
        self.inc.clear()

    def total_rank(self) -> int:
        if self.points:
            raise ValueError("the diagram is not closed yet")
        if any(self.out[a] for a in list(self.out)):
            raise ArithmeticError("minimal closed complex still has a nonzero differential")
        return sum(self.closed_counts.values()) if self.closed_counts is not None else len(self.objects)

    def ranks_by_degree(self) -> dict[int, int]:
        if self.closed_counts is not None:
            return dict(self.closed_counts)
        counts: dict[int, int] = defaultdict(int)
        for obj in self.objects.values():
            counts[obj.h] += 1
        return dict(sorted(counts.items()))

    def check_d_squared(self) -> None:
        """Debug check: compose consecutive differentials and require zero."""
        for a in list(self.out):
            acc: dict = defaultdict(set)
            ma = self.objects[a].matching
            for b, f in self.out[a].items():
                mb = self.objects[b].matching
                for c, g in self.out[b].items():
                    acc[c] ^= compose(f, g, ma, mb, self.objects[c].matching)
            for c, value in acc.items():
                if value:
                    raise ArithmeticError(f"d^2 != 0 between objects {a} and {c}")


def _scan_rank(pd: Iterable[Iterable[int]], *, order: list[int] | None = None,
                  max_objects: int | None = None, seconds: float | None = None,
                  check_d_squared: bool = False, tail_crossings: int = 2) -> dict[str, Any]:
    """Total unreduced F2 Khovanov rank of a (validated) PD code by scanning."""
    if type(tail_crossings) is not int or tail_crossings < 1:
        raise ValueError("tail_crossings must be a positive integer")
    pd = [tuple(c) for c in pd]
    if not pd:
        return {'rank': 2, 'reduced_rank': 1, 'by_degree': {0: 2}, 'stats': {}, 'order': []}
    deadline = None if seconds is None else monotonic() + seconds
    order = best_scan_order(pd, tries=min(len(pd), 12), deadline=deadline) if order is None else validate_order(len(pd), order)
    complex_ = ScanComplex(max_objects=max_objects, deadline=deadline)
    for position, index in enumerate(order):
        complex_.add_crossing(pd[index], reduce_now=position < len(order) - tail_crossings,
                              verify_d_squared=check_d_squared)
        if check_d_squared:
            complex_.check_d_squared()
    rank = complex_.total_rank()
    return {'rank': rank, 'reduced_rank': rank // 2, 'by_degree': complex_.ranks_by_degree(),
            'stats': complex_.stats, 'order': order}


def khovanov_rank(pd: Iterable[Iterable[int]], *, order: list[int] | None = None,
                  max_objects: int | None = None, seconds: float | None = None,
                  check_d_squared: bool = False, tail_crossings: int = 2,
                  decompose: bool = True) -> dict[str, Any]:
    """Exact rank for a classical knot, optionally factored over visible sums.

    An explicit order bypasses decomposition and is always checked as a full
    permutation. No Reidemeister moves are applied here, so by_degree refers
    to the original cube grading. Without limits this is a complete algorithm.
    """
    from math import isfinite
    from .diagram import Diagram
    from .decompose import connected_sum_factors
    start = monotonic()
    if max_objects is not None and (type(max_objects) is not int or max_objects < 1):
        raise ValueError("max_objects must be a positive integer or None")
    if seconds is not None and (not isfinite(seconds) or seconds < 0):
        raise ValueError("seconds must be finite and nonnegative")
    if type(tail_crossings) is not int or tail_crossings < 1:
        raise ValueError("tail_crossings must be a positive integer")
    diagram = Diagram.from_pd(pd)
    deadline = None if seconds is None else start + seconds
    if order is not None:
        order = validate_order(diagram.crossings, order)
    factors, certificate = (connected_sum_factors(diagram, deadline=deadline)
                            if decompose and order is None else ([diagram], None))
    def scan(factor, chosen_order=None):
        remaining = None if deadline is None else max(0.0, deadline - monotonic())
        return _scan_rank(factor.pd, order=chosen_order, max_objects=max_objects,
                          seconds=remaining, check_d_squared=check_d_squared,
                          tail_crossings=tail_crossings)
    if len(factors) == 1:
        return scan(factors[0], order)
    memo = {}
    results = []
    reduced_degrees = {0: 1}
    for factor in factors:
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted during factor computations")
        if factor not in memo:
            memo[factor] = scan(factor)
        r = memo[factor]
        results.append(r)
        if any(count % 2 for count in r['by_degree'].values()):
            raise ArithmeticError("unreduced F2 knot rank is not twice its reduced rank")
        degrees = {int(h): count // 2 for h, count in r['by_degree'].items()}
        product_degrees = defaultdict(int)
        for h, count in reduced_degrees.items():
            for k, count2 in degrees.items():
                product_degrees[h + k] += count * count2
        reduced_degrees = dict(product_degrees)
    reduced = sum(reduced_degrees.values())
    stats = {}
    for key in ('max_objects_before_elimination', 'max_objects_after_elimination', 'max_boundary'):
        stats[key] = max(r['stats'].get(key, 0) for r in memo.values())
    for key in ('eliminations', 'compositions', 'closed_bitset_xors', 'closed_generators',
                'deferred_crossings'):
        stats[key] = sum(r['stats'].get(key, 0) for r in memo.values())
    stats.update({'factor_count': len(factors), 'distinct_factor_computations': len(memo)})
    return {'rank': 2 * reduced, 'reduced_rank': reduced,
            'by_degree': dict(sorted((h, 2 * count) for h, count in reduced_degrees.items())),
            'stats': stats, 'order': [], 'rank_representation': 'connected-sum-product',
            'decomposition': certificate, 'factor_results': results}
