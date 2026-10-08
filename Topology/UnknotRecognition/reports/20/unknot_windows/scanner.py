"""Readable scanner used for paired experiments and independent regression tests.

The gluing and cancellation formulas follow ProveIt fastunknot 0.2.  This is a
source-derived reference backend, not a claim to be the entire upstream package.
"""
from __future__ import annotations
from collections import defaultdict
from itertools import product
from time import monotonic
from .algebra import BitAlgebra
from .geometry import ScanLimit

class ScanComplex:
    def __init__(self, max_objects=None, deadline=None, pivot='minfill', **kwargs):
        if pivot not in ('minfill', 'lifo'):
            raise ValueError('pivot must be minfill or lifo')
        if max_objects is not None and (type(max_objects) is not int or max_objects < 0):
            raise ValueError('max_objects must be a nonnegative integer')
        self.objects = {0: (frozenset(), 0)}
        self.out, self.inc = defaultdict(dict), defaultdict(set)
        self.points, self.next_id = frozenset(), 1
        self.max_objects, self.deadline, self.pivot = max_objects, deadline, pivot
        self.algebra = BitAlgebra(self._check)
        self.stats = {'max_objects_before_elimination': 0, 'max_objects_after_elimination': 0,
                      'eliminations': 0, 'compositions': 0, 'max_boundary': 0}
    def _new_id(self):
        ident = self.next_id
        self.next_id += 1
        return ident
    def _check(self):
        if self.deadline is not None and monotonic() > self.deadline:
            raise ScanLimit('time budget exhausted')
    def _set(self, a, b, value):
        if value:
            self.out[a][b] = value
            self.inc[b].add(a)
        else:
            self.out[a].pop(b, None)
            self.inc[b].discard(a)
    def add_crossing(self, slots, reduce_now=True):
        self._check()
        alg = self.algebra
        alg.clear()
        points, old, old_out = self.points, self.objects, self.out
        new_id, glued, count = {}, {}, 0
        for o, (matching, h) in old.items():
            for i in (0, 1):
                g = alg.gluing(matching, i, points, slots)
                glued[o, i] = g
                count += 1 << g.closed
        if self.max_objects is not None and count > self.max_objects:
            raise ScanLimit(f'{count} objects would exceed ceiling {self.max_objects}')
        self.objects = {}
        for (o, i), g in glued.items():
            for labels in product((0, 1), repeat=g.closed):
                ident = self._new_id()
                new_id[o, i, labels] = ident
                self.objects[ident] = (g.matching, old[o][1] + i)
        self.out, self.inc = defaultdict(dict), defaultdict(set)
        for o, (matching, _) in old.items():
            self._check()
            for ls, lt, value in alg.crossing_entries(matching, matching, 1, 0, 1, points, slots)[2]:
                self._set(new_id[o, 0, ls], new_id[o, 1, lt], value)
            for o2, f in old_out.get(o, {}).items():
                for i in (0, 1):
                    for ls, lt, value in alg.crossing_entries(matching, old[o2][0], f, i, i, points, slots)[2]:
                        self._set(new_id[o, i, ls], new_id[o2, i, lt], value)
        self.points = next(iter(glued.values())).points if glued else frozenset()
        self.stats['max_objects_before_elimination'] = max(self.stats['max_objects_before_elimination'], len(self.objects))
        self.stats['max_boundary'] = max(self.stats['max_boundary'], len(self.points))
        if reduce_now:
            self.eliminate()
            self.stats['max_objects_after_elimination'] = max(self.stats['max_objects_after_elimination'], len(self.objects))
    def _invertible(self, a, b):
        f = self.out.get(a, {}).get(b, 0)
        return bool(f & 1) and self.objects[a][0] == self.objects[b][0]
    def eliminate(self):
        # A deliberately transparent exhaustive search. Its O(M^3) bound is
        # sufficient here; the upstream backend uses a more efficient lazy heap.
        while True:
            self._check()
            candidates = [(a, b) for a in self.out for b in self.out[a] if self._invertible(a, b)]
            if not candidates:
                return
            if self.pivot == 'lifo':
                b, c = candidates[-1]
            else:
                b, c = min(candidates, key=lambda e: ((len(self.out[e[0]]) - 1) * (len(self.inc[e[1]]) - 1), e))
            alg, m = self.algebra, self.objects[b][0]
            inverse = alg.inverse(self.out[b][c], m)
            ins = [(a, self.out[a][c]) for a in sorted(self.inc[c]) if a != b]
            outs = [(f, v) for f, v in self.out[b].items() if f != c]
            for a, delta in ins:
                ma = self.objects[a][0]
                half = alg.compose(delta, inverse, ma, m, m)
                self.stats['compositions'] += 1
                if not half:
                    continue
                for f, gamma in outs:
                    term = alg.compose(half, gamma, ma, m, self.objects[f][0])
                    self.stats['compositions'] += 1
                    if term:
                        self._set(a, f, self.out[a].get(f, 0) ^ term)
            self.remove_objects((b, c))
            self.stats['eliminations'] += 1
    def remove_objects(self, ids):
        for x in list(ids):
            for y in list(self.out[x]):
                self._set(x, y, 0)
            for y in list(self.inc[x]):
                self._set(y, x, 0)
            self.objects.pop(x)
            self.out.pop(x, None)
            self.inc.pop(x, None)
    def linear_ranks(self):
        if self.points:
            raise ValueError('not a closed complex')
        by_degree = defaultdict(list)
        for ident, (_, h) in self.objects.items():
            by_degree[h].append(ident)
        ranks = {}
        for h, sources in by_degree.items():
            index = {ident: k for k, ident in enumerate(by_degree.get(h + 1, []))}
            pivots = {}
            for a in sources:
                column = 0
                for b, value in self.out.get(a, {}).items():
                    if value not in (0, 1):
                        raise ArithmeticError('closed differential is not scalar')
                    if value:
                        column ^= 1 << index[b]
                while column:
                    p = column.bit_length() - 1
                    if p not in pivots:
                        pivots[p] = column
                        break
                    column ^= pivots[p]
            ranks[h] = len(pivots)
        return {h: len(v) - ranks.get(h, 0) - ranks.get(h - 1, 0) for h, v in by_degree.items()
                if len(v) - ranks.get(h, 0) - ranks.get(h - 1, 0)}
