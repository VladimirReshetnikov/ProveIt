"""Reference F2 dotted cobordisms, following the audited ProveIt BitAlgebra.

This intentionally uses the existing pairwise composition strategy, not a new
subset-convolution backend. Speedups in the experiments are due to truncation.
"""
from __future__ import annotations
from collections import defaultdict
from itertools import product
from .geometry import SMOOTHINGS, find, glue

def bits(v: int):
    while v:
        low = v & -v
        yield low.bit_length() - 1
        v ^= low

def evaluate(plan, f: int, g: int = 0) -> int:
    result = 1
    for left, right, boundary, extra in plan:
        dots = (f & left).bit_count() + (g & right).bit_count() + extra
        if dots >= 2:
            return 0
        if not boundary:
            if dots != 1:
                return 0
            continue
        choices = (boundary,) if dots else tuple(boundary ^ (1 << k) for k in bits(boundary))
        nxt = 0
        for monomial in bits(result):
            for choice in choices:
                nxt ^= 1 << (monomial | choice)
        result = nxt
    return result

class BitAlgebra:
    zero = 0
    one = 1
    def __init__(self, check=lambda: None, cache_entries=4096):
        self.check, self.cache_entries = check, cache_entries
        self.stats = {'compose_calls': 0, 'compose_cache_hits': 0, 'plans': 0}
        self.clear()
    def clear(self):
        self.bases, self.plans, self.composed = {}, {}, {}
        self.glued, self.transfer_plans, self.transferred = {}, {}, {}
    def basis(self, a, b):
        key = (a, b)
        if key in self.bases:
            return self.bases[key]
        parent = {p: p for m in (a, b) for pair in m for p in pair}
        for m in (a, b):
            for pair in m:
                p, q = pair
                x, y = find(parent, p), find(parent, q)
                parent[x] = y
        groups = defaultdict(list)
        for p in parent:
            groups[find(parent, p)].append(p)
        keys = tuple(sorted((frozenset(g) for g in groups.values()), key=min))
        owner = {p: i for i, circle in enumerate(keys) for p in circle}
        self.bases[a, b] = self.bases[b, a] = (keys, owner)
        return keys, owner
    @staticmethod
    def is_unit(f):
        return bool(f & 1)
    @staticmethod
    def inverse(f, m):
        if not f & 1:
            raise ValueError('not a unit')
        return f
    def plan(self, a, b, c):
        key = (a, b, c)
        if key in self.plans:
            return self.plans[key]
        self.stats['plans'] += 1
        ab, abo = self.basis(a, b)
        bc, bco = self.basis(b, c)
        ac, aco = self.basis(a, c)
        parent = {(side, i): (side, i) for side, keys in ((0, ab), (1, bc)) for i in range(len(keys))}
        for pair in b:
            p = next(iter(pair))
            x, y = find(parent, (0, abo[p])), find(parent, (1, bco[p]))
            parent[x] = y
        gluings, members, boundary = defaultdict(int), defaultdict(list), defaultdict(int)
        for pair in b:
            gluings[find(parent, (0, abo[next(iter(pair))]))] += 1
        for disc in parent:
            members[find(parent, disc)].append(disc)
        for side, matching, owner in ((0, a, abo), (1, c, bco)):
            for pair in matching:
                p = next(iter(pair))
                boundary[find(parent, (side, owner[p]))] |= 1 << aco[p]
        components = []
        for root, discs in members.items():
            mask = boundary[root]
            genus2 = 2 - (len(discs) - gluings[root]) - mask.bit_count()
            if genus2 < 0 or genus2 % 2:
                raise ArithmeticError('invalid gluing genus')
            if genus2:
                self.plans[key] = None
                return None
            left = sum(1 << i for side, i in discs if side == 0)
            right = sum(1 << i for side, i in discs if side == 1)
            components.append((left, right, mask, 0))
        result = tuple(components)
        self.plans[key] = result
        return result
    def compose(self, f, g, a, b, c):
        self.stats['compose_calls'] += 1
        if not f or not g:
            return 0
        if f == 1 and a == b:
            return g
        if g == 1 and b == c:
            return f
        if a == b == c and f == g:
            return f & 1
        key = (a, b, c, f, g)
        if key in self.composed:
            self.stats['compose_cache_hits'] += 1
            return self.composed[key]
        plan, result = self.plan(a, b, c), 0
        if plan is not None:
            for tf in bits(f):
                self.check()
                for tg in bits(g):
                    result ^= evaluate(plan, tf, tg)
        if self.cache_entries:
            if len(self.composed) >= self.cache_entries:
                self.composed.clear()
            self.composed[key] = result
        return result
    def gluing(self, m, i, points, slots):
        key = (m, i)
        if key not in self.glued:
            self.glued[key] = glue(m, i, points, slots)
        return self.glued[key]
    def transfer_plan(self, a, b, isrc, itgt, points, slots):
        key = (a, b, isrc, itgt)
        if key in self.transfer_plans:
            return self.transfer_plans[key]
        gs, gt = self.gluing(a, isrc, points, slots), self.gluing(b, itgt, points, slots)
        mm, mo = self.basis(a, b)
        nn, no = self.basis(gs.matching, gt.matching)
        saddle = isrc != itgt
        discs = [('F', i) for i in range(len(mm))] + ([('I', 0)] if saddle else [('I', 0), ('I', 1)])
        def idisc(j):
            return ('I', 0 if saddle else j)
        parent = {d: d for d in discs}
        arcslot = {s: j for j, arc in enumerate(SMOOTHINGS[isrc]) for s in arc}
        unions, seen = [], {}
        for j, label in enumerate(slots):
            if label in points:
                unions.append((('F', mo[label]), idisc(arcslot[j])))
            elif label in seen:
                unions.append((idisc(arcslot[seen[label]]), idisc(arcslot[j])))
            else:
                seen[label] = j
        for x, y in unions:
            parent[find(parent, x)] = find(parent, y)
        members = defaultdict(list)
        for d in discs:
            members[find(parent, d)].append(d)
        roots = list(members)
        index = {r: i for i, r in enumerate(roots)}
        comp = {d: index[find(parent, d)] for d in discs}
        ng = len(roots)
        gluings, boundary = [0] * ng, [0] * ng
        closed_src, closed_tgt = [None] * gs.closed, [None] * gt.closed
        for x, _ in unions:
            gluings[comp[x]] += 1
        def record(disc, ref, closed):
            kind, value = ref
            if kind == 'new':
                boundary[comp[disc]] |= 1 << no[next(iter(value))]
            else:
                closed[value] = comp[disc]
        for matching, glued, closed in ((a, gs, closed_src), (b, gt, closed_tgt)):
            for pair in matching:
                record(('F', mo[next(iter(pair))]), glued.arc_of['m', pair], closed)
            for j in range(2):
                record(idisc(j), glued.arc_of['s', j], closed)
        if None in closed_src or None in closed_tgt:
            raise ArithmeticError('unassigned circle')
        basechi = [len(members[r]) - gluings[i] for i, r in enumerate(roots)]
        inputmask = [0] * ng
        for i in range(len(mm)):
            inputmask[comp['F', i]] |= 1 << i
        plans = []
        for ls in product((0, 1), repeat=gs.closed):
            for lt in product((0, 1), repeat=gt.closed):
                chi, extra = basechi[:], [0] * ng
                for j, lab in zip(closed_src, ls):
                    chi[j] += 1; extra[j] += lab
                for j, lab in zip(closed_tgt, lt):
                    chi[j] += 1; extra[j] += 1 - lab
                components = []
                for j in range(ng):
                    genus2 = 2 - chi[j] - boundary[j].bit_count()
                    if genus2 < 0 or genus2 % 2:
                        raise ArithmeticError('invalid crossing genus')
                    if genus2 or extra[j] >= 2:
                        break
                    components.append((inputmask[j], 0, boundary[j], extra[j]))
                else:
                    plans.append((ls, lt, tuple(components)))
        result = gs, gt, tuple(plans)
        self.transfer_plans[key] = result
        return result
    def crossing_entries(self, a, b, f, isrc, itgt, points, slots):
        key = (a, b, f, isrc, itgt)
        if key in self.transferred:
            return self.transferred[key]
        gs, gt, plans = self.transfer_plan(a, b, isrc, itgt, points, slots)
        entries = []
        for ls, lt, plan in plans:
            value = 0
            for monomial in bits(f):
                value ^= evaluate(plan, monomial)
            if value:
                entries.append((ls, lt, value))
        result = gs, gt, tuple(entries)
        if len(self.transferred) >= self.cache_entries:
            self.transferred.clear()
        self.transferred[key] = result
        return result
