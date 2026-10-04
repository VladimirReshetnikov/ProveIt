"""Compiled F2 dotted-cobordism maps with bit-packed coefficients.

A monomial is a bit mask of dotted boundary circles. A morphism is an integer
whose bit at position `monomial` is that monomial's coefficient. In particular,
zero is 0 and an undotted disc on every circle is 1. Basis orders are local to
Hom(a,b), not global dot names. Geometry is compiled once, then reused.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from itertools import product
from typing import Callable

from .geometry import Matching, SMOOTHINGS, Glued, glue, _dsu_find


def bits(value: int):
    """Yield set-bit indices, without expanding the surrounding zero bits."""
    while value:
        bit = value & -value
        yield bit.bit_length() - 1
        value ^= bit


@dataclass(frozen=True)
class Basis:
    keys: tuple[frozenset, ...]
    owner: dict[int, int]


# Each component is (left input mask, right input mask, output mask, extra dots).
# Genus-positive components make an entire plan zero at compile time.
Component = tuple[int, int, int, int]


def evaluate_surface(components: tuple[Component, ...] | None, f: int, g: int = 0) -> int:
    """Evaluate one pair of monomials in a compiled genus-zero surface."""
    if components is None:
        return 0
    result = 1
    for left, right, boundary, extra in components:
        dots = (f & left).bit_count() + (g & right).bit_count() + extra
        if dots >= 2:
            return 0
        if not boundary:
            if dots != 1:
                return 0
            continue
        if dots:
            choices = (boundary,)
        else:
            choices = tuple(boundary ^ (1 << k) for k in bits(boundary))
        # Different connected components have disjoint output masks.
        nxt = 0
        for monomial in bits(result):
            for choice in choices:
                nxt ^= 1 << (monomial | choice)
        result = nxt
    return result


class Algebra:
    """Run-local, stage-local caches. No scan is retained by a global cache.

    Memoized scalar results are bounded in number and discarded on overflow.
    Geometry dictionaries are stage-local and reset after each crossing.
    Limits count cache entries, not bytes; an entry can itself be large.
    """
    def __init__(self, check: Callable[[], None] = lambda: None, cache_entries: int = 32768):
        self.check = check
        self.cache_entries = cache_entries
        self.stats = {"compose_calls": 0, "compose_cache_hits": 0,
                      "composition_plans": 0, "transfer_plans": 0,
                      "transfer_cache_hits": 0}
        self.clear()

    def clear(self):
        self.bases: dict[tuple, Basis] = {}
        self.composition: dict[tuple, tuple[Component, ...] | None] = {}
        self.composed: dict[tuple, int] = {}
        self.glued: dict[tuple, Glued] = {}
        self.transfers: dict[tuple, tuple] = {}
        self.transferred: dict[tuple, tuple] = {}

    def basis(self, a: Matching, b: Matching) -> Basis:
        key = (a, b)
        if key in self.bases:
            return self.bases[key]
        parent = {p: p for pair in a | b for p in pair}
        for pair in a | b:
            p, q = pair
            rp, rq = _dsu_find(parent, p), _dsu_find(parent, q)
            parent[rp] = rq
        groups = defaultdict(list)
        for p in parent:
            groups[_dsu_find(parent, p)].append(p)
        keys = tuple(sorted((frozenset(g) for g in groups.values()), key=min))
        result = Basis(keys, {p: i for i, circle in enumerate(keys) for p in circle})
        self.bases[key] = self.bases[b, a] = result
        return result

    def encode(self, morphism: set, a: Matching, b: Matching) -> int:
        basis = self.basis(a, b)
        index = {key: i for i, key in enumerate(basis.keys)}
        result = 0
        for term in morphism:
            mask = sum(1 << index[key] for key in term)
            result ^= 1 << mask
        return result

    def decode(self, value: int, a: Matching, b: Matching) -> set:
        keys = self.basis(a, b).keys
        return {frozenset(keys[i] for i in bits(mask)) for mask in bits(value)}

    def gluing(self, m: Matching, i: int, points: frozenset, slots: tuple) -> Glued:
        key = (m, i, points, slots)
        if key not in self.glued:
            # Bypass the compatibility module's global LRU; lifetime is one stage.
            self.glued[key] = glue.__wrapped__(m, i, points, slots)
        return self.glued[key]

    def composition_plan(self, a: Matching, b: Matching, c: Matching):
        key = (a, b, c)
        if key in self.composition:
            return self.composition[key]
        self.check()
        self.stats["composition_plans"] += 1
        ab, bc, ac = self.basis(a, b), self.basis(b, c), self.basis(a, c)
        parent = {(0, i): (0, i) for i in range(len(ab.keys))}
        parent.update({(1, i): (1, i) for i in range(len(bc.keys))})
        for pair in b:
            p = next(iter(pair))
            x, y = _dsu_find(parent, (0, ab.owner[p])), _dsu_find(parent, (1, bc.owner[p]))
            parent[x] = y
        members = defaultdict(list)
        for disk in parent:
            members[_dsu_find(parent, disk)].append(disk)
        counts, boundaries = defaultdict(int), defaultdict(int)
        for pair in b:
            p = next(iter(pair))
            counts[_dsu_find(parent, (0, ab.owner[p]))] += 1
        for side, matching, basis in ((0, a, ab), (1, c, bc)):
            for pair in matching:
                p = next(iter(pair))
                root = _dsu_find(parent, (side, basis.owner[p]))
                boundaries[root] |= 1 << ac.owner[p]
        components = []
        for root, disks in members.items():
            boundary = boundaries[root]
            chi = len(disks) - counts[root]
            genus2 = 2 - chi - boundary.bit_count()
            if genus2 < 0 or genus2 % 2:
                raise ArithmeticError("invalid surface Euler characteristic")
            if genus2:
                self.composition[key] = None
                return None
            left = sum(1 << i for side, i in disks if side == 0)
            right = sum(1 << i for side, i in disks if side == 1)
            components.append((left, right, boundary, 0))
        result = tuple(components)
        self.composition[key] = result
        return result

    def compose(self, f: int, g: int, a: Matching, b: Matching, c: Matching) -> int:
        """Return g o f. No caller may confuse a coefficient bitset with a dot mask."""
        self.stats["compose_calls"] += 1
        if not f or not g:
            return 0
        if a == b and f == 1:
            return g
        if b == c and g == 1:
            return f
        if a == b == c and f == g:
            return f & 1   # (constant + nilpotent)^2 = constant in characteristic two.
        key = (a, b, c, f, g)
        if key in self.composed:
            self.stats["compose_cache_hits"] += 1
            return self.composed[key]
        plan = self.composition_plan(a, b, c)
        result = 0
        if plan is not None:
            for tf in bits(f):
                self.check()
                for tg in bits(g):
                    result ^= evaluate_surface(plan, tf, tg)
        if len(self.composed) >= self.cache_entries:
            self.composed.clear()
        self.composed[key] = result
        return result

    def transfer_plan(self, a: Matching, b: Matching, i_src: int, i_tgt: int,
                      points: frozenset, slots: tuple):
        key = (a, b, i_src, i_tgt, points, slots)
        if key in self.transfers:
            return self.transfers[key]
        self.check()
        self.stats["transfer_plans"] += 1
        gs, gt = self.gluing(a, i_src, points, slots), self.gluing(b, i_tgt, points, slots)
        mm, nn = self.basis(a, b), self.basis(gs.matching, gt.matching)
        saddle = i_src != i_tgt
        disks = [('F', i) for i in range(len(mm.keys))]
        disks += [('I', 0)] if saddle else [('I', 0), ('I', 1)]
        def idisk(j):
            return ('I', 0 if saddle else j)
        parent = {d: d for d in disks}
        smoothing_of_slot = [{s: j for j, arc in enumerate(SMOOTHINGS[i]) for s in arc}
                             for i in (i_src, i_tgt)]
        unions, seen = [], {}
        for j, label in enumerate(slots):
            if label in points:
                unions.append((('F', mm.owner[label]), idisk(smoothing_of_slot[0][j])))
            elif label in seen:
                unions.append((idisk(smoothing_of_slot[0][seen[label]]),
                               idisk(smoothing_of_slot[0][j])))
            else:
                seen[label] = j
        for x, y in unions:
            rx, ry = _dsu_find(parent, x), _dsu_find(parent, y)
            parent[rx] = ry
        members = defaultdict(list)
        for d in disks:
            members[_dsu_find(parent, d)].append(d)
        roots = list(members)
        ri = {r: i for i, r in enumerate(roots)}
        disk_index = {d: ri[_dsu_find(parent, d)] for d in disks}
        glue_count = defaultdict(int)
        for x, _ in unions:
            glue_count[_dsu_find(parent, x)] += 1
        boundary = [0] * len(roots)
        closed_src, closed_tgt = [None] * gs.closed, [None] * gt.closed
        def record(disk, ref, closed):
            comp = disk_index[disk]
            kind, value = ref
            if kind == 'new':
                boundary[comp] |= 1 << nn.owner[next(iter(value))]
            else:
                closed[value] = comp
        for side, matching, glued, closed in ((0, a, gs, closed_src), (1, b, gt, closed_tgt)):
            for pair in matching:
                record(('F', mm.owner[next(iter(pair))]), glued.arc_of['m', pair], closed)
            for j in range(2):
                record(idisk(j), glued.arc_of['s', j], closed)
        if None in closed_src or None in closed_tgt:
            raise ArithmeticError("unattached closed circle")
        base_chi = [len(members[r]) - glue_count[r] for r in roots]
        input_masks = [0] * len(roots)
        for i in range(len(mm.keys)):
            input_masks[disk_index['F', i]] |= 1 << i
        plans = []
        for ls in product((0, 1), repeat=gs.closed):
            for lt in product((0, 1), repeat=gt.closed):
                chi, extra = base_chi[:], [0] * len(roots)
                for comp, lab in zip(closed_src, ls):
                    chi[comp] += 1
                    extra[comp] += lab
                for comp, lab in zip(closed_tgt, lt):
                    chi[comp] += 1
                    extra[comp] += 1 - lab
                components = []
                for k in range(len(roots)):
                    genus2 = 2 - chi[k] - boundary[k].bit_count()
                    if genus2 < 0 or genus2 % 2:
                        raise ArithmeticError("invalid crossing surface")
                    if genus2 or extra[k] >= 2:
                        break
                    components.append((input_masks[k], 0, boundary[k], extra[k]))
                else:
                    plans.append((ls, lt, tuple(components)))
        result = (gs, gt, tuple(plans))
        self.transfers[key] = result
        return result

    def crossing_entries(self, a: Matching, b: Matching, f: int, i_src: int, i_tgt: int,
                         points: frozenset, slots: tuple):
        key = (a, b, f, i_src, i_tgt, points, slots)
        if key in self.transferred:
            self.stats["transfer_cache_hits"] += 1
            return self.transferred[key]
        gs, gt, plans = self.transfer_plan(a, b, i_src, i_tgt, points, slots)
        entries = []
        for ls, lt, components in plans:
            value = 0
            for monomial in bits(f):
                value ^= evaluate_surface(components, monomial)
            if value:
                entries.append((ls, lt, value))
        result = (gs, gt, tuple(entries))
        if len(self.transferred) >= self.cache_entries:
            self.transferred.clear()
        self.transferred[key] = result
        return result
