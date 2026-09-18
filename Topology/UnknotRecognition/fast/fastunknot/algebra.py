"""Bit-packed F2 dotted-cobordism algebra with compiled gluing plans.

The circles of a u b~ are numbered 0..k-1 (``Basis``).  A monomial is a bit
mask of dotted circles; a morphism in Hom(a, b) is a Python integer whose bit
number ``mask`` is the coefficient of that monomial.  So 0 is the zero map and
1 is the undotted canonical cobordism (the identity when a == b).  Addition is
XOR.

The topology of a gluing (which discs merge into which components, their Euler
characteristics and boundary circles) does not depend on the dots, so it is
compiled once per triple of matchings (composition) or per pair of matchings
and crossing smoothing (transfer) into a ``plan``; evaluating a monomial
against a plan is a few popcounts.  This module replaces the set-based
reference implementation in ``scan_reference`` and is cross-checked against it
in the tests.  Ideas adopted from the acceleration proposals (compiled topology,
bit masks, identity and square shortcuts, result caches) are credited in the
synthesis report.
"""
from __future__ import annotations

from collections import defaultdict
from itertools import product
from typing import Callable

from .geometry import SMOOTHINGS, Glued, Matching, dsu_find, glue_uncached


def bits(value: int):
    """Indices of the set bits of ``value``."""
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value ^= low


class Basis:
    __slots__ = ("keys", "owner")

    def __init__(self, keys, owner):
        self.keys = keys      # tuple of frozensets of boundary labels, one per circle
        self.owner = owner    # boundary label -> circle index


def evaluate(plan, f: int, g: int = 0) -> int:
    """Value of one pair of monomials on a compiled genus-zero surface.

    ``plan`` is a tuple of components (left mask, right mask, boundary mask,
    extra dots); ``None`` means some component has positive genus.
    """
    result = 1
    for left, right, boundary, extra in plan:
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
            choices = [boundary ^ (1 << k) for k in bits(boundary)]
        nxt = 0
        for monomial in bits(result):
            for choice in choices:
                nxt ^= 1 << (monomial | choice)   # components have disjoint boundary masks
        result = nxt
    return result


class BitAlgebra:
    """Stage-local caches; ``clear()`` is called before every crossing."""

    zero = 0
    one = 1

    def __init__(self, check: Callable[[], None] = lambda: None, cache_entries: int = 1 << 16,
                 self_inverse: bool = True):
        self.check = check
        self.cache_entries = cache_entries
        self.self_inverse = self_inverse
        self.stats = {"compose_calls": 0, "compose_cache_hits": 0, "plans": 0}
        self.bases: dict = {}
        self.clear()

    def clear(self) -> None:
        self.bases = {}
        self.plans: dict = {}
        self.composed: dict = {}
        self.glued: dict = {}
        self.transfer_plans: dict = {}
        self.transferred: dict = {}

    # ----- bases ---------------------------------------------------------
    def basis(self, a: Matching, b: Matching) -> Basis:
        key = (a, b)
        found = self.bases.get(key)
        if found is not None:
            return found
        parent = {p: p for pair in a for p in pair}
        for pair in b:
            for p in pair:
                parent.setdefault(p, p)
        for matching in (a, b):
            for pair in matching:
                p, q = pair
                rp, rq = dsu_find(parent, p), dsu_find(parent, q)
                if rp != rq:
                    parent[rp] = rq
        groups = defaultdict(list)
        for p in parent:
            groups[dsu_find(parent, p)].append(p)
        keys = tuple(sorted((frozenset(g) for g in groups.values()), key=min))
        owner = {p: i for i, circle in enumerate(keys) for p in circle}
        found = Basis(keys, owner)
        self.bases[key] = self.bases[b, a] = found
        return found

    def is_unit(self, f: int) -> bool:
        return bool(f & 1)

    def encode(self, morphism, a: Matching, b: Matching) -> int:
        index = {key: i for i, key in enumerate(self.basis(a, b).keys)}
        value = 0
        for term in morphism:
            value ^= 1 << sum(1 << index[key] for key in term)
        return value

    def decode(self, value: int, a: Matching, b: Matching) -> set:
        keys = self.basis(a, b).keys
        return {frozenset(keys[i] for i in bits(mask)) for mask in bits(value)}

    # ----- composition ---------------------------------------------------
    def plan(self, a: Matching, b: Matching, c: Matching):
        key = (a, b, c)
        if key in self.plans:
            return self.plans[key]
        self.stats["plans"] += 1
        ab, bc, ac = self.basis(a, b), self.basis(b, c), self.basis(a, c)
        parent = {(0, i): (0, i) for i in range(len(ab.keys))}
        parent.update({(1, i): (1, i) for i in range(len(bc.keys))})
        gluings = defaultdict(int)
        for pair in b:
            p = next(iter(pair))
            x, y = dsu_find(parent, (0, ab.owner[p])), dsu_find(parent, (1, bc.owner[p]))
            if x != y:
                parent[x] = y
        for pair in b:
            gluings[dsu_find(parent, (0, ab.owner[next(iter(pair))]))] += 1
        members = defaultdict(list)
        for disc in parent:
            members[dsu_find(parent, disc)].append(disc)
        boundary = defaultdict(int)
        for side, matching, basis in ((0, a, ab), (1, c, bc)):
            for pair in matching:
                p = next(iter(pair))
                boundary[dsu_find(parent, (side, basis.owner[p]))] |= 1 << ac.owner[p]
        components = []
        for root, discs in members.items():
            mask = boundary[root]
            twice_genus = 2 - (len(discs) - gluings[root]) - mask.bit_count()
            if twice_genus < 0 or twice_genus % 2:
                raise ArithmeticError("impossible surface component in a composition")
            if twice_genus:
                components = None
                break
            left = sum(1 << i for side, i in discs if side == 0)
            right = sum(1 << i for side, i in discs if side == 1)
            components.append((left, right, mask, 0))
        result = None if components is None else tuple(components)
        self.plans[key] = result
        return result

    def compose(self, f: int, g: int, a: Matching, b: Matching, c: Matching) -> int:
        """g o f for f in Hom(a, b), g in Hom(b, c)."""
        self.stats["compose_calls"] += 1
        if not f or not g:
            return 0
        if f == 1 and a == b:
            return g
        if g == 1 and b == c:
            return f
        if a == b == c and f == g:
            return f & 1      # (c + nilpotent)^2 = c in characteristic two
        key = (a, b, c, f, g)
        cached = self.composed.get(key)
        if cached is not None:
            self.stats["compose_cache_hits"] += 1
            return cached
        plan = self.plan(a, b, c)
        result = 0
        if plan is not None:
            for tf in bits(f):
                self.check()
                for tg in bits(g):
                    result ^= evaluate(plan, tf, tg)
        if len(self.composed) >= self.cache_entries:
            self.composed.clear()
        self.composed[key] = result
        return result

    def inverse(self, f: int, m: Matching) -> int:
        """Inverse of a unit of End(m).  Over F2 every unit is an involution:
        (1 + nu)^2 = 1 + nu^2 and nu^2 = 0 because squares of monomials vanish
        and cross terms appear twice."""
        if not f & 1:
            raise ValueError("not a unit")
        if self.self_inverse:
            return f
        nu = f ^ 1
        result = power = 1
        while True:
            power = self.compose(power, nu, m, m, m)
            if not power:
                return result
            result ^= power

    # ----- adding a crossing --------------------------------------------
    def gluing(self, m: Matching, i: int, points: frozenset, slots: tuple) -> Glued:
        key = (m, i)
        found = self.glued.get(key)
        if found is None:
            found = self.glued[key] = glue_uncached(m, i, points, slots)
        return found

    def transfer_plan(self, a: Matching, b: Matching, i_src: int, i_tgt: int,
                      points: frozenset, slots: tuple):
        key = (a, b, i_src, i_tgt)
        if key in self.transfer_plans:
            return self.transfer_plans[key]
        gs, gt = self.gluing(a, i_src, points, slots), self.gluing(b, i_tgt, points, slots)
        mm, nn = self.basis(a, b), self.basis(gs.matching, gt.matching)
        saddle = i_src != i_tgt
        discs = [("F", i) for i in range(len(mm.keys))] + ([("I", 0)] if saddle else [("I", 0), ("I", 1)])

        def idisc(j):
            return ("I", 0 if saddle else j)

        parent = {d: d for d in discs}
        arc_of_slot = {s: j for j, arc in enumerate(SMOOTHINGS[i_src]) for s in arc}
        unions, seen = [], {}
        for j, label in enumerate(slots):
            if label in points:
                unions.append((("F", mm.owner[label]), idisc(arc_of_slot[j])))
            elif label in seen:
                unions.append((idisc(arc_of_slot[seen[label]]), idisc(arc_of_slot[j])))
            else:
                seen[label] = j
        for x, y in unions:
            rx, ry = dsu_find(parent, x), dsu_find(parent, y)
            if rx != ry:
                parent[rx] = ry
        members = defaultdict(list)
        for d in discs:
            members[dsu_find(parent, d)].append(d)
        roots = list(members)
        index = {r: i for i, r in enumerate(roots)}
        comp_of = {d: index[dsu_find(parent, d)] for d in discs}
        gluings = [0] * len(roots)
        for x, _ in unions:
            gluings[comp_of[x]] += 1
        boundary = [0] * len(roots)
        closed_src, closed_tgt = [None] * gs.closed, [None] * gt.closed

        def record(disc, ref, closed):
            kind, value = ref
            if kind == "new":
                boundary[comp_of[disc]] |= 1 << nn.owner[next(iter(value))]
            else:
                closed[value] = comp_of[disc]

        for matching, glued, closed in ((a, gs, closed_src), (b, gt, closed_tgt)):
            for pair in matching:
                record(("F", mm.owner[next(iter(pair))]), glued.arc_of["m", pair], closed)
            for j in range(2):
                record(idisc(j), glued.arc_of["s", j], closed)
        if None in closed_src or None in closed_tgt:
            raise ArithmeticError("closed circle without a bounding component")
        base_chi = [len(members[r]) - gluings[i] for i, r in enumerate(roots)]
        input_mask = [0] * len(roots)
        for i in range(len(mm.keys)):
            input_mask[comp_of["F", i]] |= 1 << i
        plans = []
        for ls in product((0, 1), repeat=gs.closed):
            for lt in product((0, 1), repeat=gt.closed):
                chi, extra = base_chi[:], [0] * len(roots)
                for comp, lab in zip(closed_src, ls):
                    chi[comp] += 1
                    extra[comp] += lab          # label x on a source circle: dotted cup
                for comp, lab in zip(closed_tgt, lt):
                    chi[comp] += 1
                    extra[comp] += 1 - lab      # coefficient of 1 on a target circle: dotted cap
                components = []
                for k in range(len(roots)):
                    twice_genus = 2 - chi[k] - boundary[k].bit_count()
                    if twice_genus < 0 or twice_genus % 2:
                        raise ArithmeticError("impossible surface component at a crossing")
                    if twice_genus or extra[k] >= 2:
                        break
                    components.append((input_mask[k], 0, boundary[k], extra[k]))
                else:
                    plans.append((ls, lt, tuple(components)))
        result = (gs, gt, tuple(plans))
        self.transfer_plans[key] = result
        return result

    def crossing_entries(self, a: Matching, b: Matching, f: int, i_src: int, i_tgt: int,
                         points: frozenset, slots: tuple):
        """Entries of (complex) tensor (crossing) after delooping: [(labels_src, labels_tgt, value)]."""
        key = (a, b, f, i_src, i_tgt)
        found = self.transferred.get(key)
        if found is not None:
            return found
        gs, gt, plans = self.transfer_plan(a, b, i_src, i_tgt, points, slots)
        entries = []
        for ls, lt, components in plans:
            value = 0
            for monomial in bits(f):
                value ^= evaluate(components, monomial)
            if value:
                entries.append((ls, lt, value))
        found = (gs, gt, tuple(entries))
        if len(self.transferred) >= self.cache_entries:
            self.transferred.clear()
        self.transferred[key] = found
        return found
