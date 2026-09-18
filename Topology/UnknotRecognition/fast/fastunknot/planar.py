"""Integer planar geometry for the default scanner.

``algebra.BitAlgebra`` compiles gluing plans from matchings stored as nested
frozensets, with tuple-keyed union-find dictionaries; once the bookkeeping of
the scanner was fixed, that compilation dominated small and medium inputs.
This module does the same computations with

* matchings interned as integers, each with a ``partner`` dictionary;
* circles of a u b~ found by walking partners alternately;
* a crossing glued by following the at most four strands through it;
* union-find over small integer lists;
* boundary circles of a transfer read off the surviving and the new labels,
  instead of visiting every arc of both matchings;
* transfers memoized per monomial, since morphisms between the same two
  matchings share their monomials.

The plans have the format of ``algebra.evaluate`` and the bit conventions of
``algebra`` (bit ``mask`` of a morphism is the coefficient of the monomial
``mask``; bit ``i`` of a monomial is a dot on circle ``i``).  Circle numbering
differs from ``BitAlgebra``, so values of the two must not be mixed.
"""
from __future__ import annotations

from .algebra import evaluate
from .geometry import SMOOTHINGS

MATE = tuple({s: t for arc in sm for s, t in (arc, arc[::-1])} for sm in SMOOTHINGS)      # other end of the arc
ARC_OF = tuple({s: j for j, arc in enumerate(sm) for s in arc} for sm in SMOOTHINGS)      # arc containing a slot


def find(parent: list, x: int) -> int:
    root = x
    while parent[root] != root:
        root = parent[root]
    while parent[x] != root:
        parent[x], x = root, parent[x]
    return root


class Planar:
    """Interned matchings and per-stage plan caches."""

    def __init__(self):
        self.ids: dict = {(): 0}          # sorted tuple of sorted pairs -> id
        self.pairs: list = [()]
        self.partner: list = [{}]
        self.stats = {"plans": 0}
        self.stage(frozenset(), (0, 0, 0, 0))

    def intern(self, pairs: tuple) -> int:
        ident = self.ids.get(pairs)
        if ident is None:
            ident = self.ids[pairs] = len(self.pairs)
            self.pairs.append(pairs)
            partner = {}
            for p, q in pairs:
                partner[p] = q
                partner[q] = p
            self.partner.append(partner)
        return ident

    # ----- stage -----------------------------------------------------------
    def stage(self, points: frozenset, slots: tuple) -> None:
        """Forget the caches of the previous crossing and fix the next one."""
        self.points, self.slots = points, slots
        self.inside = tuple(label in points for label in slots)
        self.position = {label: j for j, label in enumerate(slots) if label in points}
        self.twin = tuple(-1 if self.inside[j] or slots.count(label) == 1
                          else next(k for k in range(4) if k != j and slots[k] == label)
                          for j, label in enumerate(slots))
        self.consumed = frozenset(self.position)
        self.fresh = tuple((j, label) for j, label in enumerate(slots)
                           if not self.inside[j] and self.twin[j] < 0)
        self.bases: dict = {}
        self.glued: dict = {}
        self.compose_plans: dict = {}
        self.transfer_plans: dict = {}

    def new_points(self) -> frozenset:
        return (self.points - self.consumed) | frozenset(label for _, label in self.fresh)

    # ----- circles of a u b~ -------------------------------------------------
    def basis(self, a: int, b: int):
        """(owner: label -> circle index, number of circles); shared by (a, b) and (b, a)."""
        key = (a, b)
        found = self.bases.get(key)
        if found is None:
            pa, pb = self.partner[a], self.partner[b]
            owner: dict = {}
            k = 0
            for p in pa:
                if p not in owner:
                    q = p
                    while True:
                        owner[q] = k
                        q = pa[q]
                        owner[q] = k
                        q = pb[q]
                        if q == p:
                            break
                    k += 1
            found = self.bases[key] = self.bases[b, a] = (owner, k)
        return found

    # ----- gluing the crossing of this stage to a matching ---------------------
    def glue(self, m: int, i: int):
        """(new matching id, number of closed circles, closed index or -1 of each smoothing arc)."""
        key = (m, i)
        found = self.glued.get(key)
        if found is not None:
            return found
        partner, slots, position, twin = self.partner[m], self.slots, self.position, self.twin
        ext = []                                   # outside of slot j: (True, end label) | (False, slot)
        for j in range(4):
            if self.inside[j]:
                q = partner[slots[j]]
                k = position.get(q)
                ext.append((True, q) if k is None else (False, k))
            elif twin[j] >= 0:
                ext.append((False, twin[j]))
            else:
                ext.append((True, slots[j]))
        mate, arc_of = MATE[i], ARC_OF[i]
        consumed = self.consumed
        pairs = [pair for pair in self.pairs[m] if pair[0] not in consumed and pair[1] not in consumed]
        closed_of = [-1, -1]
        seen = [False, False]
        closed = 0
        for t, (u, v) in enumerate(SMOOTHINGS[i]):
            if seen[t]:
                continue
            seen[t] = True
            group = [t]
            ends = []
            for start, stop in ((v, u), (u, v)):
                j = start
                while True:
                    is_end, value = ext[j]
                    if is_end:
                        ends.append(value)
                        break
                    if value == stop:
                        break
                    t2 = arc_of[value]
                    seen[t2] = True
                    group.append(t2)
                    j = mate[value]
                if not ends:
                    break
            if not ends:
                for t2 in group:
                    closed_of[t2] = closed
                closed += 1
            else:
                p, q = ends
                if p == q:
                    raise ArithmeticError("degenerate boundary arc")
                pairs.append((p, q) if p < q else (q, p))
        pairs.sort()
        found = self.glued[key] = (self.intern(tuple(pairs)), closed, tuple(closed_of))
        return found

    # ----- composition ---------------------------------------------------------
    def compose_plan(self, a: int, b: int, c: int):
        """Plan of g o f for f in Hom(a, b), g in Hom(b, c); None if some component has genus."""
        key = (a, b, c)
        if key in self.compose_plans:
            return self.compose_plans[key]
        self.stats["plans"] += 1
        (own_ab, k1), (own_bc, k2), (own_ac, _) = self.basis(a, b), self.basis(b, c), self.basis(a, c)
        parent = list(range(k1 + k2))
        arcs = [p for p, _ in self.pairs[b]]
        for p in arcs:
            x, y = find(parent, own_ab[p]), find(parent, k1 + own_bc[p])
            if x != y:
                parent[x] = y
        gluings = [0] * (k1 + k2)
        for p in arcs:
            gluings[find(parent, own_ab[p])] += 1
        boundary = [0] * (k1 + k2)
        for p, _ in self.pairs[a]:
            boundary[find(parent, own_ab[p])] |= 1 << own_ac[p]
        for p, _ in self.pairs[c]:
            boundary[find(parent, k1 + own_bc[p])] |= 1 << own_ac[p]
        left, right, discs = [0] * (k1 + k2), [0] * (k1 + k2), [0] * (k1 + k2)
        for d in range(k1):
            root = find(parent, d)
            left[root] |= 1 << d
            discs[root] += 1
        for d in range(k2):
            root = find(parent, k1 + d)
            right[root] |= 1 << d
            discs[root] += 1
        components: list | None = []
        for root in range(k1 + k2):
            if not discs[root]:
                continue
            twice_genus = 2 - (discs[root] - gluings[root]) - boundary[root].bit_count()
            if twice_genus < 0 or twice_genus % 2:
                raise ArithmeticError("impossible surface component in a composition")
            if twice_genus:
                components = None
                break
            components.append((left[root], right[root], boundary[root], 0))
        result = None if components is None else (tuple(components), {})
        self.compose_plans[key] = result
        return result

    def compose(self, a: int, b: int, c: int, f: int, g: int) -> int:
        plan = self.compose_plan(a, b, c)
        if plan is None:
            return 0
        components, memo = plan
        result = 0
        fs = []
        while f:
            low = f & -f
            fs.append(low.bit_length() - 1)
            f ^= low
        while g:
            low = g & -g
            tg = low.bit_length() - 1
            g ^= low
            for tf in fs:
                key = (tf, tg)
                value = memo.get(key)
                if value is None:
                    value = memo[key] = evaluate(components, tf, tg)
                result ^= value
        return result

    # ----- the crossing ---------------------------------------------------------
    def transfer_plan(self, a: int, b: int, i_src: int, i_tgt: int):
        """((source label offset, target label offset, components), ...) and a memo dictionary."""
        key = (a, b, i_src, i_tgt)
        found = self.transfer_plans.get(key)
        if found is not None:
            return found
        self.stats["plans"] += 1
        ga, closed_src, closed_of_src = self.glue(a, i_src)
        gb, closed_tgt, closed_of_tgt = self.glue(b, i_tgt)
        owner, k = self.basis(a, b)
        new_owner, _ = self.basis(ga, gb)
        saddle = i_src != i_tgt
        arc_of = ARC_OF[i_src]
        n = k + (1 if saddle else 2)
        parent = list(range(n))
        gluings_at = []
        for j, label in enumerate(self.slots):
            if self.inside[j]:
                x, y = owner[label], k + (0 if saddle else arc_of[j])
            elif self.twin[j] > j:
                x, y = k + (0 if saddle else arc_of[j]), k + (0 if saddle else arc_of[self.twin[j]])
            else:
                continue
            gluings_at.append(x)
            rx, ry = find(parent, x), find(parent, y)
            if rx != ry:
                parent[rx] = ry
        touched = sorted({find(parent, d) for d in range(k, n)})
        index = {root: t for t, root in enumerate(touched)}
        count = len(touched)
        chi, boundary, inputs = [0] * count, [0] * count, [0] * count
        for d in range(n):
            t = index.get(find(parent, d))
            if t is not None:
                chi[t] += 1
                if d < k:
                    inputs[t] |= 1 << d
        for x in gluings_at:
            chi[index[find(parent, x)]] -= 1
        consumed = self.consumed
        untouched = []                                    # circles that only change their number
        done = set()
        for p, d in owner.items():
            if p in consumed:
                continue
            t = index.get(find(parent, d))
            if t is not None:
                boundary[t] |= 1 << new_owner[p]
            elif d not in done:
                done.add(d)
                untouched.append((1 << d, 0, 1 << new_owner[p], 0))
        for j, label in self.fresh:
            boundary[index[find(parent, k + (0 if saddle else arc_of[j]))]] |= 1 << new_owner[label]
        comp_src = [0] * closed_src
        comp_tgt = [0] * closed_tgt
        for t2 in (0, 1):
            if closed_of_src[t2] >= 0:
                comp_src[closed_of_src[t2]] = index[find(parent, k + (0 if saddle else t2))]
            if closed_of_tgt[t2] >= 0:
                comp_tgt[closed_of_tgt[t2]] = index[find(parent, k + (0 if saddle else t2))]
        plans = []
        for ls in range(1 << closed_src):
            for lt in range(1 << closed_tgt):
                euler, extra = chi[:], [0] * count
                for j, comp in enumerate(comp_src):
                    euler[comp] += 1
                    extra[comp] += ls >> j & 1            # label x on a source circle: dotted cup
                for j, comp in enumerate(comp_tgt):
                    euler[comp] += 1
                    extra[comp] += 1 - (lt >> j & 1)      # coefficient of 1 on a target circle: dotted cap
                components = []
                for t in range(count):
                    twice_genus = 2 - euler[t] - boundary[t].bit_count()
                    if twice_genus < 0 or twice_genus % 2:
                        raise ArithmeticError("impossible surface component at a crossing")
                    if twice_genus or extra[t] >= 2:
                        break
                    components.append((inputs[t], 0, boundary[t], extra[t]))
                else:
                    plans.append((ls, lt, tuple(components) + tuple(untouched)))
        found = self.transfer_plans[key] = (tuple(plans), {})
        return found

    def transfer(self, a: int, b: int, f: int, i_src: int, i_tgt: int) -> tuple:
        """Entries of f tensor the crossing after delooping: ((source offset, target offset, value), ...)."""
        plans, memo = self.transfer_plan(a, b, i_src, i_tgt)
        if not plans:
            return ()
        total = [0] * len(plans)
        while f:
            low = f & -f
            monomial = low.bit_length() - 1
            f ^= low
            values = memo.get(monomial)
            if values is None:
                values = memo[monomial] = [evaluate(components, monomial) for _, _, components in plans]
            for t, value in enumerate(values):
                total[t] ^= value
        return tuple((plan[0], plan[1], value) for plan, value in zip(plans, total) if value)
