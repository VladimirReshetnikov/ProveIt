"""Source-derived execution fixture of upstream planar.py, retrieved 2026-10-07.

Executable statements follow source blob 1078526e7e7dbaf0b7267728105d870d94136769.
Comments and whitespace have been shortened; this is NOT a byte-identical copy.
Retained only to make the current-engine experiments independently reproducible.
"""
from __future__ import annotations
from .geometry import SMOOTHINGS
MATE = tuple({s: t for arc in sm for s, t in (arc, arc[::-1])} for sm in SMOOTHINGS)
ARC_OF = tuple({s: j for j, arc in enumerate(sm) for s in arc} for sm in SMOOTHINGS)

def evaluate(components, f: int, g: int = 0) -> int:
    result = 1
    for left, right, boundary, extra, choices in components:
        dots = (f & left).bit_count() + (g & right).bit_count() + extra
        if dots >= 2:
            return 0
        if dots:
            result <<= boundary
        elif not boundary:
            return 0
        else:
            nxt = 0
            for choice in choices:
                nxt ^= result << choice
            result = nxt
    return result

def component(left: int, right: int, boundary: int, extra: int) -> tuple:
    choices = []
    rest = boundary
    while rest:
        low = rest & -rest
        choices.append(boundary ^ low)
        rest ^= low
    return (left, right, boundary, extra, tuple(choices))

SHAPE_CACHE = 200_000

def find(parent: list, x: int) -> int:
    root = x
    while parent[root] != root:
        root = parent[root]
    while parent[x] != root:
        parent[x], x = root, parent[x]
    return root

class Planar:
    def __init__(self, shape_cache: bool = True):
        self.shape_cache = shape_cache
        self.ids: dict = {(): 0}
        self.pairs: list = [()]
        self.partner: list = [{}]
        self.stats = {"plans": 0, "shape_hits": 0, "result_hits": 0}
        self.shape_plans: dict = {}
        self.shape_ids: dict = {}
        self.shape_results: dict = {}
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

    def stage(self, points: frozenset, slots: tuple) -> None:
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
        if not self.shape_cache:
            return
        rank = {label: r for r, label in enumerate(sorted(points.union(slots)))}
        self.rank = rank
        if len(self.shape_plans) + len(self.shape_results) > SHAPE_CACHE:
            self.shape_plans.clear()
            self.shape_results.clear()
            self.shape_ids.clear()
        self.shape_slots = self.shape_ids.setdefault(("slots",) + tuple(rank[label] for label in slots), len(self.shape_ids))
        self.shapes: dict = {}
        self.shapes_after: dict = {}
        self.rank_after = None

    def shape_after(self, m: int) -> int:
        found = self.shapes_after.get(m)
        if found is None:
            rank = self.rank_after
            if rank is None:
                rank = self.rank_after = {label: r for r, label in enumerate(sorted(self.new_points()))}
            pairs = tuple((rank[p], rank[q]) for p, q in self.pairs[m])
            found = self.shapes_after[m] = self.shape_ids.setdefault(pairs, len(self.shape_ids))
        return found

    def shape(self, m: int) -> int:
        found = self.shapes.get(m)
        if found is None:
            rank = self.rank
            pairs = tuple((rank[p], rank[q]) for p, q in self.pairs[m])
            found = self.shapes[m] = self.shape_ids.setdefault(pairs, len(self.shape_ids))
        return found

    def new_points(self) -> frozenset:
        return (self.points - self.consumed) | frozenset(label for _, label in self.fresh)

    def basis(self, a: int, b: int):
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

    def glue(self, m: int, i: int):
        key = (m, i)
        found = self.glued.get(key)
        if found is not None:
            return found
        partner, slots, position, twin = self.partner[m], self.slots, self.position, self.twin
        ext = []
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

    def compose_plan(self, a: int, b: int, c: int):
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
            components.append(component(left[root], right[root], boundary[root], 0))
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

    def transfer_plan(self, a: int, b: int, i_src: int, i_tgt: int):
        key = (a, b, i_src, i_tgt)
        found = self.transfer_plans.get(key)
        if found is not None:
            return found
        shape_key = None
        if self.shape_cache:
            shapes = self.shapes
            sa, sb = shapes.get(a), shapes.get(b)
            if sa is None:
                sa = self.shape(a)
            if sb is None:
                sb = self.shape(b)
            shape_key = (sa, sb, self.shape_slots, i_src, i_tgt)
            found = self.shape_plans.get(shape_key)
            if found is not None:
                self.stats["shape_hits"] += 1
                self.transfer_plans[key] = found
                return found
        self.stats["plans"] += 1
        ga, closed_src, closed_of_src = self.glue(a, i_src)
        gb, closed_tgt, closed_of_tgt = self.glue(b, i_tgt)
        owner, _ = self.basis(a, b)
        new_owner, _ = self.basis(ga, gb)
        saddle = i_src != i_tgt
        arc_of = (0, 0, 0, 0) if saddle else ARC_OF[i_src]
        parent = [0] if saddle else [0, 1]
        local: dict = {}
        circle_of = [-1] * len(parent)
        glued_at = []
        twin = self.twin
        for j, label in enumerate(self.slots):
            y = arc_of[j]
            if self.inside[j]:
                d = owner[label]
                x = local.get(d)
                if x is None:
                    x = local[d] = len(parent)
                    parent.append(x)
                    circle_of.append(d)
            elif twin[j] > j:
                x = arc_of[twin[j]]
            else:
                continue
            glued_at.append(x)
            rx, ry = find(parent, x), find(parent, y)
            if rx != ry:
                parent[rx] = ry
        n = len(parent)
        index: dict = {}
        comp = [0] * n
        for x in range(n):
            comp[x] = index.setdefault(find(parent, x), len(index))
        count = len(index)
        chi, boundary, inputs = [0] * count, [0] * count, [0] * count
        touched_mask = 0
        for x in range(n):
            chi[comp[x]] += 1
            d = circle_of[x]
            if d >= 0:
                inputs[comp[x]] |= 1 << d
                touched_mask |= 1 << d
        for x in glued_at:
            chi[comp[x]] -= 1
        consumed = self.consumed
        renumber: dict = {}
        for p, d in owner.items():
            if p not in consumed:
                x = local.get(d)
                if x is None:
                    renumber[1 << d] = 1 << new_owner[p]
                else:
                    boundary[comp[x]] |= 1 << new_owner[p]
        for j, label in self.fresh:
            boundary[comp[arc_of[j]]] |= 1 << new_owner[label]
        comp_src = [0] * closed_src
        comp_tgt = [0] * closed_tgt
        for t in (0, 1):
            x = 0 if saddle else t
            if closed_of_src[t] >= 0:
                comp_src[closed_of_src[t]] = comp[x]
            if closed_of_tgt[t] >= 0:
                comp_tgt[closed_of_tgt[t]] = comp[x]
        plans = []
        for ls in range(1 << closed_src):
            for lt in range(1 << closed_tgt):
                euler, extra = chi[:], [0] * count
                for j, c in enumerate(comp_src):
                    euler[c] += 1
                    extra[c] += ls >> j & 1
                for j, c in enumerate(comp_tgt):
                    euler[c] += 1
                    extra[c] += 1 - (lt >> j & 1)
                components = []
                for t in range(count):
                    twice_genus = 2 - euler[t] - boundary[t].bit_count()
                    if twice_genus < 0 or twice_genus % 2:
                        raise ArithmeticError("impossible surface component at a crossing")
                    if twice_genus or extra[t] >= 2:
                        break
                    components.append(component(inputs[t], 0, boundary[t], extra[t]))
                else:
                    plans.append((ls, lt, tuple(components)))
        found = self.transfer_plans[key] = (tuple(plans), touched_mask, renumber, {})
        if shape_key is not None:
            self.shape_plans[shape_key] = found
        return found

    def transfer(self, a: int, b: int, f: int, i_src: int, i_tgt: int) -> tuple:
        plans, touched_mask, renumber, memo = self.transfer_plan(a, b, i_src, i_tgt)
        if not plans:
            return ()
        total = [0] * len(plans)
        while f:
            low = f & -f
            monomial = low.bit_length() - 1
            f ^= low
            core = monomial & touched_mask
            values = memo.get(core)
            if values is None:
                values = memo[core] = [evaluate(components, core) for _, _, components in plans]
            rest = monomial ^ core
            shift = 0
            while rest:
                low = rest & -rest
                shift |= renumber[low]
                rest ^= low
            for t, value in enumerate(values):
                total[t] ^= value << shift
        return tuple((plan[0], plan[1], value) for plan, value in zip(plans, total) if value)
