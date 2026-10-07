"""Numerical reference extracted from ProveIt's planar.py (MIT-0).

Source blob: 1078526e7e7dbaf0b7267728105d870d94136769.
The evaluate, component, find, basis, compose_plan and compose routines below
retain the repository algorithms. Unneeded geometry/transfer methods are omitted;
this is an excerpt harness, NOT a vendored full recognizer.
"""
from functools import lru_cache


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


def find(parent: list, x: int) -> int:
    root = x
    while parent[root] != root:
        root = parent[root]
    while parent[x] != root:
        parent[x], x = root, parent[x]
    return root


class ReferencePlanar:
    def __init__(self):
        self.ids = {(): 0}
        self.pairs = [()]
        self.partner = [{}]
        self.stats = {"plans": 0}
        self.bases = {}
        self.compose_plans = {}

    def stage(self, *args):
        self.bases.clear()
        self.compose_plans.clear()

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

    def basis(self, a: int, b: int):
        key = (a, b)
        found = self.bases.get(key)
        if found is None:
            pa, pb = self.partner[a], self.partner[b]
            owner = {}
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
        components = []
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


def brute(components, f, g):
    fs = [i for i in range(f.bit_length()) if f >> i & 1]
    gs = [i for i in range(g.bit_length()) if g >> i & 1]
    result = 0
    for tf in fs:
        for tg in gs:
            result ^= evaluate(components, tf, tg)
    return result


@lru_cache(maxsize=None)
def matchings(points: tuple):
    if not points:
        return ((),)
    first = points[0]
    out = []
    for j in range(1, len(points), 2):
        for a in matchings(points[1:j]):
            for b in matchings(points[j + 1:]):
                out.append(tuple(sorted(((first, points[j]),) + a + b)))
    return tuple(out)
