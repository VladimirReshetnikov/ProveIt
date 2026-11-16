"""Exact finite reference algorithms for the accompanying iPRA paper.

Python data structures are convenient representatives of numerical tables.
These executable checks are not Lean proofs or iPRA derivations.  All searches
below range over explicitly finite input tables; the paper supplies numerical
codings, bounds, and the corresponding induction arguments.
"""
from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Category:
    objects: int
    source: tuple
    target: tuple
    identity: tuple
    composition: tuple  # composition[g][f] = g after f; -1 off its domain

    @property
    def arrows(self):
        return len(self.source)

    def comp(self, g, f):
        return self.composition[g][f]

    def hom(self, x, y):
        return tuple(f for f in range(self.arrows)
                     if self.source[f] == x and self.target[f] == y)

    def valid(self):
        n, m = self.objects, self.arrows
        if n < 0 or len(self.target) != m or len(self.identity) != n:
            return False
        if len(self.composition) != m or any(len(row) != m for row in self.composition):
            return False
        if any(not 0 <= x < n for x in self.source + self.target):
            return False
        for x, e in enumerate(self.identity):
            if not 0 <= e < m or self.source[e] != x or self.target[e] != x:
                return False
        for f in range(m):
            if self.comp(self.identity[self.target[f]], f) != f:
                return False
            if self.comp(f, self.identity[self.source[f]]) != f:
                return False
            for g in range(m):
                h = self.comp(g, f)
                if self.target[f] != self.source[g]:
                    if h != -1:
                        return False
                elif not (0 <= h < m and self.source[h] == self.source[f]
                          and self.target[h] == self.target[g]):
                    return False
        # Only index composite arrows after EVERY table entry was range checked.
        for f in range(m):
            for g in range(m):
                for k in range(m):
                    if self.target[f] == self.source[g] and self.target[g] == self.source[k]:
                        if self.comp(k, self.comp(g, f)) != self.comp(self.comp(k, g), f):
                            return False
        return True

    def opposite(self):
        return Category(self.objects, self.target, self.source, self.identity,
                        tuple(tuple(self.comp(f, g) for f in range(self.arrows))
                              for g in range(self.arrows)))


def thin_category(n, relation):
    """The supplied relation must be a finite preorder."""
    pairs = tuple((x, y) for x in range(n) for y in range(n) if relation(x, y))
    loc = {p: i for i, p in enumerate(pairs)}
    return Category(n, tuple(x for x, y in pairs), tuple(y for x, y in pairs),
                    tuple(loc[(x, x)] for x in range(n)),
                    tuple(tuple(loc[(x, v)] if y == u else -1 for x, y in pairs)
                          for u, v in pairs))


def cyclic_group(n):
    assert n > 0
    return Category(1, (0,) * n, (0,) * n, (0,),
                    tuple(tuple((g + f) % n for f in range(n)) for g in range(n)))


@dataclass(frozen=True)
class Functor:
    source: Category
    target: Category
    objects: tuple
    arrows: tuple

    def valid(self):
        c, d = self.source, self.target
        if not c.valid() or not d.valid():
            return False
        if len(self.objects) != c.objects or len(self.arrows) != c.arrows:
            return False
        if any(not 0 <= x < d.objects for x in self.objects):
            return False
        if any(not 0 <= f < d.arrows for f in self.arrows):
            return False
        for x in range(c.objects):
            if self.arrows[c.identity[x]] != d.identity[self.objects[x]]:
                return False
        for f in range(c.arrows):
            if (d.source[self.arrows[f]], d.target[self.arrows[f]]) != (
                    self.objects[c.source[f]], self.objects[c.target[f]]):
                return False
            for g in range(c.arrows):
                if c.target[f] == c.source[g]:
                    if self.arrows[c.comp(g, f)] != d.comp(self.arrows[g], self.arrows[f]):
                        return False
        return True


def all_functors(c, d):
    return tuple(f for obj in product(range(d.objects), repeat=c.objects)
                 for arr in product(range(d.arrows), repeat=c.arrows)
                 if (f := Functor(c, d, obj, arr)).valid())


def natural(f, g, eta):
    c, d = f.source, f.target
    if g.source != c or g.target != d or len(eta) != c.objects:
        return False
    if not f.valid() or not g.valid():
        return False
    for x, e in enumerate(eta):
        if not (0 <= e < d.arrows and d.source[e] == f.objects[x]
                and d.target[e] == g.objects[x]):
            return False
    return all(d.comp(eta[c.target[a]], f.arrows[a]) ==
               d.comp(g.arrows[a], eta[c.source[a]]) for a in range(c.arrows))


def functor_category(c, d):
    functors = all_functors(c, d)
    trans = tuple((i, j, e) for i, f in enumerate(functors)
                  for j, g in enumerate(functors)
                  for e in product(range(d.arrows), repeat=c.objects) if natural(f, g, e))
    index = {t: k for k, t in enumerate(trans)}
    ids = tuple(index[(i, i, tuple(d.identity[x] for x in f.objects))]
                for i, f in enumerate(functors))
    comp = tuple(tuple(index[(i, l, tuple(d.comp(v, u) for u, v in zip(e, h)))]
                       if j == k else -1 for i, j, e in trans)
                 for k, l, h in trans)
    return Category(len(functors), tuple(t[0] for t in trans), tuple(t[1] for t in trans), ids, comp)


@dataclass(frozen=True)
class SetDiagram:
    category: Category
    sizes: tuple
    maps: tuple
    contravariant: bool = False

    def valid(self):
        c = self.category
        if not c.valid() or len(self.sizes) != c.objects or len(self.maps) != c.arrows:
            return False
        if any(n < 0 for n in self.sizes):
            return False
        for f, row in enumerate(self.maps):
            s, t = c.source[f], c.target[f]
            if self.contravariant:
                s, t = t, s
            if len(row) != self.sizes[s] or any(not 0 <= y < self.sizes[t] for y in row):
                return False
        for x in range(c.objects):
            if self.maps[c.identity[x]] != tuple(range(self.sizes[x])):
                return False
        for f in range(c.arrows):
            for g in range(c.arrows):
                if c.target[f] == c.source[g]:
                    a, b = (g, f) if self.contravariant else (f, g)
                    if self.maps[c.comp(g, f)] != tuple(self.maps[b][y] for y in self.maps[a]):
                        return False
        return True


def limit(diagram):
    assert diagram.valid() and not diagram.contravariant
    c = diagram.category
    return tuple(t for t in product(*(range(n) for n in diagram.sizes))
                 if all(diagram.maps[f][t[c.source[f]]] == t[c.target[f]]
                        for f in range(c.arrows)))


def colimit(diagram):
    """Bounded transitive closure; return vertices, class representatives, quotient."""
    assert diagram.valid() and not diagram.contravariant
    c = diagram.category
    vertices = tuple((x, a) for x, n in enumerate(diagram.sizes) for a in range(n))
    lookup = {v: i for i, v in enumerate(vertices)}
    n = len(vertices)
    reach = [[i == j for j in range(n)] for i in range(n)]
    for f in range(c.arrows):
        for a, b in enumerate(diagram.maps[f]):
            i, j = lookup[(c.source[f], a)], lookup[(c.target[f], b)]
            reach[i][j] = reach[j][i] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                reach[i][j] = reach[i][j] or (reach[i][k] and reach[k][j])
    reps = tuple(next(j for j in range(n) if reach[i][j]) for i in range(n))
    classes = tuple(sorted(set(reps)))
    quotient = tuple(classes.index(r) for r in reps)
    return vertices, classes, quotient


def representable(c, a):
    homs = tuple(c.hom(x, a) for x in range(c.objects))
    maps = tuple(tuple(homs[c.source[f]].index(c.comp(h, f))
                       for h in homs[c.target[f]]) for f in range(c.arrows))
    return SetDiagram(c, tuple(map(len, homs)), maps, True), homs


def natural_sets(p, q, components):
    assert p.category == q.category and p.contravariant == q.contravariant
    c = p.category
    if len(components) != c.objects:
        return False
    for x, row in enumerate(components):
        if len(row) != p.sizes[x] or any(not 0 <= y < q.sizes[x] for y in row):
            return False
    for f in range(c.arrows):
        s, t = c.source[f], c.target[f]
        if p.contravariant:
            s, t = t, s
        for u in range(p.sizes[s]):
            if components[t][p.maps[f][u]] != q.maps[f][components[s][u]]:
                return False
    return True


def all_natural_sets(p, q):
    possibilities = [tuple(product(range(q.sizes[x]), repeat=p.sizes[x]))
                     for x in range(p.category.objects)]
    return tuple(t for t in product(*possibilities) if natural_sets(p, q, t))


def yoneda_expand(p, a, u):
    assert p.valid() and p.contravariant and 0 <= u < p.sizes[a]
    c = p.category
    return tuple(tuple(p.maps[h][u] for h in c.hom(x, a)) for x in range(c.objects))


def yoneda_extract(c, a, eta):
    return eta[a][c.hom(a, a).index(c.identity[a])]


def evaluation(m, n, code, x):
    """Table [n] -> [m]; natural base-m encoding, with empty cases explicit."""
    assert 0 <= code < m ** n and 0 <= x < n
    assert m > 0
    return code // (m ** x) % m


def curry(m, n, k, table):
    assert len(table) == k * n and all(0 <= y < m for y in table)
    return tuple(sum(table[x * n + y] * m ** y for y in range(n)) for x in range(k))


def uncurry(m, n, codes):
    assert all(0 <= c < m ** n for c in codes)
    return tuple(evaluation(m, n, c, y) for c in codes for y in range(n))
