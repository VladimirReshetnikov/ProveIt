#!/usr/bin/env python3
"""Exhaustive finite checks supporting the uniform proofs in 03_finite.tex.

Python 3 standard library only. This is independent finite-model validation,
not a proof of any universal theorem and not an iPRA proof checker.

Run: python3 code/finite_topology.py --max-n 4
"""
from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass


@dataclass(frozen=True)
class Space:
    rows: tuple[int, ...]  # bit y in rows[x] means x <= y

    @property
    def n(self):
        return len(self.rows)

    @property
    def full(self):
        return (1 << self.n) - 1

    def le(self, x, y):
        return bool(self.rows[x] & (1 << y))

    def is_open(self, a):
        return all(not (a >> x & 1) or not (self.rows[x] & ~a)
                   for x in range(self.n))

    def opens(self):
        return tuple(a for a in range(1 << self.n) if self.is_open(a))

    def closed(self):
        return tuple(self.full ^ a for a in self.opens())

    def interior(self, a):
        return sum(1 << x for x in range(self.n)
                   if self.rows[x] & a == self.rows[x])

    def closure(self, a):
        return sum(1 << x for x in range(self.n) if self.rows[x] & a)

    def upward(self, a):
        z = 0
        for x in range(self.n):
            if a >> x & 1:
                z |= self.rows[x]
        return z

    def components(self):
        unseen = self.full
        result = []
        while unseen:
            x = (unseen & -unseen).bit_length() - 1
            c = 1 << x
            for _ in range(self.n):
                old = c
                for y in range(self.n):
                    if old >> y & 1:
                        for z in range(self.n):
                            if self.le(y, z) or self.le(z, y):
                                c |= 1 << z
            result.append(c)
            unseen &= ~c
        return tuple(result)


def points(mask, n):
    return tuple(x for x in range(n) if mask >> x & 1)


def preorders(n):
    for raw in range(1 << (n * n)):
        rows = tuple((raw >> (x * n)) & ((1 << n) - 1) for x in range(n))
        if any(not (rows[x] >> x & 1) for x in range(n)):
            continue
        if any(rows[y] & ~rows[x]
               for x in range(n) for y in range(n) if rows[x] >> y & 1):
            continue
        yield Space(rows)


def preimage(f, a):
    return sum(1 << x for x, fx in enumerate(f) if a >> fx & 1)


def image(f, a):
    z = 0
    for x, fx in enumerate(f):
        if a >> x & 1:
            z |= 1 << fx
    return z


def monotone(p, q, f):
    return all(not p.le(x, y) or q.le(f[x], f[y])
               for x in range(p.n) for y in range(p.n))


def continuous(p, q, f):
    return all(p.is_open(preimage(f, u)) for u in q.opens())


def topology_test(n, family):
    full = (1 << n) - 1
    return (0 in family and full in family and
            all(a & b in family and a | b in family for a in family for b in family))


def verify_space(p, counts):
    n, full = p.n, p.full
    subsets = range(1 << n)
    opens, closed = p.opens(), p.closed()
    assert topology_test(n, opens)
    recovered = tuple(sum(1 << y for y in range(n)
                          if all(not (u >> x & 1) or (u >> y & 1) for u in opens))
                      for x in range(n))
    assert recovered == p.rows
    for a in subsets:
        i, c = p.interior(a), p.closure(a)
        assert i & ~a == 0 and a & ~c == 0
        assert p.is_open(i) and full ^ c in opens
        assert p.interior(i) == i and p.closure(c) == c
        assert p.interior(full ^ a) == full ^ c
        assert all(u & ~a or u & ~i == 0 for u in opens)
        assert all(a & ~d or c & ~d == 0 for d in closed)
        boundary = c & p.closure(full ^ a)
        exterior = p.interior(full ^ a)
        assert i | exterior | boundary == full
        assert not (i & exterior or i & boundary or exterior & boundary)
        for b in subsets:
            assert p.interior(a & b) == p.interior(a) & p.interior(b)
            assert p.closure(a | b) == p.closure(a) | p.closure(b)
            if a & ~b == 0:
                assert p.interior(a) & ~p.interior(b) == 0
                assert p.closure(a) & ~p.closure(b) == 0
            counts['closure_interior_pairs'] += 1
    comps = p.components()
    for a in subsets:
        clopen = a in opens and a in closed
        union_of_components = all(not (a & c) or a & c == c for c in comps)
        assert clopen == union_of_components
        counts['clopen_subsets'] += 1
    normal = all(a & b or p.upward(a) & p.upward(b) == 0
                 for a in closed for b in closed)
    least_components = all(any(all(p.le(m, x) for x in points(c, n))
                               for m in points(c, n)) for c in comps)
    assert normal == least_components
    counts['normal_spaces'] += int(normal)
    for a in closed:
        sat_a = sum(c for c in comps if c & a)
        assert sat_a in opens and sat_a in closed
        for b in closed:
            if normal and not a & b:
                assert not sat_a & b
                sep = tuple(0 if sat_a >> x & 1 else 1 for x in range(n))
                assert all(sep[x] == 0 for x in points(a, n))
                assert all(sep[x] == 1 for x in points(b, n))
                assert all(not p.le(x, y) or sep[x] == sep[y]
                           for x in range(n) for y in range(n))
                counts['urysohn_separators'] += 1
        if normal:
            aa = points(a, n)
            for vals in itertools.product(range(3), repeat=len(aa)):
                f = dict(zip(aa, vals))
                if any(p.le(x, y) and f[x] != f[y] for x in aa for y in aa):
                    continue
                ext = {}
                for c in comps:
                    ca = points(c & a, n)
                    v = f[ca[0]] if ca else 0
                    for x in points(c, n):
                        ext[x] = v
                assert all(ext[x] == f[x] for x in aa)
                assert all(not p.le(x, y) or ext[x] == ext[y]
                           for x in range(n) for y in range(n))
                counts['tietze_extensions'] += 1
    t1 = all((full ^ (1 << x)) in opens for x in range(n))
    hausdorff = all(x == y or not (p.rows[x] & p.rows[y])
                   for x in range(n) for y in range(n))
    discrete = len(opens) == 1 << n
    assert t1 == hausdorff == discrete
    for x in range(n):
        for y in range(n):
            dxy = 0 if p.le(x, y) else 1
            for z in range(n):
                assert (0 if p.le(x, z) else 1) <= dxy + (0 if p.le(y, z) else 1)
                counts['quasimetric_triangles'] += 1
    # Subspace topology independently compared against all relative open sets.
    for a in subsets:
        aa = points(a, n)
        q = Space(tuple(sum(1 << j for j, y in enumerate(aa) if p.le(x, y))
                        for x in aa))
        rel = {sum(1 << i for i, x in enumerate(aa) if u >> x & 1) for u in opens}
        assert set(q.opens()) == rel
        counts['subspaces'] += 1


def verify_maps(spaces, counts):
    for n in range(min(3, max(spaces)) + 1):
        for m in range(min(3, max(spaces)) + 1):
            for p in spaces[n]:
                for q in spaces[m]:
                    for f in itertools.product(range(m), repeat=n):
                        hm = monotone(p, q, f)
                        assert hm == continuous(p, q, f)
                        closure_condition = all(
                            image(f, p.closure(a)) & ~q.closure(image(f, a)) == 0
                            for a in range(1 << n))
                        assert hm == closure_condition
                        counts['maps'] += 1


def verify_quotients(spaces, counts):
    for n in range(min(3, max(spaces)) + 1):
        for p in spaces[n]:
            for m in range(n + 1):
                for f in itertools.product(range(m), repeat=n):
                    if set(f) != set(range(m)):
                        continue
                    rows = [1 << a for a in range(m)]
                    for x in range(n):
                        for y in range(n):
                            if p.le(x, y):
                                rows[f[x]] |= 1 << f[y]
                    for k in range(m):
                        for x in range(m):
                            if rows[x] >> k & 1:
                                rows[x] |= rows[k]
                    q = Space(tuple(rows))
                    quotient_opens = {u for u in range(1 << m)
                                      if p.is_open(preimage(f, u))}
                    assert set(q.opens()) == quotient_opens
                    counts['quotients'] += 1


def verify_exponentials(spaces, counts):
    for n in range(min(2, max(spaces)) + 1):
        for m in range(min(2, max(spaces)) + 1):
            for p in spaces[n]:
                for q in spaces[m]:
                    maps = tuple(f for f in itertools.product(range(m), repeat=n)
                                 if monotone(p, q, f))
                    e = Space(tuple(sum(1 << j for j, g in enumerate(maps)
                                        if all(q.le(f[x], g[x]) for x in range(n)))
                                    for f in maps))
                    generators = []
                    for k in range(1 << n):
                        for u in q.opens():
                            generators.append(sum(1 << i for i, f in enumerate(maps)
                                                  if image(f, k) & ~u == 0))
                    generated = {0, e.full, *generators}
                    for _ in range(1 << len(maps)):
                        old = set(generated)
                        generated |= {a & b for a in old for b in old}
                        generated |= {a | b for a in old for b in old}
                        if generated == old:
                            break
                    assert generated == set(e.opens())
                    for i, f in enumerate(maps):
                        for j, g in enumerate(maps):
                            for x in range(n):
                                for y in range(n):
                                    if e.le(i, j) and p.le(x, y):
                                        assert q.le(f[x], g[y])
                    counts['exponentials'] += 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=4, choices=range(5))
    args = parser.parse_args()
    spaces = {n: tuple(preorders(n)) for n in range(args.max_n + 1)}
    counts = {k: 0 for k in ('closure_interior_pairs', 'clopen_subsets',
                             'normal_spaces', 'urysohn_separators',
                             'tietze_extensions', 'quasimetric_triangles',
                             'subspaces', 'maps', 'quotients', 'exponentials')}
    for ss in spaces.values():
        for p in ss:
            verify_space(p, counts)
    # Independently enumerate topology tables for n <= 3.
    topology_counts = {}
    for n in range(min(3, args.max_n) + 1):
        families = []
        for raw in range(1 << (1 << n)):
            fam = {a for a in range(1 << n) if raw >> a & 1}
            if topology_test(n, fam):
                families.append(frozenset(fam))
        assert set(families) == {frozenset(p.opens()) for p in spaces[n]}
        topology_counts[str(n)] = len(families)
    verify_maps(spaces, counts)
    verify_quotients(spaces, counts)
    verify_exponentials(spaces, counts)
    print(json.dumps({
        'status': 'all assertions passed',
        'scope': 'Exhaustive finite-model validation; not a universal proof or iPRA proof checker.',
        'max_carrier_size': args.max_n,
        'preorder_counts': {str(n): len(ss) for n, ss in spaces.items()},
        'independent_topology_counts': topology_counts,
        'checks': counts,
        'map_carrier_bound': min(3, args.max_n),
        'exponential_carrier_bound': min(2, args.max_n)
    }, indent=2))


if __name__ == '__main__':
    main()
