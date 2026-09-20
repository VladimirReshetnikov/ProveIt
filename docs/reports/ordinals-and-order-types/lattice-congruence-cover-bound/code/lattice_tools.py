#!/usr/bin/env python3
"""Exact finite-lattice tools. Python standard library only.

A natural labelling respects the order. A lattice is encoded by the bitmask
of the principal downset of each vertex. No external lattice database is used.
"""
from __future__ import annotations
from collections.abc import Iterator, Iterable
from dataclasses import dataclass


def bits(mask: int) -> Iterator[int]:
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def natural_posets(n: int) -> Iterator[tuple[int, ...]]:
    """Each partial order compatible with 0<1<...<n-1, exactly once."""
    if n < 0:
        raise ValueError('n must be nonnegative')
    def extend(down: tuple[int, ...]) -> Iterator[tuple[int, ...]]:
        m = len(down)
        if m == n:
            yield down
            return
        for ideal in range(1 << m):
            if all(down[x] & ~ideal == 0 for x in bits(ideal)):
                yield from extend(down + (ideal | (1 << m),))
    yield from extend(())


@dataclass
class Lattice:
    down: tuple[int, ...]
    up: tuple[int, ...]
    meet: tuple[tuple[int, ...], ...]
    join: tuple[tuple[int, ...], ...]
    lower: tuple[tuple[int, ...], ...]
    upper: tuple[tuple[int, ...], ...]

    @property
    def n(self) -> int:
        return len(self.down)

    @property
    def ji(self) -> tuple[int, ...]:
        return tuple(x for x in range(self.n) if len(self.lower[x]) == 1)

    @property
    def jr(self) -> tuple[int, ...]:
        return tuple(x for x in range(self.n) if len(self.lower[x]) >= 2)

    @property
    def mr(self) -> tuple[int, ...]:
        return tuple(x for x in range(self.n) if len(self.upper[x]) >= 2)

    @property
    def skeleton(self) -> set[int]:
        ans = set(self.jr) | set(self.mr)
        for x in self.jr:
            ans.update(self.lower[x])
        for x in self.mr:
            ans.update(self.upper[x])
        return ans


def from_downsets(down: tuple[int, ...]) -> Lattice | None:
    """Return a lattice, or None if the supplied natural poset is not one."""
    n = len(down)
    if n == 0:
        return None
    if any(down[x] & (1 << x) == 0 for x in range(n)):
        raise ValueError('Downsets must contain their vertices.')
    if any(down[x] >> (x + 1) for x in range(n)):
        raise ValueError('The labelling must be natural.')
    if any(down[y] & ~down[x] for x in range(n) for y in bits(down[x])):
        raise ValueError('The relation must be transitive.')
    up = tuple(sum(1 << y for y in range(n) if down[y] & (1 << x))
               for x in range(n))
    meet = [[0]*n for _ in range(n)]
    join = [[0]*n for _ in range(n)]
    for x in range(n):
        for y in range(x, n):
            common = down[x] & down[y]
            if not common:
                return None
            m = common.bit_length() - 1
            if down[m] != common:
                return None
            common_up = up[x] & up[y]
            if not common_up:
                return None
            j = (common_up & -common_up).bit_length() - 1
            if up[j] != common_up:
                return None
            meet[x][y] = meet[y][x] = m
            join[x][y] = join[y][x] = j
    lower = []
    for x in range(n):
        strict = down[x] ^ (1 << x)
        lower.append(tuple(y for y in bits(strict)
                           if up[y] & strict == 1 << y))
    upper = tuple(tuple(x for x in range(n) if y in lower[x]) for y in range(n))
    return Lattice(down, up, tuple(map(tuple, meet)), tuple(map(tuple, join)),
                   tuple(lower), upper)


def bounded_lattices(n: int) -> Iterator[tuple[Lattice, int]]:
    """Enumerate naturally labelled lattices; second output is poset index."""
    if n < 1:
        raise ValueError('n must be positive')
    if n == 1:
        yield from_downsets((1,)), 0
        return
    for index, interior in enumerate(natural_posets(n - 2)):
        down = (1,) + tuple((mask << 1) | 1 for mask in interior) + ((1 << n) - 1,)
        L = from_downsets(down)
        if L is not None:
            yield L, index


def from_edges(n: int, edges: Iterable[tuple[int, int]]) -> Lattice:
    """Edges may include non-cover comparabilities; labels must be natural."""
    down = [1 << x for x in range(n)]
    for x, y in edges:
        if not 0 <= x < y < n:
            raise ValueError('Require 0 <= x < y < n')
        down[y] |= 1 << x
    for y in range(n):
        for x in list(bits(down[y])):
            down[y] |= down[x]
    L = from_downsets(tuple(down))
    if L is None:
        raise ValueError('The supplied order is not a lattice.')
    return L


class UnionFind:
    def __init__(self, n: int):
        self.parent = list(range(n))

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def merge(self, x: int, y: int) -> bool:
        x, y = self.find(x), self.find(y)
        if x == y:
            return False
        if x > y:
            x, y = y, x
        self.parent[y] = x
        return True

    def partition(self) -> tuple[int, ...]:
        return tuple(self.find(x) for x in range(len(self.parent)))


def principal_congruence(L: Lattice, a: int, b: int) -> tuple[int, ...]:
    """Least compatible equivalence relation identifying a and b."""
    U = UnionFind(L.n)
    U.merge(a, b)
    changed = True
    while changed:
        changed = False
        for x in range(L.n):
            for y in range(x):
                if U.find(x) == U.find(y):
                    for z in range(L.n):
                        changed |= U.merge(L.meet[x][z], L.meet[y][z])
                        changed |= U.merge(L.join[x][z], L.join[y][z])
    return U.partition()


def partition_join(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    """Equivalence closure of a union. For congruences, this is their join."""
    U = UnionFind(len(a))
    for x in range(len(a)):
        U.merge(x, a[x])
        U.merge(x, b[x])
    return U.partition()


def principal_labels(L: Lattice) -> dict[int, tuple[int, ...]]:
    return {j: principal_congruence(L, L.lower[j][0], j) for j in L.ji}


def all_congruences(L: Lattice, labels=None) -> set[tuple[int, ...]]:
    """Enumerate joins of principal labels, without distributivity assumptions."""
    if labels is None:
        labels = principal_labels(L)
    found = {tuple(range(L.n))}
    for theta in sorted(set(labels.values())):
        found |= {partition_join(phi, theta) for phi in tuple(found)}
    return found


def all_partitions(n: int) -> Iterator[tuple[int, ...]]:
    """Restricted-growth enumeration, canonicalized to least block members."""
    if n < 0:
        raise ValueError('n must be nonnegative')
    if n == 0:
        yield ()
        return
    def extend(p: tuple[int, ...], reps: tuple[int, ...]):
        if len(p) == n:
            yield p
            return
        for r in reps:
            yield from extend(p + (r,), reps)
        r = len(p)
        yield from extend(p + (r,), reps + (r,))
    yield from extend((0,), (0,))


def is_congruence(L: Lattice, p: tuple[int, ...]) -> bool:
    """Direct compatibility check, independent of principal-label generation."""
    for x in range(L.n):
        for y in range(x):
            if p[x] == p[y]:
                for z in range(L.n):
                    if (p[L.meet[x][z]] != p[L.meet[y][z]] or
                        p[L.join[x][z]] != p[L.join[y][z]]):
                        return False
    return True


def partition_le(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
    return all(b[x] == b[a[x]] for x in range(len(a)))


def is_chain_glued_Mk(L: Lattice, u: int, k: int) -> bool:
    """Recognize exactly C_s glued M_k glued C_t at the designated u."""
    atoms = L.upper[u]
    if len(atoms) != k:
        return False
    v = L.join[atoms[0]][atoms[1]]
    middle = {u, v, *atoms}
    for x in range(L.n):
        if x in middle:
            continue
        if not (L.down[u] & (1 << x) or L.up[v] & (1 << x)):
            return False
    low, high = list(bits(L.down[u])), list(bits(L.up[v]))
    for side in (low, high):
        if any(not ((L.down[x] & (1 << y)) or (L.down[y] & (1 << x)))
               for x in side for y in side):
            return False
    return all(L.join[x][y] == v for x in atoms for y in atoms if x != y)
