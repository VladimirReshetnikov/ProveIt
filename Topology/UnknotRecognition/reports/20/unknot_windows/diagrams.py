"""Validated knot-only PD codes in ProveIt's counterclockwise convention."""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass

class DiagramError(ValueError):
    pass

class DSU:
    def __init__(self, n):
        self.parent = list(range(n))
    def find(self, x):
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x
    def union(self, x, y):
        self.parent[self.find(x)] = self.find(y)

def cycles(p):
    seen, result = set(), []
    for s in range(len(p)):
        if s in seen:
            continue
        row, u = [], s
        while u not in seen:
            seen.add(u); row.append(u); u = p[u]
        result.append(tuple(row))
    return result

@dataclass(frozen=True)
class Diagram:
    pd: tuple
    @property
    def crossings(self):
        return len(self.pd)
    @classmethod
    def from_pd(cls, rows):
        try:
            rows = [tuple(row) for row in rows]
        except TypeError as exc:
            raise DiagramError('PD must be an iterable of rows') from exc
        if any(len(row) != 4 or any(type(x) is not int for x in row) for row in rows):
            raise DiagramError('each crossing needs four integer labels')
        if not rows:
            return cls(())
        where = defaultdict(list)
        for i, row in enumerate(rows):
            for j, label in enumerate(row):
                where[label].append(4 * i + j)
        if any(len(v) != 2 for v in where.values()):
            raise DiagramError('each edge must occur exactly twice')
        labels = {x: i for i, x in enumerate(sorted(where))}
        pd = tuple(tuple(labels[x] for x in row) for row in rows)
        n = len(pd)
        alpha = [0] * (4 * n)
        dsu = DSU(4 * n)
        for a, b in where.values():
            alpha[a], alpha[b] = b, a
            dsu.union(a, b)
        for i in range(n):
            dsu.union(4 * i, 4 * i + 2); dsu.union(4 * i + 1, 4 * i + 3)
        if len({dsu.find(d) for d in range(4 * n)}) != 1:
            raise DiagramError('closure is not a knot')
        faces = cycles([4 * (alpha[d] // 4) + (alpha[d] + 1) % 4 for d in range(4 * n)])
        if len(faces) != n + 2:
            raise DiagramError('rotation system is not spherical')
        return cls(pd)
    @classmethod
    def from_braid(cls, strands, word):
        word = list(word)
        if type(strands) is not int or strands < 1:
            raise DiagramError('strands must be positive')
        if any(type(g) is not int or not 1 <= abs(g) < strands for g in word):
            raise DiagramError('invalid braid generator')
        p = list(range(strands))
        for g in word:
            i = abs(g) - 1
            p[i], p[i + 1] = p[i + 1], p[i]
        if len(cycles(p)) != 1:
            raise DiagramError('closure is not a knot')
        if not word:
            return cls(())
        current, nxt, rows = list(range(strands)), strands, []
        for g in word:
            i = abs(g) - 1
            left, right = current[i:i + 2]
            lo, ro = nxt, nxt + 1
            nxt += 2
            rows.append((right, left, lo, ro) if g > 0 else (left, lo, ro, right))
            current[i:i + 2] = [lo, ro]
        close = DSU(nxt)
        for top, bottom in enumerate(current):
            close.union(top, bottom)
        return cls.from_pd([[close.find(x) for x in row] for row in rows])
    def alpha(self):
        where = defaultdict(list)
        for i, row in enumerate(self.pd):
            for j, e in enumerate(row):
                where[e].append(4 * i + j)
        alpha = [0] * (4 * self.crossings)
        for a, b in where.values():
            alpha[a], alpha[b] = b, a
        return alpha
    def signs(self):
        n = self.crossings
        if not n:
            return []
        alpha, current = self.alpha(), 0
        under, over = [0] * n, [1] * n
        for _ in range(2 * n):
            (over if current % 2 else under)[current // 4] = current % 4
            current = alpha[4 * (current // 4) + (current + 2) % 4]
        if current != 0:
            raise DiagramError('inconsistent traversal')
        return [1 if (o - u) % 4 == 3 else -1 for u, o in zip(under, over)]
    def mirror(self):
        return Diagram.from_pd([row[1:] + row[:1] for row in self.pd])
