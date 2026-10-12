"""Small explicit and analytically certified huge test oracles. MIT-0.

Neither test oracle is a replacement for general AHT interval reduction.
"""
from __future__ import annotations
from bisect import bisect_right
from .surfaces import DSU


class ExplicitOracle:
    def __init__(self, n: int, edges):
        self.n = n
        dsu = DSU(n)
        for x, y in edges:
            dsu.union(x, y)
        self.labels = tuple(dsu.find(i) for i in range(n))
        self.base = len(set(self.labels))

    def __call__(self, extra=()):
        touched = sorted({self.labels[x] for pair in extra for x in pair})
        index = {x: i for i, x in enumerate(touched)}
        dsu = DSU(len(touched))
        decrement = 0
        for x, y in extra:
            a, b = index[self.labels[x]], index[self.labels[y]]
            if dsu.find(a) != dsu.find(b):
                decrement += 1
                dsu.union(a, b)
        return self.base - decrement


class BlockOracle:
    """Equivalence classes are consecutive integer blocks plus singleton tail.

    Block endpoints and the universe may have arbitrarily many bits. The
    count uses only binary searches on the supplied block list and finite DSU.
    This exact analytic oracle tests enormous path subdivisions without expansion.
    """
    def __init__(self, blocks: list[tuple[int, int]], singleton_tail: int = 0):
        if singleton_tail < 0:
            raise ValueError('invalid tail')
        self.blocks = tuple(blocks)
        self.starts = tuple(a for a, b in blocks)
        previous = 0
        for a, b in blocks:
            if a != previous or b <= a:
                raise ValueError('blocks must partition an initial interval')
            previous = b
        self.end, self.n = previous, previous + singleton_tail
        self.base = len(blocks) + singleton_tail

    def label(self, x: int):
        if not 0 <= x < self.n:
            raise ValueError('outside universe')
        if x >= self.end:
            return len(self.blocks) + x-self.end
        return bisect_right(self.starts, x)-1

    def __call__(self, extra=()):
        labels = {self.label(x) for pair in extra for x in pair}
        index = {x: i for i, x in enumerate(sorted(labels))}
        dsu = DSU(len(index))
        decrement = 0
        for x, y in extra:
            a, b = index[self.label(x)], index[self.label(y)]
            if dsu.find(a) != dsu.find(b):
                decrement += 1
                dsu.union(a, b)
        return self.base - decrement


class SingletonOracle:
    def __init__(self, n: int):
        self.n = n

    def __call__(self, extra=()):
        values = sorted({x for pair in extra for x in pair})
        if values and not 0 <= values[0] <= values[-1] < self.n:
            raise ValueError('outside universe')
        index = {x: i for i, x in enumerate(values)}
        dsu = DSU(len(values))
        decrement = 0
        for x, y in extra:
            a, b = index[x], index[y]
            if dsu.find(a) != dsu.find(b):
                decrement += 1
                dsu.union(a, b)
        return self.n-decrement
