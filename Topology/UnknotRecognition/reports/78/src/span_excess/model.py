"""Validated finite height systems and balanced minimum-span witnesses.

No class in this module authenticates a 3-manifold or a knot diagram.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Callable, Sequence

Check = Callable[[], None]
Constraint = tuple[int, int, int]  # p[v] - p[u] <= bound
Edge = tuple[int, int, int, int]  # u, v, cocycle offset, nonnegative weight


def integer(x: object) -> int:
    if type(x) is not int:
        raise ValueError("expected an integer, not a float or boolean")
    return x


def noop() -> None:
    pass


class WorkLimit(RuntimeError):
    """A local computation is unfinished, never a negative knot verdict."""


class Budget:
    def __init__(self, limit: int | None = None, check: Check = noop):
        if limit is not None and integer(limit) < 0:
            raise ValueError("negative work allowance")
        self.limit, self.check, self.work = limit, check, 0

    def tick(self) -> None:
        self.check()
        self.work += 1
        if self.limit is not None and self.work > self.limit:
            raise WorkLimit("span-excess work allowance exhausted")


@dataclass(frozen=True)
class HeightModel:
    n: int
    vertices: tuple[tuple[int, int, int, int], ...]
    heights: tuple[tuple[int, int, int, int], ...]
    low: tuple[int, ...]
    high: tuple[int, ...]
    optimum: int
    initial: tuple[int, ...]
    edges: tuple[Edge, ...] = ()

    def validate(self) -> None:
        if integer(self.n) < 1 or not self.vertices:
            raise ValueError("nonempty height model required")
        t = len(self.vertices)
        if not (len(self.heights) == len(self.low) == len(self.high) == t):
            raise ValueError("tetrahedron array length mismatch")
        if len(self.initial) != self.n:
            raise ValueError("potential length mismatch")
        for x in self.initial:
            integer(x)
        integer(self.optimum)
        balance = [0] * self.n
        dual = 0
        used = set()
        for vs, hs, lo, hi in zip(self.vertices, self.heights, self.low, self.high):
            if len(vs) != 4 or len(hs) != 4:
                raise ValueError("exactly four corners required")
            for v in vs:
                if not 0 <= integer(v) < self.n:
                    raise ValueError("vertex index out of range")
                used.add(v)
            for h in hs:
                integer(h)
            if not 0 <= integer(lo) < 4 or not 0 <= integer(hi) < 4:
                raise ValueError("anchor out of range")
            balance[vs[hi]] += 1
            balance[vs[lo]] -= 1
            dual += hs[hi] - hs[lo]
        if used != set(range(self.n)):
            raise ValueError("unreferenced global vertex")
        if any(balance) or dual != self.optimum:
            raise ValueError("unbalanced or incorrect minimum-span dual")
        if self.span(self.initial) != self.optimum:
            raise ValueError("initial primal does not attain the dual")
        for u, v, c, w in self.edges:
            if not (0 <= integer(u) < self.n and 0 <= integer(v) < self.n):
                raise ValueError("objective vertex out of range")
            integer(c)
            if integer(w) < 0:
                raise ValueError("negative Euler edge weight is unsupported")

    def adjusted(self, p: Sequence[int]) -> list[tuple[int, ...]]:
        return [tuple(h + p[v] for v, h in zip(vs, hs))
                for vs, hs in zip(self.vertices, self.heights)]

    def span(self, p: Sequence[int]) -> int:
        return sum(max(a) - min(a) for a in self.adjusted(p))

    def defects(self, p: Sequence[int]) -> tuple[int, ...]:
        ans = []
        for a, lo, hi in zip(self.adjusted(p), self.low, self.high):
            ans.extend((max(a) - a[hi], a[lo] - min(a)))
        return tuple(ans)

    def objective(self, p: Sequence[int]) -> int:
        return sum(w * abs(c + p[v] - p[u]) for u, v, c, w in self.edges)

    def score2(self, p: Sequence[int]) -> int:
        """Equals twice Euler characteristic ONLY for a validated geometric model."""
        return 2 * self.span(p) - self.objective(p)

    def to_dict(self) -> dict:
        from dataclasses import asdict
        return asdict(self)

    @classmethod
    def from_dict(cls, data: dict) -> 'HeightModel':
        keys = {'n', 'vertices', 'heights', 'low', 'high', 'optimum', 'initial', 'edges'}
        if set(data) != keys:
            raise ValueError("unexpected model fields")
        obj = cls(data['n'], tuple(map(tuple, data['vertices'])),
                  tuple(map(tuple, data['heights'])), tuple(data['low']),
                  tuple(data['high']), data['optimum'], tuple(data['initial']),
                  tuple(map(tuple, data['edges'])))
        obj.validate()
        return obj
