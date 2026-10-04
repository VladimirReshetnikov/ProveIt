"""Validated classical one-component knot diagrams.

PD convention: a crossing is ``[a, b, c, d]`` in counterclockwise order with the
under-strand joining ``a`` to ``c`` and the over-strand joining ``b`` to ``d``.
Every edge label occurs exactly twice.  ``{"pd": []}`` is one crossing-free
circle.  Braid closures and rectangular (grid) diagrams are converted to PD
codes; grids use the convention of archive 01 (rows bottom to top, verticals
pass over horizontals).
"""
from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Any, Iterable, Sequence


class DiagramError(ValueError):
    """The data do not describe a classical one-component knot diagram."""


class DisjointSet:
    def __init__(self, n: int):
        self.parent = list(range(n))

    def find(self, x: int) -> int:
        root = x
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[x] != root:
            self.parent[x], x = root, self.parent[x]
        return root

    def union(self, a: int, b: int) -> None:
        a, b = self.find(a), self.find(b)
        if a != b:
            self.parent[a] = b


def cycles(permutation: Sequence[int]) -> list[tuple[int, ...]]:
    seen: set[int] = set()
    result = []
    for start in range(len(permutation)):
        if start in seen:
            continue
        cycle, x = [], start
        while x not in seen:
            seen.add(x)
            cycle.append(x)
            x = permutation[x]
        result.append(tuple(cycle))
    return result


@dataclass(frozen=True)
class Diagram:
    """A normalized PD code (labels 0..2n-1) with cached face and strand data."""
    pd: tuple[tuple[int, int, int, int], ...]

    @property
    def crossings(self) -> int:
        return len(self.pd)

    @classmethod
    def from_pd(cls, data: Iterable[Iterable[int]]) -> "Diagram":
        try:
            rows = [tuple(row) for row in data]
        except TypeError as exc:
            raise DiagramError("PD must be a list of four-integer crossings") from exc
        for row in rows:
            if len(row) != 4 or any(type(x) is not int for x in row):
                raise DiagramError("each crossing must be four integer edge labels")
        if not rows:
            return cls(())
        counts = Counter(x for row in rows for x in row)
        if any(c != 2 for c in counts.values()):
            raise DiagramError("every edge label must occur exactly twice")
        relabel = {label: i for i, label in enumerate(sorted(counts))}
        pd = tuple(tuple(relabel[x] for x in row) for row in rows)
        n = len(pd)
        # darts 4i+j; alpha pairs the two darts of an edge
        where: dict[int, list[int]] = defaultdict(list)
        for i, row in enumerate(pd):
            for j, e in enumerate(row):
                where[e].append(4 * i + j)
        alpha = [0] * (4 * n)
        for a, b in where.values():
            alpha[a], alpha[b] = b, a
        strands = DisjointSet(4 * n)
        for a, b in where.values():
            strands.union(a, b)
        for i in range(n):
            strands.union(4 * i, 4 * i + 2)
            strands.union(4 * i + 1, 4 * i + 3)
        if len({strands.find(d) for d in range(4 * n)}) != 1:
            raise DiagramError("the diagram must have exactly one component")
        faces = cycles([4 * (alpha[d] // 4) + (alpha[d] + 1) % 4 for d in range(4 * n)])
        if len(faces) != n + 2:
            raise DiagramError("the rotation system is not spherical (virtual diagram)")
        return cls(pd)

    @classmethod
    def from_braid(cls, strands: int, word: Iterable[int]) -> "Diagram":
        """Closure of an Artin braid; generator +i puts strand i over strand i+1."""
        word = list(word)
        if type(strands) is not int or strands < 1:
            raise DiagramError("strands must be a positive integer")
        if any(type(g) is not int or not 1 <= abs(g) < strands for g in word):
            raise DiagramError("braid generators must satisfy 1 <= |g| < strands")
        if strands > len(word) + 1:
            raise DiagramError("too few crossings for a one-component closure")
        permutation = list(range(strands))
        for g in word:
            i = abs(g) - 1
            permutation[i], permutation[i + 1] = permutation[i + 1], permutation[i]
        if len(cycles(permutation)) != 1:
            raise DiagramError("the braid closure is a link, not a knot")
        if not word:
            return cls(())
        current = list(range(strands))
        next_label = strands
        rows = []
        for g in word:
            i = abs(g) - 1
            left, right = current[i], current[i + 1]
            out_left, out_right = next_label, next_label + 1
            next_label += 2
            rows.append((right, left, out_left, out_right) if g > 0
                        else (left, out_left, out_right, right))
            current[i], current[i + 1] = out_left, out_right
        closure = DisjointSet(next_label)
        for top, bottom in enumerate(current):
            closure.union(top, bottom)
        return cls.from_pd([[closure.find(x) for x in row] for row in rows])

    @classmethod
    def from_grid(cls, rows: Sequence[Sequence[int]]) -> "Diagram":
        """Rectangular diagram: two marked columns per row (rows bottom to top)."""
        rows = [tuple(sorted(r)) for r in rows]
        n = len(rows)
        if n < 2 or any(len(r) != 2 or r[0] == r[1] or not 0 <= r[0] < n or not 0 <= r[1] < n
                        for r in rows):
            raise DiagramError("a grid needs two distinct column indices in each row")
        cols: list[list[int]] = [[] for _ in range(n)]
        for r, (a, b) in enumerate(rows):
            cols[a].append(r)
            cols[b].append(r)
        if any(len(c) != 2 for c in cols):
            raise DiagramError("every column must contain exactly two corners")
        crossing_id: dict[tuple[int, int], int] = {}
        events = []
        r, c = 0, rows[0][0]
        start = (r, c)
        visited = 0
        while True:
            a, b = rows[r]
            d = b if c == a else a
            dx = 1 if d > c else -1
            for col in range(c + dx, d, dx):
                lo, hi = cols[col]
                if lo < r < hi:
                    key = (r, col)
                    crossing_id.setdefault(key, len(crossing_id))
                    events.append((crossing_id[key], False, dx))
            c = d
            lo, hi = cols[c]
            s = hi if r == lo else lo
            dy = 1 if s > r else -1
            for row in range(r + dy, s, dy):
                a2, b2 = rows[row]
                if a2 < c < b2:
                    key = (row, c)
                    crossing_id.setdefault(key, len(crossing_id))
                    events.append((crossing_id[key], True, dy))
            r = s
            visited += 1
            if (r, c) == start:
                break
        if visited != n:
            raise DiagramError("the grid has more than one component")
        m = len(events)
        if m == 0:
            return cls(())
        info: dict[int, dict[str, tuple[int, int, int]]] = {}
        for k, (cid, over, direction) in enumerate(events):
            info.setdefault(cid, {})['over' if over else 'under'] = ((k - 1) % m, k, direction)
        pd = []
        for cid in range(len(crossing_id)):
            u_in, u_out, dx = info[cid]['under']
            o_in, o_out, dy = info[cid]['over']
            south = o_in if dy == 1 else o_out
            north = o_out if dy == 1 else o_in
            pd.append([u_in, south, u_out, north] if dx == 1 else [u_in, north, u_out, south])
        return cls.from_pd(pd)

    @classmethod
    def from_json(cls, value: Any) -> "Diagram":
        if isinstance(value, list):
            return cls.from_pd(value)
        if not isinstance(value, dict):
            raise DiagramError("input must be a JSON object or a PD array")
        keys = [k for k in ("pd", "braid", "rows", "x") if k in value]
        if len(keys) != 1:
            raise DiagramError("specify exactly one of pd, braid, rows, or x/o")
        key = keys[0]
        if key == "pd":
            return cls.from_pd(value["pd"])
        if key == "braid":
            braid = value["braid"]
            if not isinstance(braid, dict) or "strands" not in braid or "word" not in braid:
                raise DiagramError("braid must have strands and word")
            return cls.from_braid(braid["strands"], braid["word"])
        if key == "rows":
            return cls.from_grid(value["rows"])
        x, o = value["x"], value.get("o")
        if not isinstance(x, list) or not isinstance(o, list) or len(x) != len(o):
            raise DiagramError("x and o must be equal-length arrays")
        return cls.from_grid(list(zip(x, o)))

    # ----- derived data -------------------------------------------------
    def alpha(self) -> list[int]:
        n = self.crossings
        where: dict[int, list[int]] = defaultdict(list)
        for i, row in enumerate(self.pd):
            for j, e in enumerate(row):
                where[e].append(4 * i + j)
        alpha = [0] * (4 * n)
        for a, b in where.values():
            alpha[a], alpha[b] = b, a
        return alpha

    def faces(self) -> list[tuple[int, ...]]:
        alpha = self.alpha()
        return cycles([4 * (alpha[d] // 4) + (alpha[d] + 1) % 4 for d in range(4 * self.crossings)])

    def traversal(self) -> list[int]:
        """Incoming darts of an oriented traversal starting on the under-port of crossing 0."""
        if not self.pd:
            return []
        alpha = self.alpha()
        walk, current = [], 0
        for _ in range(2 * self.crossings):
            walk.append(current)
            opposite = 4 * (current // 4) + (current + 2) % 4
            current = alpha[opposite]
        if current != 0:
            raise DiagramError("internal traversal error")
        return walk

    def signs(self) -> list[int]:
        """Oriented crossing signs, using BOTH incoming strand directions."""
        over, under = {}, {}
        for dart in self.traversal():
            (over if dart % 2 else under)[dart // 4] = dart % 4
        return [1 if (over[i] - under[i]) % 4 == 3 else -1
                for i in range(self.crossings)]

    def writhe(self) -> int:
        return sum(self.signs())

    def mirror(self) -> "Diagram":
        return Diagram.from_pd([row[1:] + row[:1] for row in self.pd])

    def to_json(self) -> dict[str, Any]:
        return {"pd": [list(row) for row in self.pd]}
