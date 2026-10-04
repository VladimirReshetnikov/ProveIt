"""Validated classical one-component planar diagrams and braid closures.

A crossing is four edge labels in cyclic order. Slots 0 and 2 are the
underpassing strand; slots 1 and 3 are the overpassing strand. Labels need
not be consecutive. Empty PD is defined to mean ONE crossing-free circle.
No implicit extra crossing-free components are allowed.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Iterable


class InvalidDiagram(ValueError):
    """The supplied data are not a supported classical knot diagram."""


class UnionFind:
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, x: int) -> int:
        while x != self.parent[x]:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a: int, b: int) -> None:
        a, b = self.find(a), self.find(b)
        if a == b:
            return
        if self.size[a] < self.size[b]:
            a, b = b, a
        self.parent[b] = a
        self.size[a] += self.size[b]


def permutation_cycles(p: list[int]) -> list[tuple[int, ...]]:
    seen: set[int] = set()
    cycles = []
    for start in range(len(p)):
        if start in seen:
            continue
        cycle, cur = [], start
        while cur not in seen:
            seen.add(cur)
            cycle.append(cur)
            cur = p[cur]
        if cur != start:
            raise ValueError("Not a permutation")
        cycles.append(tuple(cycle))
    return cycles


@dataclass(frozen=True)
class PlanarDiagram:
    """Use from_pd/from_braid to construct; internal labels are dense, zero-based."""

    crossings: tuple[tuple[int, int, int, int], ...]
    labels: tuple[int, ...]
    faces: int

    @property
    def n(self) -> int:
        return len(self.crossings)

    @classmethod
    def from_pd(cls, data: object) -> PlanarDiagram:
        if not isinstance(data, (list, tuple)):
            raise InvalidDiagram("PD must be a list of four-element crossings")
        rows = []
        for row in data:
            if not isinstance(row, (list, tuple)) or len(row) != 4:
                raise InvalidDiagram("Each crossing must have exactly four labels")
            if any(type(x) is not int for x in row):
                raise InvalidDiagram("Edge labels must be integers, not booleans")
            rows.append(tuple(row))
        if not rows:
            return cls((), (), 2)
        counts = Counter(x for row in rows for x in row)
        if any(count != 2 for count in counts.values()):
            raise InvalidDiagram("Each edge label must occur exactly twice")
        labels = tuple(sorted(counts))
        dense = {label: i for i, label in enumerate(labels)}
        rows = [tuple(dense[x] for x in row) for row in rows]
        n = len(rows)
        occurrences: dict[int, list[int]] = defaultdict(list)
        for i, row in enumerate(rows):
            for j, edge in enumerate(row):
                occurrences[edge].append(4 * i + j)
        alpha = [0] * (4 * n)
        projection = UnionFind(n)
        for darts in occurrences.values():
            a, b = darts
            alpha[a], alpha[b] = b, a
            projection.union(a // 4, b // 4)
        if len({projection.find(i) for i in range(n)}) != 1:
            raise InvalidDiagram("Disconnected projection; only knots are supported")
        rho = [4 * (d // 4) + (d + 1) % 4 for d in range(4 * n)]
        faces = len(permutation_cycles([rho[alpha[d]] for d in range(4 * n)]))
        if faces != n + 2:
            raise InvalidDiagram("Rotation system is not a sphere embedding (virtual PD)")
        strands = UnionFind(2 * n)
        for a, b, c, d in rows:
            strands.union(a, c)
            strands.union(b, d)
        components = len({strands.find(i) for i in range(2 * n)})
        if components != 1:
            raise InvalidDiagram(f"Expected one knot component; found {components}")
        return cls(tuple(rows), labels, faces)

    @classmethod
    def from_braid(cls, strands: int, word: Iterable[int]) -> PlanarDiagram:
        if type(strands) is not int or strands < 1:
            raise InvalidDiagram("Braid strand count must be a positive integer")
        try:
            word = tuple(word)
        except TypeError as exc:
            raise InvalidDiagram("Braid word must be an integer sequence") from exc
        if any(type(g) is not int or not 1 <= abs(g) < strands for g in word):
            raise InvalidDiagram("Generator indices must satisfy 1 <= |g| < strands")
        # A transposition word for a single cycle needs at least strands-1
        # letters. Reject before allocating arrays for an enormous strand count.
        if len(word) < strands - 1:
            raise InvalidDiagram("Braid word is too short for a one-component closure")
        permutation = list(range(strands))
        for g in word:
            i = abs(g) - 1
            permutation[i], permutation[i + 1] = permutation[i + 1], permutation[i]
        if len(permutation_cycles(permutation)) != 1:
            raise InvalidDiagram("Braid closure has more than one component")
        if not word:
            return cls.from_pd([])  # Only strands=1 can reach here.
        wires = UnionFind(strands + 2 * len(word))
        current = list(range(strands))
        next_label = strands
        rows = []
        for g in word:
            i = abs(g) - 1
            top_left, top_right = current[i], current[i + 1]
            bottom_left, bottom_right = next_label, next_label + 1
            next_label += 2
            if g > 0:  # Left input passes over the right input.
                rows.append((top_right, top_left, bottom_left, bottom_right))
            else:
                rows.append((top_left, bottom_left, bottom_right, top_right))
            current[i], current[i + 1] = bottom_left, bottom_right
        for i, end in enumerate(current):
            wires.union(i, end)
        return cls.from_pd([[wires.find(e) for e in row] for row in rows])

    @classmethod
    def from_json(cls, obj: object) -> PlanarDiagram:
        if isinstance(obj, (list, tuple)):
            return cls.from_pd(obj)
        if not isinstance(obj, dict):
            raise InvalidDiagram("Input must be a PD list or an object with pd or braid")
        if ("pd" in obj) == ("braid" in obj):
            raise InvalidDiagram("Specify exactly one of pd and braid")
        if "pd" in obj:
            return cls.from_pd(obj["pd"])
        braid = obj["braid"]
        if not isinstance(braid, dict) or set(braid) != {"strands", "word"}:
            raise InvalidDiagram("braid must have exactly strands and word fields")
        return cls.from_braid(braid["strands"], braid["word"])

    def basepoint(self, original_label: int | None = None) -> int:
        if original_label is None:
            return 0
        if type(original_label) is not int:
            raise InvalidDiagram("Basepoint edge must be an integer label")
        try:
            return self.labels.index(original_label)
        except ValueError as exc:
            raise InvalidDiagram("Basepoint edge does not occur in the diagram") from exc

    def to_pd(self) -> list[list[int]]:
        return [[self.labels[e] for e in row] for row in self.crossings]
