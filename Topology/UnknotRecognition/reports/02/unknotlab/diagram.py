"""Classical knot diagrams in PD notation; no external dependencies.

Each crossing is a cyclic (counterclockwise) tuple (a,b,c,d), with the
underpass joining a to c and the overpass joining b to d. Arc labels may
be arbitrary positive integers; every label must occur twice. Empty PD
means exactly one crossing-free circle. Hidden crossing-free components
are not expressible in this input format.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Iterable


class InvalidDiagram(ValueError):
    """The input is not a one-component classical knot diagram."""


class DSU:
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, x: int) -> int:
        while self.parent[x] != x:
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
        current, cycle = start, []
        while current not in seen:
            seen.add(current)
            cycle.append(current)
            current = p[current]
        if current != start:
            raise ValueError("Not a permutation")
        cycles.append(tuple(cycle))
    return cycles


@dataclass(frozen=True)
class Diagram:
    pd: tuple[tuple[int, int, int, int], ...]
    alpha: tuple[int, ...] = field(init=False, repr=False)
    faces: tuple[tuple[int, ...], ...] = field(init=False, repr=False)

    def __post_init__(self) -> None:
        if any(len(c) != 4 for c in self.pd):
            raise InvalidDiagram("Each crossing must contain four arc labels")
        flat = [x for c in self.pd for x in c]
        if any(type(x) is not int or x <= 0 for x in flat):
            raise InvalidDiagram("Arc labels must be positive integers, not booleans")
        labels = {x: i for i, x in enumerate(sorted(set(flat)))}
        pd = tuple(tuple(labels[x] for x in c) for c in self.pd)
        occurrences: dict[int, list[int]] = defaultdict(list)
        for i, c in enumerate(pd):
            for j, x in enumerate(c):
                occurrences[x].append(4 * i + j)
        if any(len(v) != 2 for v in occurrences.values()):
            raise InvalidDiagram("Every arc label must occur exactly twice")
        n = len(pd)
        alpha = [0] * (4 * n)
        components = DSU(4 * n)
        for a, b in occurrences.values():
            alpha[a], alpha[b] = b, a
            components.union(a, b)
        for i in range(n):
            components.union(4 * i, 4 * i + 2)
            components.union(4 * i + 1, 4 * i + 3)
        if n and len({components.find(i) for i in range(4 * n)}) != 1:
            raise InvalidDiagram("Expected one knot component, not a link")
        face_next = [4 * (alpha[d] // 4) + (alpha[d] + 1) % 4
                     for d in range(4 * n)]
        faces = permutation_cycles(face_next)
        # One knot component guarantees a connected projection graph.
        if n and len(faces) != n + 2:
            genus = (n + 2 - len(faces)) // 2
            raise InvalidDiagram(f"Non-planar rotation system (supporting genus {genus})")
        object.__setattr__(self, 'pd', tuple(tuple(x + 1 for x in c) for c in pd))
        object.__setattr__(self, 'alpha', tuple(alpha))
        object.__setattr__(self, 'faces', tuple(faces))

    @classmethod
    def from_pd(cls, data: Iterable[Iterable[int]]) -> Diagram:
        try:
            return cls(tuple(tuple(c) for c in data))
        except (TypeError, AttributeError) as exc:
            raise InvalidDiagram("PD must be a list of four-integer crossings") from exc

    @property
    def crossings(self) -> int:
        return len(self.pd)

    def as_json(self) -> dict:
        return {'pd': [list(c) for c in self.pd]}

    def traverse(self, start: int = 0) -> tuple[int, ...]:
        """Incoming darts in a directed traversal; slots 1,3 are overpasses."""
        if not self.pd:
            return ()
        if not 0 <= start < 4 * self.crossings:
            raise ValueError("Invalid starting dart")
        current, walk = start, []
        for _ in range(2 * self.crossings):
            walk.append(current)
            opposite = 4 * (current // 4) + (current + 2) % 4
            current = self.alpha[opposite]
        if current != start or len(set(walk)) != 2 * self.crossings:
            raise AssertionError("Internal knot traversal error")
        return tuple(walk)

    def descending_start(self) -> int | None:
        """Find a traversal that meets every crossing first on its overpass.

        A witness is sufficient for unknotness; failure proves nothing.
        Both directions and all starting arcs are examined in O(n^2) time.
        """
        if not self.pd:
            return 0
        for start in range(4 * self.crossings):
            seen = set()
            for dart in self.traverse(start):
                crossing = dart // 4
                if crossing not in seen and dart % 2 == 0:
                    break
                seen.add(crossing)
            else:
                return start
        return None


def braid_closure(strands: int, word: Iterable[int]) -> Diagram:
    """Construct the PD of an oriented braid closure, rejecting multi-component links.

    Generator +i has the strand at position i over position i+1.
    The braid is read from top to bottom. This is also a test-data builder.
    """
    word = tuple(word)
    if type(strands) is not int or strands < 1:
        raise ValueError("strands must be a positive integer")
    if any(type(g) is not int or not 1 <= abs(g) < strands for g in word):
        raise ValueError("Braid generator out of range")
    if not word:
        if strands != 1:
            raise InvalidDiagram("The empty multi-strand braid closes to a link")
        return Diagram.from_pd([])
    if strands > len(word) + 1:
        raise InvalidDiagram("Too few crossings to connect all braid strands into one component")
    permutation = list(range(strands))
    for g in word:
        i = abs(g) - 1
        permutation[i], permutation[i + 1] = permutation[i + 1], permutation[i]
    if len(permutation_cycles(permutation)) != 1:
        raise InvalidDiagram("The braid closure has more than one component")
    dsu = DSU(strands + 2 * len(word))
    current = list(range(strands))
    crossings = []
    for k, g in enumerate(word):
        i = abs(g) - 1
        left, right = current[i], current[i + 1]
        out_left, out_right = strands + 2 * k, strands + 2 * k + 1
        if g > 0:
            crossing = (right, left, out_left, out_right)
        else:
            crossing = (left, out_left, out_right, right)
        crossings.append(crossing)
        current[i], current[i + 1] = out_left, out_right
    for i in range(strands):
        dsu.union(current[i], i)
    labels: dict[int, int] = {}
    def label(x: int) -> int:
        root = dsu.find(x)
        if root not in labels:
            labels[root] = len(labels) + 1
        return labels[root]
    return Diagram.from_pd([[label(x) for x in c] for c in crossings])
