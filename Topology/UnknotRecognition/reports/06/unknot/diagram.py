"""Validated, classical, one-component planar diagrams and braid closures.

A crossing is (a,b,c,d), counterclockwise, with (a,c) the understrand.
Labels denote edges, NOT crossings; every label must occur twice.
Empty PD deliberately denotes one crossing-free circle, not the empty link.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from typing import Any, Iterable


def popcount(value: int) -> int:
    """Population count, including compatibility with Python 3.9."""
    return bin(value).count("1")


class DiagramError(ValueError):
    """The input is malformed, nonclassical, or not a knot."""


class DisjointSet:
    def __init__(self, size: int) -> None:
        self.parent = list(range(size))
        self.size = [1] * size

    def find(self, x: int) -> int:
        while x != self.parent[x]:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, x: int, y: int) -> None:
        x, y = self.find(x), self.find(y)
        if x == y:
            return
        if self.size[x] < self.size[y]:
            x, y = y, x
        self.parent[y] = x
        self.size[x] += self.size[y]


def cycles(permutation: list[int]) -> list[tuple[int, ...]]:
    """Disjoint cycles of a validated finite permutation."""
    seen: set[int] = set()
    answer = []
    for first in range(len(permutation)):
        if first in seen:
            continue
        cycle, current = [], first
        while current not in seen:
            seen.add(current)
            cycle.append(current)
            current = permutation[current]
        answer.append(tuple(cycle))
    return answer


@dataclass(frozen=True)
class Diagram:
    """Immutable normalized PD. Construct through from_pd/from_json only.

    Edge zero is the basepoint edge. Validation is repeated by public solvers
    so constructing the dataclass directly cannot bypass their input checks.
    """
    pd: tuple[tuple[int, int, int, int], ...]
    name: str = "unnamed"

    @property
    def crossings(self) -> int:
        return len(self.pd)

    @classmethod
    def from_pd(cls, pd: Iterable[Iterable[int]], *, basepoint: int | None = None,
                name: str = "unnamed") -> Diagram:
        try:
            data = [tuple(crossing) for crossing in pd]
        except TypeError as error:
            raise DiagramError("PD must be a sequence of four-tuples") from error
        if not isinstance(name, str):
            raise DiagramError("name must be a string")
        if not data:
            if basepoint is not None:
                raise DiagramError("A crossing-free diagram has no labeled basepoint edge")
            return cls((), name)
        occurrences: dict[int, list[int]] = defaultdict(list)
        for i, crossing in enumerate(data):
            if len(crossing) != 4:
                raise DiagramError(f"Crossing {i} must have four entries")
            for j, label in enumerate(crossing):
                if type(label) is not int or label < 0:
                    raise DiagramError("Edge labels must be nonnegative integers, not booleans")
                occurrences[label].append(4 * i + j)
        if any(len(darts) != 2 for darts in occurrences.values()):
            raise DiagramError("Each edge label must occur exactly twice")
        labels = sorted(occurrences)
        if basepoint is not None:
            if type(basepoint) is not int or basepoint not in occurrences:
                raise DiagramError("basepoint must name an existing edge")
            labels.remove(basepoint)
            labels.insert(0, basepoint)
        renumber = {edge: i for i, edge in enumerate(labels)}
        normalized = tuple(tuple(renumber[e] for e in c) for c in data)
        components = DisjointSet(len(labels))
        for a, b, c, d in normalized:
            components.union(a, c)
            components.union(b, d)
        count = len({components.find(e) for e in range(len(labels))})
        if count != 1:
            raise DiagramError(f"Expected one knot component; diagram has {count}")
        # A connected rotation system embeds in its associated oriented surface.
        # Euler characteristic two is precisely genus zero. This rejects virtual
        # diagrams rather than applying a classical unknot theorem to them.
        twin = [0] * (4 * len(data))
        for a, b in occurrences.values():
            twin[a], twin[b] = b, a
        face_successor = [4 * (twin[d] // 4) + (twin[d] + 1) % 4
                          for d in range(len(twin))]
        euler = len(data) - len(labels) + len(cycles(face_successor))
        if euler != 2:
            raise DiagramError(f"PD rotation system is not spherical (Euler characteristic {euler})")
        return cls(normalized, name)  # type: ignore[arg-type]

    @classmethod
    def from_json(cls, value: Any) -> Diagram:
        if not isinstance(value, dict):
            raise DiagramError("Input must be a JSON object")
        if ("pd" in value) == ("braid" in value):
            raise DiagramError("Specify exactly one of pd and braid")
        if "components" in value and (type(value["components"]) is not int
                                      or value["components"] != 1):
            raise DiagramError("Only one-component knot inputs are supported")
        name = value.get("name", "unnamed")
        if "pd" in value:
            return cls.from_pd(value["pd"], basepoint=value.get("basepoint"), name=name)
        if "basepoint" in value:
            raise DiagramError("Specify basepoints on PD input, not braid input")
        braid = value["braid"]
        if not isinstance(braid, dict):
            raise DiagramError("braid must contain strands and word")
        return from_braid(braid.get("strands"), braid.get("word"), name=name)

    def to_json(self) -> dict[str, Any]:
        return {"name": self.name, "pd": [list(crossing) for crossing in self.pd]}


def from_braid(strands: int, word: Iterable[int], *, name: str = "braid closure") -> Diagram:
    """Close a downward-oriented braid; positive generator has left over right."""
    if type(strands) is not int or strands < 1:
        raise DiagramError("The braid strand count must be a positive integer")
    try:
        generators = list(word)
    except TypeError as error:
        raise DiagramError("A braid word must be a list of signed generator indices") from error
    for generator in generators:
        if type(generator) is not int or not 1 <= abs(generator) < strands:
            raise DiagramError("Braid generators must satisfy 1 <= abs(i) < strands")
    if not generators:
        if strands == 1:
            return Diagram.from_pd([], name=name)
        raise DiagramError(f"The identity braid closes to {strands} components")
    # The closure components are the cycles of the underlying permutation.
    permutation = list(range(strands))
    for generator in generators:
        i = abs(generator) - 1
        permutation[i], permutation[i + 1] = permutation[i + 1], permutation[i]
    count = len(cycles(permutation))
    if count != 1:
        raise DiagramError(f"Expected one knot component; braid closure has {count}")
    current = list(range(strands))
    next_edge = strands
    pd = []
    for generator in generators:
        i = abs(generator) - 1
        left, right = current[i], current[i + 1]
        out_left, out_right = next_edge, next_edge + 1
        next_edge += 2
        if generator > 0:
            pd.append((right, left, out_left, out_right))
        else:
            pd.append((left, out_left, out_right, right))
        current[i], current[i + 1] = out_left, out_right
    joined = DisjointSet(next_edge)
    for top, bottom in enumerate(current):
        joined.union(top, bottom)
    return Diagram.from_pd([[joined.find(e) for e in c] for c in pd], name=name)
