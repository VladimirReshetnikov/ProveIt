"""Validated classical one-component planar diagrams and closed braids.

PD convention: each crossing lists four ports counterclockwise, starting on
an underpassing port. Opposite ports belong to the same strand. Empty PD
means ONE crossing-free circle, never the empty link.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterable


class DiagramError(ValueError):
    """The data do not encode a classical one-component knot diagram."""


class DisjointSet:
    def __init__(self, size: int):
        self.parent = list(range(size))
        self.size = [1] * size

    def find(self, a: int) -> int:
        while self.parent[a] != a:
            self.parent[a] = self.parent[self.parent[a]]
            a = self.parent[a]
        return a

    def union(self, a: int, b: int) -> None:
        a, b = self.find(a), self.find(b)
        if a == b:
            return
        if self.size[a] < self.size[b]:
            a, b = b, a
        self.parent[b] = a
        self.size[a] += self.size[b]


def cycles(permutation: tuple[int, ...] | list[int]) -> tuple[tuple[int, ...], ...]:
    """Cycle decomposition; the caller supplies a valid permutation."""
    visited: set[int] = set()
    result = []
    for start in range(len(permutation)):
        if start in visited:
            continue
        orbit = []
        a = start
        while a not in visited:
            visited.add(a)
            orbit.append(a)
            a = permutation[a]
        result.append(tuple(orbit))
    return tuple(result)


@dataclass(frozen=True)
class Diagram:
    """A normalized PD. Use from_pd() or from_braid(), not this constructor.

    The public recognition function revalidates instances, so direct construction
    cannot bypass the knot and planarity checks.
    """
    pd: tuple[tuple[int, int, int, int], ...]
    basepoint: int = 0

    @property
    def crossings(self) -> int:
        return len(self.pd)

    @property
    def edges(self) -> int:
        return 2 * len(self.pd)

    @classmethod
    def from_pd(cls, data: Iterable[Iterable[int]],
                basepoint: int | None = None) -> Diagram:
        if isinstance(data, (str, bytes, dict)):
            raise DiagramError("PD must be a list of four-integer crossings")
        try:
            raw = tuple(tuple(crossing) for crossing in data)
        except TypeError as exc:
            raise DiagramError("PD must be a list of four-integer crossings") from exc
        labels: dict[int, int] = {}
        pd = []
        occurrences: dict[int, list[int]] = {}
        for i, crossing in enumerate(raw):
            if len(crossing) != 4:
                raise DiagramError(f"crossing {i} must have four ports")
            row = []
            for j, label in enumerate(crossing):
                if type(label) is not int or label < 0:
                    raise DiagramError("arc labels must be nonnegative integers, not bools")
                if label not in labels:
                    labels[label] = len(labels)
                normalized = labels[label]
                row.append(normalized)
                occurrences.setdefault(normalized, []).append(4 * i + j)
            pd.append(tuple(row))
        if not raw:
            if basepoint is not None and (type(basepoint) is not int or basepoint != 0):
                raise DiagramError("the empty PD has only the conventional basepoint 0")
            return cls((), 0)
        if any(len(ports) != 2 for ports in occurrences.values()):
            raise DiagramError("each arc label must occur exactly twice")
        if basepoint is None:
            marked = 0
        elif type(basepoint) is not int or basepoint not in labels:
            raise DiagramError("basepoint must be an arc label present in the PD")
        else:
            marked = labels[basepoint]

        n = len(raw)
        alpha = list(range(4 * n))
        components = DisjointSet(4 * n)
        for a, b in occurrences.values():
            alpha[a], alpha[b] = b, a
            components.union(a, b)
        for i in range(n):
            components.union(4 * i, 4 * i + 2)
            components.union(4 * i + 1, 4 * i + 3)
        component_count = len({components.find(d) for d in range(4 * n)})
        if component_count != 1:
            raise DiagramError(f"expected a knot, found {component_count} components")
        # A one-component knot has connected underlying projection. Its ribbon
        # graph thickening caps to an oriented surface with chi = n-2n+F.
        face_permutation = [4 * (alpha[d] // 4) + (alpha[d] + 1) % 4
                            for d in range(4 * n)]
        faces = len(cycles(face_permutation))
        euler = faces - n
        if euler != 2:
            genus = (2 - euler) // 2
            raise DiagramError(
                f"nonplanar rotation system (supporting genus {genus}); "
                "virtual diagrams are not supported")
        return cls(tuple(pd), marked)

    @classmethod
    def from_braid(cls, strands: int, word: Iterable[int]) -> Diagram:
        """Close an Artin braid; generators are +/-1,...,+/-(strands-1).

        Positive generators have the upper-left strand passing over the
        upper-right strand. Returns only one-component closures.
        """
        if type(strands) is not int or strands < 1:
            raise DiagramError("strands must be a positive integer")
        if isinstance(word, (str, bytes, dict)):
            raise DiagramError("braid word must be a list of signed integers")
        try:
            word = tuple(word)
        except TypeError as exc:
            raise DiagramError("braid word must be iterable") from exc
        if any(type(g) is not int or g == 0 or abs(g) >= strands for g in word):
            raise DiagramError("braid generators must satisfy 1 <= abs(g) < strands")
        # Check closure components before omitting any crossing-free strands.
        position = list(range(strands))
        for g in word:
            i = abs(g) - 1
            position[i], position[i + 1] = position[i + 1], position[i]
        count = len(cycles(position))
        if count != 1:
            raise DiagramError(f"braid closure has {count} components, not one")
        if not word:
            return cls((), 0)
        current = list(range(strands))
        next_label = strands
        pd = []
        for g in word:
            i = abs(g) - 1
            incoming_left, incoming_right = current[i:i + 2]
            outgoing_left, outgoing_right = next_label, next_label + 1
            next_label += 2
            if g > 0:
                crossing = (incoming_right, incoming_left, outgoing_left, outgoing_right)
            else:
                crossing = (incoming_left, outgoing_left, outgoing_right, incoming_right)
            pd.append(crossing)
            current[i:i + 2] = [outgoing_left, outgoing_right]
        closure = DisjointSet(next_label)
        for top, bottom in enumerate(current):
            closure.union(top, bottom)
        closed_pd = [tuple(closure.find(a) for a in row) for row in pd]
        return cls.from_pd(closed_pd)

    @classmethod
    def from_json(cls, value: Any) -> Diagram:
        if isinstance(value, list):
            return cls.from_pd(value)
        if not isinstance(value, dict):
            raise DiagramError("input must be a PD array or a JSON object")
        if "pd" in value and "braid" in value:
            raise DiagramError("specify pd or braid, not both")
        if "pd" in value:
            extra = set(value) - {"pd", "basepoint", "name", "description", "expected_rank"}
            if extra:
                raise DiagramError(f"unexpected keys: {sorted(extra)}")
            return cls.from_pd(value["pd"], value.get("basepoint"))
        if "braid" in value:
            extra = set(value) - {"braid", "name", "description", "expected_rank"}
            if extra:
                raise DiagramError(f"unexpected keys: {sorted(extra)}")
            braid = value["braid"]
            if not isinstance(braid, dict) or set(braid) != {"strands", "word"}:
                raise DiagramError("braid must have exactly strands and word keys")
            return cls.from_braid(braid["strands"], braid["word"])
        raise DiagramError("JSON object must contain pd or braid")

    def mirror(self) -> Diagram:
        return Diagram.from_pd([row[1:] + row[:1] for row in self.pd], self.basepoint)

    def to_json(self) -> dict[str, Any]:
        return {"pd": [list(row) for row in self.pd], "basepoint": self.basepoint}
