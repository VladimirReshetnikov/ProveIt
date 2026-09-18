"""Classical one-component planar diagrams and braid closures.

A crossing is four edge labels in counterclockwise cyclic order.
Positions 0,2 form the under-strand; positions 1,3 form the over-strand.
The empty PD denotes ONE crossing-free circle, not an empty link.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from typing import Sequence

from .algebra import DisjointSet


class InvalidDiagram(ValueError):
    pass


@dataclass(frozen=True)
class PlanarDiagram:
    crossings: tuple[tuple[int, int, int, int], ...]

    def __post_init__(self) -> None:
        try:
            crossings = tuple(tuple(row) for row in self.crossings)
        except TypeError as exc:
            raise InvalidDiagram("PD must be a list of four-entry lists.") from exc
        if any(len(row) != 4 for row in crossings):
            raise InvalidDiagram("Every crossing needs four edge labels.")
        if any(type(x) is not int for row in crossings for x in row):
            raise InvalidDiagram("Edge labels must be integers.")
        if not crossings:
            object.__setattr__(self, "crossings", ())
            return
        counts = Counter(x for row in crossings for x in row)
        if any(count != 2 for count in counts.values()):
            raise InvalidDiagram("Every edge label must occur exactly twice.")
        labels = {label: i for i, label in enumerate(sorted(counts))}
        normalized = tuple(tuple(labels[x] for x in row) for row in crossings)
        object.__setattr__(self, "crossings", normalized)
        alpha = self.edge_involution()
        dsu = DisjointSet(4 * self.n)
        for d in range(4 * self.n):
            dsu.union(d, alpha[d])
            dsu.union(d, 4 * (d // 4) + (d % 4 + 2) % 4)
        if len({dsu.find(d) for d in range(4 * self.n)}) != 1:
            raise InvalidDiagram("The diagram must have exactly one link component.")
        # The rotation system determines the actual embedding, not merely
        # whether its abstract graph admits some planar embedding.
        if self.n - 2 * self.n + len(self.face_darts()) != 2:
            raise InvalidDiagram("The given rotation system is not a sphere diagram.")

    @property
    def n(self) -> int:
        return len(self.crossings)

    def to_json(self) -> dict:
        return {"pd": [list(row) for row in self.crossings]}

    def edge_involution(self) -> tuple[int, ...]:
        occurrences: dict[int, list[int]] = {}
        for v, crossing in enumerate(self.crossings):
            for p, label in enumerate(crossing):
                occurrences.setdefault(label, []).append(4 * v + p)
        alpha = [0] * (4 * self.n)
        for a, b in occurrences.values():
            alpha[a], alpha[b] = b, a
        return tuple(alpha)

    def face_darts(self) -> tuple[tuple[int, ...], ...]:
        alpha = self.edge_involution()
        seen: set[int] = set()
        faces = []
        for start in range(len(alpha)):
            if start in seen:
                continue
            face, d = [], start
            while d not in seen:
                seen.add(d)
                face.append(d)
                opposite = alpha[d]
                d = 4 * (opposite // 4) + (opposite % 4 + 1) % 4
            faces.append(tuple(face))
        return tuple(faces)

    def mirror(self) -> PlanarDiagram:
        return PlanarDiagram(tuple((b, c, d, a) for a, b, c, d in self.crossings))


def braid_closure(strands: int, word: Sequence[int]) -> PlanarDiagram:
    """Closure of an Artin braid; positive sigma_i has left strand over right.

    Reject multi-component closures rather than dropping crossing-free components.
    Strand count is part of the explicit input size.
    """
    if type(strands) is not int or strands < 1:
        raise InvalidDiagram("The number of strands must be a positive integer.")
    try:
        word = tuple(word)
    except TypeError as exc:
        raise InvalidDiagram("The braid word must be a sequence of integers.") from exc
    if any(type(g) is not int or g == 0 or abs(g) >= strands for g in word):
        raise InvalidDiagram("Each generator must satisfy 1 <= abs(g) < strands.")
    if strands > 1 and len(word) < strands - 1:
        raise InvalidDiagram("Too few crossings for a one-component braid closure.")
    perm = list(range(strands))
    for generator in word:
        i = abs(generator) - 1
        perm[i], perm[i + 1] = perm[i + 1], perm[i]
    visited = set()
    k = 0
    while k not in visited:
        visited.add(k)
        k = perm[k]
    if len(visited) != strands:
        raise InvalidDiagram("The braid closure has more than one component.")
    if not word:
        return PlanarDiagram(())
    current = list(range(strands))
    next_label = strands
    rows = []
    for generator in word:
        i = abs(generator) - 1
        a, b = current[i:i + 2]
        c, d = next_label, next_label + 1
        next_label += 2
        rows.append((b, a, c, d) if generator > 0 else (a, c, d, b))
        current[i:i + 2] = [c, d]
    dsu = DisjointSet(next_label)
    for i, label in enumerate(current):
        dsu.union(i, label)
    return PlanarDiagram(tuple(tuple(dsu.find(x) for x in row) for row in rows))


def read_diagram(data: object) -> PlanarDiagram:
    if not isinstance(data, dict):
        raise InvalidDiagram("Input must be an object containing 'pd' or 'braid'.")
    if ("pd" in data) == ("braid" in data):
        raise InvalidDiagram("Supply exactly one of 'pd' and 'braid'.")
    if "pd" in data:
        return PlanarDiagram(data["pd"])
    braid = data["braid"]
    if not isinstance(braid, dict) or "strands" not in braid or "word" not in braid:
        raise InvalidDiagram("A braid needs 'strands' and 'word'.")
    return braid_closure(braid["strands"], braid["word"])
