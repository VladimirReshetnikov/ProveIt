"""Polynomial essential-pattern test on the boundary of an ALREADY KNOWN 3-ball.

Input is a cubic spherical rotation system, plus vertex-free circle components.
This module neither recognizes a 3-ball nor constructs a 3-manifold hierarchy.
The criterion is Proposition 2.6 of Lackenby, arXiv:2607.23350v1.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Any


@dataclass(frozen=True)
class BallPattern:
    """At each vertex: three darts in cyclic order; edge pairing is d <-> d^1.

    Each dart from 0 through 3*V-1 occurs once. A loop uses two darts at one
    vertex. Every connected rotation-system component must have genus zero.
    Separate component nesting is immaterial to the essentialness decision.
    """
    rotations: tuple[tuple[int, int, int], ...] = ()
    circles: int = 0

    def __post_init__(self) -> None:
        if type(self.circles) is not int or self.circles < 0:
            raise ValueError("circles must be a nonnegative integer")
        if not isinstance(self.rotations, tuple):
            raise ValueError("rotations must be a tuple")
        if any(not isinstance(r, tuple) or len(r) != 3 for r in self.rotations):
            raise ValueError("every graph vertex must have three darts")
        darts = [d for r in self.rotations for d in r]
        if any(type(d) is not int for d in darts) or len(darts) % 2:
            raise ValueError("invalid dart data")
        if sorted(darts) != list(range(len(darts))):
            raise ValueError("each dart 0..3*V-1 must occur exactly once")
        vertex_of = self.vertex_of()
        faces = self.faces()
        adjacency = [set() for _ in self.rotations]
        for d in range(0, len(darts), 2):
            a, b = vertex_of[d], vertex_of[d ^ 1]
            adjacency[a].add(b)
            adjacency[b].add(a)
        for component in _components(adjacency):
            edge_count = sum(vertex_of[d] in component for d in range(0, len(darts), 2))
            face_count = sum(vertex_of[face[0]] in component for face in faces)
            if len(component) - edge_count + face_count != 2:
                raise ValueError("rotation system is not spherical")

    @classmethod
    def from_json(cls, value: Any) -> BallPattern:
        if not isinstance(value, dict):
            raise ValueError("pattern must be an object")
        rows = value.get("rotations", [])
        if not isinstance(rows, list) or any(not isinstance(row, list) for row in rows):
            raise ValueError("rotations must be an array of arrays")
        return cls(tuple(tuple(row) for row in rows), value.get("circles", 0))

    def vertex_of(self) -> tuple[int, ...]:
        result = [0] * (3 * len(self.rotations))
        for v, row in enumerate(self.rotations):
            for d in row:
                result[d] = v
        return tuple(result)

    def faces(self) -> tuple[tuple[int, ...], ...]:
        successor = [0] * (3 * len(self.rotations))
        for row in self.rotations:
            for i in range(3):
                successor[row[i]] = row[(i + 1) % 3]
        unseen = set(range(len(successor)))
        faces = []
        while unseen:
            start = min(unseen)
            d = start
            face = []
            while d in unseen:
                unseen.remove(d)
                face.append(d)
                d = successor[d ^ 1]
            if d != start:
                raise ValueError("invalid face permutation")
            faces.append(tuple(face))
        return tuple(faces)

    def graph_components(self) -> list[set[int]]:
        vertex_of = self.vertex_of()
        adjacency = [set() for _ in self.rotations]
        for d in range(0, len(vertex_of), 2):
            a, b = vertex_of[d], vertex_of[d ^ 1]
            adjacency[a].add(b)
            adjacency[b].add(a)
        return _components(adjacency)


def _components(adjacency: list[set[int]], removed: frozenset[int] = frozenset()
                ) -> list[set[int]]:
    unseen = set(range(len(adjacency))) - removed
    result = []
    while unseen:
        root = min(unseen)
        unseen.remove(root)
        component = {root}
        stack = [root]
        while stack:
            for v in adjacency[stack.pop()]:
                if v in unseen:
                    unseen.remove(v)
                    component.add(v)
                    stack.append(v)
        result.append(component)
    return result


def assess_pattern(pattern: BallPattern) -> dict[str, Any]:
    """O(F^3*(F+E)) direct dual-connectivity test, not a geometric disc search."""
    components = pattern.graph_components()
    total_components = len(components) + pattern.circles
    if total_components == 0:
        return {"essential": True, "reason": "empty_pattern"}
    if total_components > 1:
        return {"essential": False, "reason": "disconnected_pattern",
                "witness": {"pattern_components": total_components}}
    if pattern.circles == 1:
        return {"essential": True, "reason": "single_circle"}
    faces = pattern.faces()
    face_of = [0] * (3 * len(pattern.rotations))
    for i, face in enumerate(faces):
        for d in face:
            face_of[d] = i
    edge_between: dict[tuple[int, int], int] = {}
    adjacency: list[set[int]] = [set() for _ in faces]
    for d in range(0, len(face_of), 2):
        a, b = sorted((face_of[d], face_of[d ^ 1]))
        if a == b:
            return {"essential": False, "reason": "dual_loop",
                    "witness": {"primal_edges": [d // 2]}}
        if (a, b) in edge_between:
            return {"essential": False, "reason": "dual_parallel_edges",
                    "witness": {"primal_edges": [edge_between[a, b], d // 2]}}
        edge_between[a, b] = d // 2
        adjacency[a].add(b)
        adjacency[b].add(a)
    n = len(faces)
    if n in (3, 4) and len(edge_between) == n * (n - 1) // 2:
        return {"essential": True, "reason": f"dual_K{n}"}
    if n < 5:
        raise ArithmeticError("unexpected simple dual of a connected cubic spherical graph")
    for k in range(1, 4):
        for separator in combinations(range(n), k):
            remaining = _components(adjacency, frozenset(separator))
            if len(remaining) > 1:
                return {"essential": False, "reason": "dual_vertex_separator",
                        "witness": {"dual_vertices": list(separator),
                                    "remaining_components": [sorted(c) for c in remaining]}}
    return {"essential": True, "reason": "dual_4_connected"}
