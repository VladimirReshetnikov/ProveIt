"""Essential boundary patterns on the boundary of a KNOWN 3-ball.

Supported patterns are disjoint unions of embedded cubic multigraphs and
vertex-free circles. A rotation system specifies each graph component's
spherical embedding. Relative nesting is irrelevant to essentiality here.

This is a terminal hierarchy subroutine, NOT an unknot or 3-ball recognizer.
It must never be applied to a general 3-manifold merely because its boundary
is a sphere. The caller must establish the 3-ball precondition separately.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Any

from .diagram import cycles


@dataclass(frozen=True)
class BallPattern:
    # Edge e has darts 2*e and 2*e+1. Each vertex is a cyclic triple of darts.
    rotation: tuple[tuple[int, int, int], ...]
    circles: int = 0

    @classmethod
    def from_json(cls, data: Any) -> BallPattern:
        if not isinstance(data, dict) or data.get("ambient") != "3-ball":
            raise ValueError("Pattern input must explicitly set ambient to '3-ball'")
        raw = data.get("rotation")
        if not isinstance(raw, (list, tuple)):
            raise ValueError("rotation must be a list of cyclic triples of darts")
        rotation = []
        for row in raw:
            if not isinstance(row, (list, tuple)) or len(row) != 3:
                raise ValueError("Every graph vertex must have degree three")
            if any(type(d) is not int or d < 0 for d in row):
                raise ValueError("Darts must be nonnegative integers")
            rotation.append(tuple(row))
        circle_count = data.get("circles", 0)
        if type(circle_count) is not int or circle_count < 0:
            raise ValueError("circles must be a nonnegative integer")
        flat = [d for vertex in rotation for d in vertex]
        if len(flat) % 2 or sorted(flat) != list(range(len(flat))):
            raise ValueError("Darts must occur exactly once and be numbered 0 through 2E-1")
        pattern = cls(tuple(rotation), circle_count)  # type: ignore[arg-type]
        # Every connected rotation-system component must be spherical.
        sigma = [0] * len(flat)
        for a, b, c in rotation:
            sigma[a], sigma[b], sigma[c] = b, c, a
        faces = cycles([sigma[d ^ 1] for d in range(len(flat))])
        vertices_of_darts = pattern.dart_vertices()
        parts = pattern.components()
        owner = [0] * len(rotation)
        for index, part in enumerate(parts):
            for vertex in part:
                owner[vertex] = index
        edge_counts, face_counts = [0] * len(parts), [0] * len(parts)
        for a, _ in pattern.edges():
            edge_counts[owner[a]] += 1
        for face in faces:
            face_counts[owner[vertices_of_darts[face[0]]]] += 1
        for index, part in enumerate(parts):
            if len(part) - edge_counts[index] + face_counts[index] != 2:
                raise ValueError("Every connected graph rotation system must be spherical")
        return pattern

    def dart_vertices(self) -> list[int]:
        result = [0] * (3 * len(self.rotation))
        for vertex, darts in enumerate(self.rotation):
            for dart in darts:
                result[dart] = vertex
        return result

    def edges(self) -> tuple[tuple[int, int], ...]:
        where = self.dart_vertices()
        return tuple((where[d], where[d + 1]) for d in range(0, len(where), 2))

    def components(self, removed: frozenset[int] = frozenset()) -> list[tuple[int, ...]]:
        adjacency: list[list[int]] = [[] for _ in self.rotation]
        for i, (a, b) in enumerate(self.edges()):
            if i not in removed:
                adjacency[a].append(b)
                adjacency[b].append(a)
        unseen = set(range(len(self.rotation)))
        parts = []
        while unseen:
            root = min(unseen)
            unseen.remove(root)
            component, pending = [], [root]
            while pending:
                vertex = pending.pop()
                component.append(vertex)
                for neighbor in adjacency[vertex]:
                    if neighbor in unseen:
                        unseen.remove(neighbor)
                        pending.append(neighbor)
            parts.append(tuple(sorted(component)))
        return parts

    def to_json(self) -> dict[str, Any]:
        return {"ambient": "3-ball", "rotation": [list(v) for v in self.rotation],
                "circles": self.circles}


def classify_pattern(pattern: BallPattern) -> dict[str, Any]:
    """Exhaustively enumerate bonds of size at most three, in O(E^4) time.

    A bond is a minimal nonempty edge cut. In a connected sphere-embedded
    graph it is dual to a simple closed curve crossing exactly those edges.
    In a cubic graph, a three-edge bond is harmless precisely when one side
    consists of a single vertex, i.e. the permitted tripod. A one- or two-edge
    bond is violating. Disconnected nonempty patterns have a zero-crossing
    violating curve; an empty pattern or sole circle is essential.
    """
    pattern = BallPattern.from_json(pattern.to_json())
    parts = pattern.components()
    count = len(parts) + pattern.circles
    result: dict[str, Any] = {"schema": "ball-pattern-result-v1", "input": pattern.to_json(),
                              "algorithm": "small-bond-enumeration", "worst_case": "O(E^4)",
                              "precondition": "ambient is a known 3-ball"}
    if count > 1:
        result.update(status="violating", witness={"kind": "disconnected-pattern",
                                                   "intersections": 0,
                                                   "component_count": count})
        return result
    edges = pattern.edges()
    if count == 0 or pattern.circles == 1:
        result.update(status="essential", tested_edge_subsets=0)
        return result
    tested = 0
    for size in range(1, 4):
        for cut in combinations(range(len(edges)), size):
            tested += 1
            pieces = pattern.components(frozenset(cut))
            if len(pieces) != 2:
                continue
            side = set(pieces[0])
            boundary = tuple(e for e, (a, b) in enumerate(edges) if (a in side) != (b in side))
            if boundary != cut:
                continue  # This subset contains redundant removed edges; it is not a bond.
            if size == 3 and min(map(len, pieces)) == 1:
                continue  # A disk on one side meets the pattern in a tripod.
            result.update(status="violating", tested_edge_subsets=tested,
                          witness={"kind": "bond", "intersections": size,
                                   "cut_edges": list(cut),
                                   "vertex_sides": [list(p) for p in pieces]})
            return result
    result.update(status="essential", tested_edge_subsets=tested)
    return result


def verify_violating_witness(pattern: BallPattern, witness: Any) -> bool:
    """Verify a negative witness directly, without rerunning subset enumeration."""
    pattern = BallPattern.from_json(pattern.to_json())
    if not isinstance(witness, dict):
        return False
    count = len(pattern.components()) + pattern.circles
    if witness.get("kind") == "disconnected-pattern":
        return (count >= 2 and witness.get("intersections") == 0
                and witness.get("component_count") == count)
    if witness.get("kind") != "bond" or count != 1 or pattern.circles:
        return False
    cut = witness.get("cut_edges")
    if not isinstance(cut, list) or any(type(e) is not int for e in cut):
        return False
    edges = pattern.edges()
    if (len(cut) not in (1, 2, 3) or sorted(set(cut)) != cut
            or any(not 0 <= e < len(edges) for e in cut)
            or witness.get("intersections") != len(cut)):
        return False
    parts = pattern.components(frozenset(cut))
    if len(parts) != 2 or witness.get("vertex_sides") != [list(p) for p in parts]:
        return False
    first = set(parts[0])
    if [e for e, (a, b) in enumerate(edges) if (a in first) != (b in first)] != cut:
        return False
    return len(cut) != 3 or min(map(len, parts)) > 1
