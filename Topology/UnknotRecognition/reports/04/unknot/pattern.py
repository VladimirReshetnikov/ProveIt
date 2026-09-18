"""Essentiality of a boundary pattern on an ALREADY KNOWN 3-ball.

Implements the finite graph test behind the terminal hierarchy step. It does
not recognize 3-balls, construct compression discs in a 3-manifold, or build
a hierarchy. The caller supplies the ball hypothesis. See Lackenby (2026),
Proposition 2.6, and the user's slides 24--26 and 109.

Each vertex is a counterclockwise cyclic list of three signed edge labels;
each positive label must occur once and its negative must occur once.
Unvertexed simple closed curves are recorded separately as `circles`.
For multiple components the relative nesting is unnecessary for this test.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Any

from .diagram import DisjointSet, cycles


class PatternError(ValueError):
    pass


@dataclass(frozen=True)
class PatternResult:
    essential_on_ball: bool
    reason: str
    witness: dict[str, Any]
    components: int
    dual_vertices: int | None

    def to_json(self) -> dict[str, Any]:
        return {
            "essential_on_assumed_ball": self.essential_on_ball,
            "required_hypothesis": "the ambient 3-manifold is already known to be a ball",
            "reason": self.reason,
            "graph_obstruction": self.witness,
            "pattern_components": self.components,
            "dual_vertices": self.dual_vertices,
            "constructs_embedded_violating_disc": False,
        }


def components_without(adjacency: list[set[int]], removed: set[int]) -> list[list[int]]:
    remaining = [v not in removed for v in range(len(adjacency))]
    components = []
    for start in range(len(adjacency)):
        if not remaining[start]:
            continue
        remaining[start] = False
        queue = [start]
        for vertex in queue:
            for neighbor in adjacency[vertex]:
                if remaining[neighbor]:
                    remaining[neighbor] = False
                    queue.append(neighbor)
        components.append(queue)
    return components


def classify_ball_pattern(vertices: list[list[int]] | tuple[tuple[int, ...], ...],
                          circles: int = 0) -> PatternResult:
    if type(circles) is not int or circles < 0:
        raise PatternError("circles must be a nonnegative integer")
    if not isinstance(vertices, (list, tuple)):
        raise PatternError("vertices must be an array of cyclic triples")
    halfedges: dict[int, int] = {}
    rows = []
    for v, row in enumerate(vertices):
        if not isinstance(row, (list, tuple)) or len(row) != 3:
            raise PatternError("every graph vertex must be trivalent")
        for j, label in enumerate(row):
            if type(label) is not int or label == 0:
                raise PatternError("halfedge labels must be nonzero signed integers")
            if label in halfedges:
                raise PatternError("each signed halfedge label must occur once")
            halfedges[label] = 3 * v + j
        rows.append(tuple(row))
    if any(-label not in halfedges for label in halfedges):
        raise PatternError("every edge must have both a positive and a negative end")
    if not rows:
        return PatternResult(circles <= 1,
                             "empty_or_single_circle" if circles <= 1
                             else "disconnected_pattern", {}, circles, None)
    vertex_union = DisjointSet(len(rows))
    alpha = list(range(3 * len(rows)))
    for label, dart in halfedges.items():
        opposite = halfedges[-label]
        alpha[dart] = opposite
        vertex_union.union(dart // 3, opposite // 3)
    phi = [3 * (alpha[d] // 3) + (alpha[d] + 1) % 3 for d in range(len(alpha))]
    faces = cycles(phi)
    face_of = [0] * len(alpha)
    counts: dict[int, list[int]] = {}
    for v in range(len(rows)):
        root = vertex_union.find(v)
        counts.setdefault(root, [0, 0, 0])[0] += 1
    for label, dart in halfedges.items():
        if label > 0:
            counts[vertex_union.find(dart // 3)][1] += 1
    for index, face in enumerate(faces):
        counts[vertex_union.find(face[0] // 3)][2] += 1
        for dart in face:
            face_of[dart] = index
    for num_v, num_e, num_f in counts.values():
        if num_v - num_e + num_f != 2:
            raise PatternError("a graph component has a non-spherical rotation system")
    component_count = len(counts) + circles
    if component_count != 1:
        return PatternResult(False, "disconnected_pattern", {}, component_count, None)

    dual_count = len(faces)
    adjacency: list[set[int]] = [set() for _ in faces]
    seen: dict[tuple[int, int], int] = {}
    for label, dart in halfedges.items():
        if label < 0:
            continue
        a, b = face_of[dart], face_of[alpha[dart]]
        if a == b:
            return PatternResult(False, "dual_loop", {"primal_edge": label,
                                 "dual_vertex": a}, 1, dual_count)
        edge = tuple(sorted((a, b)))
        if edge in seen:
            return PatternResult(False, "dual_parallel_edges",
                                 {"primal_edges": [seen[edge], label],
                                  "dual_endpoints": list(edge)}, 1, dual_count)
        seen[edge] = label
        adjacency[a].add(b)
        adjacency[b].add(a)
    if dual_count in (3, 4) and all(len(neighbors) == dual_count - 1
                                    for neighbors in adjacency):
        return PatternResult(True, f"dual_is_K{dual_count}", {}, 1, dual_count)
    for size in range(4):
        for separator in combinations(range(dual_count), size):
            separated = components_without(adjacency, set(separator))
            if len(separated) > 1:
                return PatternResult(False, "dual_separator",
                                     {"separator": list(separator),
                                      "remaining_components": separated}, 1, dual_count)
    if dual_count < 5:
        # A connected simple triangulated sphere has at least three vertices;
        # the small exceptions were checked above. Reject an invariant failure.
        raise PatternError("unexpected small dual graph; check input rotations")
    return PatternResult(True, "dual_is_simple_4_connected", {}, 1, dual_count)
