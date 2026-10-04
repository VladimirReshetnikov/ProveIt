"""Essential boundary patterns on a KNOWN 3-ball.

This is an actual polynomial-time kernel of the hierarchy approach. It does not
recognize 3-balls and does not construct or validate an entire 3D hierarchy.
Input: spherical rotation systems for cubic multigraph components, and a count
of vertex-free circle components. Nesting of disconnected components is not
needed for the essential/inessential answer.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from itertools import combinations


@dataclass(frozen=True)
class PatternVerdict:
    essential: bool
    reason: str
    cut_edges: tuple[int, ...] = ()
    side_vertices: tuple[int, ...] = ()
    dual_faces: tuple[int, ...] = ()
    checked_cuts: int = 0

    def to_json(self) -> dict:
        return {"essential": self.essential, "reason": self.reason,
                "cut_edges": list(self.cut_edges), "side_vertices": list(self.side_vertices),
                "dual_faces": list(self.dual_faces), "checked_cuts": self.checked_cuts,
                "scope": "boundary pattern on a known 3-ball only"}


class SphericalPattern:
    def __init__(self, rotations: list[list[int]] | tuple[tuple[int, ...], ...],
                 circle_components: int = 0):
        if type(circle_components) is not int or circle_components < 0:
            raise ValueError("circle_components must be a non-negative integer.")
        self.rotations = tuple(tuple(row) for row in rotations)
        if any(len(row) != 3 for row in self.rotations):
            raise ValueError("Each graph vertex must have valence three (loops count twice).")
        if any(type(e) is not int for row in self.rotations for e in row):
            raise ValueError("Edge identifiers must be integers.")
        counts = Counter(e for row in self.rotations for e in row)
        if any(count != 2 for count in counts.values()):
            raise ValueError("Each edge must occur twice in the rotation lists.")
        if sorted(counts) != list(range(len(counts))):
            raise ValueError("Edge identifiers must be consecutive, beginning at zero.")
        self.circle_components = circle_components
        self.vertex_count = len(self.rotations)
        self.edge_count = len(counts)
        occurrences: dict[int, list[int]] = {}
        for v, row in enumerate(self.rotations):
            for p, edge in enumerate(row):
                occurrences.setdefault(edge, []).append(3 * v + p)
        self.alpha = [0] * (3 * self.vertex_count)
        self.edge_darts = []
        self.endpoints = []
        for edge in range(self.edge_count):
            a, b = occurrences[edge]
            self.alpha[a], self.alpha[b] = b, a
            self.edge_darts.append((a, b))
            self.endpoints.append((a // 3, b // 3))
        self.adjacency: list[list[tuple[int, int]]] = [[] for _ in self.rotations]
        for edge, (a, b) in enumerate(self.endpoints):
            self.adjacency[a].append((b, edge))
            self.adjacency[b].append((a, edge))
        self.components = self._components(frozenset())
        seen = set()
        self.faces = []
        self.dart_face = [0] * len(self.alpha)
        for start in range(len(self.alpha)):
            if start in seen:
                continue
            face, d = [], start
            while d not in seen:
                seen.add(d)
                self.dart_face[d] = len(self.faces)
                face.append(d)
                opposite = self.alpha[d]
                d = 3 * (opposite // 3) + (opposite % 3 + 1) % 3
            self.faces.append(tuple(face))
        for component in self.components:
            vertices = set(component)
            edges = sum(a in vertices for a, b in self.endpoints)
            faces = sum(face[0] // 3 in vertices for face in self.faces)
            if len(vertices) - edges + faces != 2:
                raise ValueError("A component's specified rotation system is not spherical.")

    def _components(self, removed: frozenset[int]) -> tuple[tuple[int, ...], ...]:
        seen = set()
        components = []
        for root in range(self.vertex_count):
            if root in seen:
                continue
            stack = [root]
            seen.add(root)
            component = []
            while stack:
                vertex = stack.pop()
                component.append(vertex)
                for other, edge in self.adjacency[vertex]:
                    if edge not in removed and other not in seen:
                        seen.add(other)
                        stack.append(other)
            components.append(tuple(sorted(component)))
        return tuple(components)

    def _dual_cycle(self, edges: tuple[int, ...]) -> tuple[tuple[int, ...], tuple[int, ...]]:
        """A primal bond is a dual simple cycle, including loops and digons."""
        endpoints = {edge: tuple(self.dart_face[d] for d in self.edge_darts[edge])
                     for edge in edges}
        first = min(edges)
        start, current = endpoints[first]
        ordered, faces, unused = [first], [start, current], set(edges) - {first}
        while unused:
            edge = next((edge for edge in sorted(unused) if current in endpoints[edge]), None)
            if edge is None:
                raise ArithmeticError("A spherical bond did not yield a dual cycle.")
            a, b = endpoints[edge]
            current = b if current == a else a
            faces.append(current)
            ordered.append(edge)
            unused.remove(edge)
        if current != start or len(set(faces[:-1])) != len(edges):
            raise ArithmeticError("The dual bond cycle is not simple.")
        return tuple(ordered), tuple(faces)

    def classify(self) -> PatternVerdict:
        count = len(self.components) + self.circle_components
        if count == 0:
            return PatternVerdict(True, "empty pattern")
        if count > 1:
            side = self.components[0] if self.components else ()
            return PatternVerdict(False, "disconnected pattern: a zero-crossing separator exists",
                                  side_vertices=side)
        if self.circle_components:
            return PatternVerdict(True, "a single circle")
        checked = 0
        for size in (1, 2, 3):
            for cut in combinations(range(self.edge_count), size):
                checked += 1
                components = self._components(frozenset(cut))
                if len(components) != 2:
                    continue
                side = set(components[0])
                # An inclusion-minimal edge cut (a bond) has connected sides
                # and every deleted edge runs between the two sides.
                if not all((self.endpoints[e][0] in side) !=
                           (self.endpoints[e][1] in side) for e in cut):
                    continue
                if size == 3 and min(map(len, components)) == 1:
                    continue  # one side is exactly a tripod
                edges, faces = self._dual_cycle(cut)
                return PatternVerdict(False, "nontrivial bond of size at most three", edges,
                                      components[0], faces, checked)
        return PatternVerdict(True, "all short bonds are trivial tripod cuts", checked_cuts=checked)

    def verify_witness(self, verdict: PatternVerdict) -> bool:
        """Check a negative witness without running the exhaustive cut search."""
        if verdict.essential:
            return False
        if len(self.components) + self.circle_components > 1:
            return not verdict.cut_edges
        cut = frozenset(verdict.cut_edges)
        if len(cut) != len(verdict.cut_edges) or not 1 <= len(cut) <= 3:
            return False
        if any(type(e) is not int or not 0 <= e < self.edge_count for e in cut):
            return False
        components = self._components(cut)
        if len(components) != 2:
            return False
        side = set(verdict.side_vertices)
        if side not in (set(components[0]), set(components[1])):
            return False
        if not all((self.endpoints[e][0] in side) != (self.endpoints[e][1] in side) for e in cut):
            return False
        if len(cut) == 3 and min(map(len, components)) == 1:
            return False
        faces = verdict.dual_faces
        if len(faces) != len(cut) + 1 or faces[0] != faces[-1]:
            return False
        if len(set(faces[:-1])) != len(cut):
            return False
        for i, edge in enumerate(verdict.cut_edges):
            a, b = (self.dart_face[d] for d in self.edge_darts[edge])
            if (faces[i], faces[i + 1]) not in ((a, b), (b, a)):
                return False
        return True
