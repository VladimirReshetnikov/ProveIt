"""Exact polynomial essentiality test for boundary patterns on a KNOWN 3-ball.

Pattern = disjoint embedded cubic multigraphs and vertex-free circles on S^2.
A rotation lists three half-edge IDs at each vertex. IDs 2e and 2e+1 are
paired to form edge e. Graphs need not be simple. Each component's rotation
must have genus zero. Nesting of distinct components is immaterial to this
yes/no test: every pattern with at least two components is inessential.

This does NOT recognize balls, construct a hierarchy, or test a pattern on
an arbitrary 3-manifold. In particular, it must not be used merely because
b_1(M)=0 or the boundary of M is a sphere.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations

from .diagrams import permutation_cycles


class InvalidPattern(ValueError):
    pass


@dataclass(frozen=True)
class BallPattern:
    rotations: tuple[tuple[int, int, int], ...]
    circle_components: int = 0

    def __post_init__(self) -> None:
        if type(self.circle_components) is not int or self.circle_components < 0:
            raise InvalidPattern("circle_components must be a nonnegative integer")
        if any(len(row) != 3 for row in self.rotations):
            raise InvalidPattern("Each graph vertex must have exactly three half-edges")
        flat = [d for row in self.rotations for d in row]
        if any(type(d) is not int for d in flat):
            raise InvalidPattern("Half-edge IDs must be integers")
        if len(flat) % 2 or sorted(flat) != list(range(len(flat))):
            raise InvalidPattern("Half-edges must partition 0,...,2E-1 exactly once")
        if not flat:
            return
        owner = self.owners()
        faces = self.face_cycles()
        for component in self.components():
            edges = {d // 2 for v in component for d in self.rotations[v]}
            face_count = sum(owner[face[0]] in component for face in faces)
            if len(component) - len(edges) + face_count != 2:
                raise InvalidPattern("A graph component is not embedded on a sphere")

    @classmethod
    def from_json(cls, obj: object) -> BallPattern:
        if not isinstance(obj, dict) or "rotations" not in obj:
            raise InvalidPattern("Pattern requires rotations and optional circle_components")
        rotations = obj["rotations"]
        if not isinstance(rotations, (list, tuple)):
            raise InvalidPattern("rotations must be a list")
        if any(not isinstance(row, (list, tuple)) for row in rotations):
            raise InvalidPattern("Each rotation must be a list")
        return cls(tuple(tuple(row) for row in rotations), obj.get("circle_components", 0))

    @property
    def edge_count(self) -> int:
        return 3 * len(self.rotations) // 2

    def owners(self) -> list[int]:
        owner = [0] * (2 * self.edge_count)
        for v, row in enumerate(self.rotations):
            for d in row:
                owner[d] = v
        return owner

    def endpoints(self) -> list[tuple[int, int]]:
        owner = self.owners()
        return [(owner[2 * e], owner[2 * e + 1]) for e in range(self.edge_count)]

    def face_cycles(self) -> list[tuple[int, ...]]:
        rho = [0] * (2 * self.edge_count)
        for row in self.rotations:
            for i, dart in enumerate(row):
                rho[dart] = row[(i + 1) % 3]
        return permutation_cycles([rho[d ^ 1] for d in range(len(rho))])

    def components(self, deleted: frozenset[int] = frozenset()) -> list[frozenset[int]]:
        adjacency = [[] for _ in self.rotations]
        for e, (u, v) in enumerate(self.endpoints()):
            if e not in deleted:
                adjacency[u].append(v)
                adjacency[v].append(u)
        unvisited = set(range(len(adjacency)))
        components = []
        for start in range(len(adjacency)):
            if start not in unvisited:
                continue
            unvisited.remove(start)
            component, stack = {start}, [start]
            while stack:
                for neighbor in adjacency[stack.pop()]:
                    if neighbor in unvisited:
                        unvisited.remove(neighbor)
                        component.add(neighbor)
                        stack.append(neighbor)
            components.append(frozenset(component))
        return components

    def cut_edges(self, shore: frozenset[int]) -> tuple[int, ...]:
        return tuple(e for e, (u, v) in enumerate(self.endpoints())
                     if (u in shore) != (v in shore))

    def dual_cycle(self, edges: tuple[int, ...]) -> dict:
        """Construct the simple dual cycle of a primal bond of size <=3."""
        face_of = [0] * (2 * self.edge_count)
        for face_id, face in enumerate(self.face_cycles()):
            for dart in face:
                face_of[dart] = face_id
        dual = {e: (face_of[2 * e], face_of[2 * e + 1]) for e in edges}
        start = min(v for ends in dual.values() for v in ends)
        current = start
        remaining = set(edges)
        ordered_edges, ordered_faces = [], [start]
        while remaining:
            choices = [e for e in remaining if current in dual[e]]
            if not choices:
                raise ArithmeticError("Disconnected dual cycle")
            edge = min(choices)
            a, b = dual[edge]
            current = b if current == a else a
            remaining.remove(edge)
            ordered_edges.append(edge)
            ordered_faces.append(current)
        if current != start or len(set(ordered_faces[:-1])) != len(edges):
            raise ArithmeticError("Bond did not yield a simple dual cycle")
        return {"edges": ordered_edges, "faces": ordered_faces}


def decide_ball_pattern(pattern: BallPattern) -> dict:
    """Decide essentiality. Complexity O(E^3(V+E)) combinatorial operations."""
    components = pattern.components()
    total = len(components) + pattern.circle_components
    base = {"ambient_manifold_assumption": "known-3-ball",
            "vertices": len(pattern.rotations), "edges": pattern.edge_count,
            "pattern_components": total}
    if total > 1:
        return {**base, "essential": False,
                "certificate": {"kind": "disconnected-pattern", "components": total}}
    if not pattern.rotations:
        return {**base, "essential": True, "certificate": None,
                "reason": "Empty pattern or one vertex-free circle"}
    for k in (1, 2, 3):
        for edges in combinations(range(pattern.edge_count), k):
            parts = pattern.components(frozenset(edges))
            if len(parts) != 2:
                continue  # Smaller cuts have already been examined.
            shore = min(parts, key=lambda x: (len(x), tuple(sorted(x))))
            if k == 3 and len(shore) == 1:
                continue  # This only cuts off an allowed tripod.
            cut = pattern.cut_edges(shore)
            if len(cut) != k:
                continue  # Supersets of an already handled smaller cut.
            certificate = {"kind": "violating-bond", "shore": sorted(shore),
                           "cut_edges": list(cut), "dual_cycle": pattern.dual_cycle(cut)}
            if not verify_violation(pattern, certificate):
                raise ArithmeticError("Internal boundary-pattern certificate failure")
            return {**base, "essential": False, "certificate": certificate}
    return {**base, "essential": True, "certificate": None,
            "reason": "No 1- or 2-edge bond and no nontrivial 3-edge bond"}


def verify_violation(pattern: BallPattern, certificate: object) -> bool:
    """Check a negative witness without searching over edge subsets."""
    if not isinstance(certificate, dict):
        return False
    kind = certificate.get("kind")
    if kind == "disconnected-pattern":
        actual = len(pattern.components()) + pattern.circle_components
        return actual > 1 and certificate.get("components") == actual
    if kind != "violating-bond" or pattern.circle_components:
        return False
    raw_shore = certificate.get("shore")
    if not isinstance(raw_shore, list) or any(type(v) is not int for v in raw_shore):
        return False
    shore = frozenset(raw_shore)
    if raw_shore != sorted(shore):
        return False
    n = len(pattern.rotations)
    if not 0 < len(shore) < n or any(v < 0 or v >= n for v in shore):
        return False
    cut = pattern.cut_edges(shore)
    if not 1 <= len(cut) <= 3 or list(cut) != certificate.get("cut_edges"):
        return False
    parts = pattern.components(frozenset(cut))
    if len(parts) != 2 or shore not in parts:
        return False
    if len(cut) == 3 and min(len(p) for p in parts) == 1:
        return False
    return certificate.get("dual_cycle") == pattern.dual_cycle(cut)
