"""Essential boundary-pattern testing on a KNOWN 3-ball.

This polynomial-time module finds violating dual cycles of length <=3.
It does not certify that an arbitrary 3-manifold is a ball, and it does
not transport the resulting disk through a hierarchy.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from itertools import combinations
from .diagram import DSU, permutation_cycles


@dataclass(frozen=True)
class PatternResult:
    essential: bool
    reason: str
    dual_cycle: tuple[int, ...] = ()
    crossed_edges: tuple[tuple[int, int], ...] = ()

    def as_json(self) -> dict:
        return {'essential': self.essential, 'reason': self.reason,
                'dual_cycle': list(self.dual_cycle),
                'crossed_primal_edges': [list(e) for e in self.crossed_edges],
                'precondition': 'the ambient manifold is a 3-ball',
                'not_supplied': 'a transported compression disk in an earlier manifold'}


class BallPattern:
    """A spherical trivalent rotation system plus isolated circle components.

    Vertex i has outgoing darts 3*i,3*i+1,3*i+2 in cyclic order.
    `edge_pairs` is a perfect matching of these darts; loops and multiple
    edges are allowed. For disconnected graphs, rotations need not encode
    nesting: essentiality is false regardless of that nesting.
    """
    def __init__(self, vertices: int, edge_pairs: list | tuple, *, circles: int = 0):
        if type(vertices) is not int or vertices < 0:
            raise ValueError('vertices must be a nonnegative integer')
        if type(circles) is not int or circles < 0:
            raise ValueError('circles must be a nonnegative integer')
        if not isinstance(edge_pairs, (list, tuple)):
            raise ValueError('edge_pairs must be a list of pairs')
        pairs = []
        for pair in edge_pairs:
            if not isinstance(pair, (list, tuple)) or len(pair) != 2:
                raise ValueError('Each edge must consist of two darts')
            if any(type(d) is not int or not 0 <= d < 3 * vertices for d in pair):
                raise ValueError('Dart outside the rotation system')
            pairs.append(tuple(pair))
        if sorted(d for pair in pairs for d in pair) != list(range(3 * vertices)):
            raise ValueError('Every dart must occur in exactly one edge')
        self.vertices, self.circles = vertices, circles
        self.edge_pairs = tuple(pairs)
        alpha = [0] * (3 * vertices)
        components = DSU(vertices)
        for a, b in pairs:
            alpha[a], alpha[b] = b, a
            components.union(a // 3, b // 3)
        self.alpha = tuple(alpha)
        face_next = [3 * (alpha[d] // 3) + (alpha[d] + 1) % 3
                     for d in range(3 * vertices)]
        self.faces = tuple(permutation_cycles(face_next))
        self.face_of = {}
        for f, face in enumerate(self.faces):
            for d in face:
                self.face_of[d] = f
        counts = defaultdict(lambda: [0, 0, 0])
        for v in range(vertices):
            counts[components.find(v)][0] += 1
        for a, _ in pairs:
            counts[components.find(a // 3)][1] += 1
        for face in self.faces:
            counts[components.find(face[0] // 3)][2] += 1
        if any(v - e + f != 2 for v, e, f in counts.values()):
            raise ValueError('The rotation system is not spherical')
        self.graph_components = len(counts)

    def test_essential(self) -> PatternResult:
        components = self.graph_components + self.circles
        if components == 0:
            return PatternResult(True, 'empty pattern')
        if components != 1:
            return PatternResult(False, 'disconnected pattern; a disjoint curve separates it')
        if self.circles == 1:
            return PatternResult(True, 'one simple closed curve')
        # Build the embedded dual. Loops and parallel edges give cycles of
        # length 1 and 2 whose crossed primal edges are explicitly recorded.
        dual_edges: dict[tuple[int, int], tuple[int, int]] = {}
        adjacency = [set() for _ in self.faces]
        for a, b in self.edge_pairs:
            u, v = self.face_of[a], self.face_of[b]
            if u == v:
                return PatternResult(False, 'dual loop', (u,), ((a, b),))
            key = tuple(sorted((u, v)))
            if key in dual_edges:
                return PatternResult(False, 'two distinct dual edges with the same endpoints',
                                     key, (dual_edges[key], (a, b)))
            dual_edges[key] = (a, b)
            adjacency[u].add(v)
            adjacency[v].add(u)
        # Each primal vertex determines a triangular dual face. In a simple
        # spherical triangulation a triangle is non-violating iff it is facial
        # on at least one side. This includes the two-face K3 sphere.
        facial_triangles = {
            frozenset(self.face_of[3 * v + j] for j in range(3))
            for v in range(self.vertices)}
        for u in range(len(self.faces)):
            for v, w in combinations(sorted(x for x in adjacency[u] if x > u), 2):
                if w in adjacency[v] and frozenset((u, v, w)) not in facial_triangles:
                    cycle_edges = tuple(dual_edges[tuple(sorted(pair))]
                                        for pair in ((u, v), (v, w), (w, u)))
                    return PatternResult(False, 'non-facial triangular dual cycle',
                                         (u, v, w), cycle_edges)
        return PatternResult(True, 'all dual cycles of length at most three are non-violating')

    @classmethod
    def from_dual_triangles(cls, triangles: list | tuple) -> BallPattern:
        """Build a cubic primal pattern from oriented triangular faces of a sphere.

        Integer vertex names need not be consecutive. Every directed edge
        must occur once and its reverse once; sphere validation is automatic.
        Repeated unoriented faces are permitted for the two-face K3 sphere.
        """
        if not isinstance(triangles, (list, tuple)) or not triangles:
            raise ValueError('A nonempty list of oriented triangles is required')
        darts = {}
        for i, face in enumerate(triangles):
            if not isinstance(face, (list, tuple)) or len(face) != 3:
                raise ValueError('Each face must be a triangle')
            if any(type(v) is not int for v in face) or len(set(face)) != 3:
                raise ValueError('Three distinct integer vertex names are required')
            for j in range(3):
                edge = face[j], face[(j + 1) % 3]
                if edge in darts:
                    raise ValueError('A directed edge occurs in more than one triangle')
                darts[edge] = 3 * i + j
        pairs = []
        for (a, b), dart in darts.items():
            if (b, a) not in darts:
                raise ValueError('Each triangle edge must have an oppositely oriented partner')
            if a < b:
                pairs.append((dart, darts[b, a]))
        return cls(len(triangles), pairs)
