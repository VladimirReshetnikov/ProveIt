"""Compressed cohomology-dual normal surfaces in finite 3-manifold triangulations.

This implements one algebraic building block, not the quasipolynomial hierarchy.
It does not cut manifolds, perform pattern compression, or find Cheeger regions.
All vertices are finite: ideal triangulations must first be truncated elsewhere.
"""
from __future__ import annotations
from collections import defaultdict, deque
from dataclasses import dataclass
from itertools import combinations
from .algebra import integer_nullspace
from .diagram import DSU

EDGES = tuple(combinations(range(4), 2))
EDGE_INDEX = {pair: i for i, pair in enumerate(EDGES)}
# Quad j separates QUAD_SIDES[j] from its complement.
QUAD_SIDES = (frozenset((0, 1)), frozenset((0, 2)), frozenset((0, 3)))
FaceGluing = tuple[int, tuple[int, int, int, int]] | None


def permutation_sign(p: tuple[int, ...]) -> int:
    return -1 if sum(p[i] > p[j] for i in range(len(p))
                     for j in range(i + 1, len(p))) % 2 else 1


class SignedDSU:
    """An oriented generator at x equals sign[x] times its parent's generator."""
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.sign = [1] * n
        self.size = [1] * n

    def find(self, x: int) -> tuple[int, int]:
        current, sign, path = x, 1, []
        while self.parent[current] != current:
            path.append(current)
            sign *= self.sign[current]
            current = self.parent[current]
        root, accumulated = current, 1
        for vertex in reversed(path):
            accumulated *= self.sign[vertex]
            self.parent[vertex], self.sign[vertex] = root, accumulated
        return root, sign

    def union(self, a: int, b: int, relation: int) -> None:
        """Impose a = relation*b, rejecting an edge identified to its reverse."""
        if type(relation) is not int or relation not in (-1, 1):
            raise ValueError("relation must be +1 or -1")
        ra, sa = self.find(a)
        rb, sb = self.find(b)
        relation *= sa * sb
        if ra == rb:
            if relation != 1:
                raise ValueError('An edge is identified to itself with reversed orientation')
            return
        if self.size[ra] < self.size[rb]:
            ra, rb = rb, ra  # inverse sign equals sign
        self.parent[rb], self.sign[rb] = ra, relation
        self.size[ra] += self.size[rb]


@dataclass(frozen=True)
class NormalSurface:
    cocycle: tuple[int, ...]
    coordinates: tuple[tuple[int, int, int, int, int, int, int], ...]
    euler_characteristic: int

    @property
    def disc_count(self) -> int:
        return sum(sum(row) for row in self.coordinates)

    @property
    def coordinate_bits(self) -> int:
        return sum(max(1, x.bit_length()) for row in self.coordinates for x in row)

    def as_json(self) -> dict:
        return {
            'edge_cocycle': list(self.cocycle),
            'normal_coordinates': [list(row) for row in self.coordinates],
            'coordinate_order': 'tri0,tri1,tri2,tri3,quad01|23,quad02|13,quad03|12',
            'euler_characteristic': self.euler_characteristic,
            'disc_count': self.disc_count,
            'coordinate_bits': self.coordinate_bits,
            'connectedness': 'not computed',
            'role': 'cohomology-dual surface only; not a bounded-genus hierarchy step',
        }


class Triangulation:
    """Finite, orientable, compact 3-manifold triangulation by face identifications.

    `gluings[t][f]` is None for a boundary face, or (u,p), where p is a
    permutation of vertices 0..3 carrying face f to face p[f] of tetrahedron u.
    Every pairing must also occur reciprocally. Distinct faces of the same
    tetrahedron may be paired; a face cannot be paired to itself.

    Validation includes orientability, no reversed edge identifications, and
    sphere/disk vertex links. Positive-genus ideal vertices are rejected.
    """
    def __init__(self, gluings: list | tuple):
        if not isinstance(gluings, (list, tuple)) or not gluings:
            raise ValueError('At least one tetrahedron is required')
        n = len(gluings)
        converted = []
        for row in gluings:
            if not isinstance(row, (list, tuple)) or len(row) != 4:
                raise ValueError('Each tetrahedron must specify four faces')
            converted_row = []
            for gluing in row:
                if gluing is None:
                    converted_row.append(None)
                    continue
                if not isinstance(gluing, (list, tuple)) or len(gluing) != 2:
                    raise ValueError('A gluing is (tetrahedron, permutation), or None')
                target, p = gluing
                if type(target) is not int or not 0 <= target < n:
                    raise ValueError('Invalid target tetrahedron')
                if not isinstance(p, (list, tuple)) or len(p) != 4:
                    raise ValueError('A gluing permutation must have length four')
                if any(type(v) is not int for v in p) or sorted(p) != list(range(4)):
                    raise ValueError('A gluing must give a permutation of vertices 0..3')
                converted_row.append((target, tuple(p)))
            converted.append(tuple(converted_row))
        self.gluings = tuple(converted)
        self.tetrahedra = n
        for t, row in enumerate(self.gluings):
            for f, gluing in enumerate(row):
                if gluing is None:
                    continue
                u, p = gluing
                if (u, p[f]) == (t, f):
                    raise ValueError('A face cannot be paired to itself')
                inverse = tuple(p.index(v) for v in range(4))
                if self.gluings[u][p[f]] != (t, inverse):
                    raise ValueError('Face identifications must be reciprocal')
        self._validate_orientability()
        vertices, edges = DSU(4 * n), SignedDSU(6 * n)
        for t, f, u, p in self.pairings():
            face = [v for v in range(4) if v != f]
            for v in face:
                vertices.union(4 * t + v, 4 * u + p[v])
            for a, b in combinations(face, 2):
                c, d = p[a], p[b]
                edges.union(6 * t + EDGE_INDEX[a, b],
                            6 * u + EDGE_INDEX[tuple(sorted((c, d)))],
                            1 if c < d else -1)
        self.vertex_classes = tuple(vertices.find(i) for i in range(4 * n))
        edge_data = [edges.find(i) for i in range(6 * n)]
        roots = sorted({root for root, _ in edge_data})
        indices = {root: i for i, root in enumerate(roots)}
        self.edge_map = tuple((indices[root], sign) for root, sign in edge_data)
        self.edge_count = len(roots)
        self.edge_endpoints = tuple(
            (self.vertex_classes[4 * (root // 6) + EDGES[root % 6][0]],
             self.vertex_classes[4 * (root // 6) + EDGES[root % 6][1]])
            for root in roots)
        self.vertex_links = self._validate_vertex_links()

    def pairings(self):
        """Each paired face exactly once."""
        for t, row in enumerate(self.gluings):
            for f, gluing in enumerate(row):
                if gluing is not None:
                    u, p = gluing
                    if (t, f) < (u, p[f]):
                        yield t, f, u, p

    def unique_faces(self):
        for t, row in enumerate(self.gluings):
            for f, gluing in enumerate(row):
                if gluing is None or (t, f) < (gluing[0], gluing[1][f]):
                    yield t, f

    def _validate_orientability(self) -> None:
        signs = {}
        for start in range(self.tetrahedra):
            if start in signs:
                continue
            signs[start] = 1
            queue = deque([start])
            while queue:
                t = queue.popleft()
                for gluing in self.gluings[t]:
                    if gluing is None:
                        continue
                    u, p = gluing
                    expected = -permutation_sign(p) * signs[t]
                    if u in signs:
                        if signs[u] != expected:
                            raise ValueError('The triangulation is not orientable')
                    else:
                        signs[u] = expected
                        queue.append(u)

    def _validate_vertex_links(self) -> dict[int, dict[str, int]]:
        # A corner of a vertex-link triangle is indexed by (tet, v, w), w!=v.
        # A side is indexed by (tet, v, f), f!=v (face f contains v).
        local = [(t, v, w) for t in range(self.tetrahedra)
                 for v in range(4) for w in range(4) if w != v]
        index = {key: i for i, key in enumerate(local)}
        corners, sides = DSU(len(local)), DSU(len(local))
        for t, f, u, p in self.pairings():
            for v in range(4):
                if v == f:
                    continue
                sides.union(index[t, v, f], index[u, p[v], p[f]])
                for w in range(4):
                    if w not in (v, f):
                        corners.union(index[t, v, w], index[u, p[v], p[w]])
        vertices = defaultdict(set)
        edges = defaultdict(set)
        faces = defaultdict(int)
        boundary = defaultdict(int)
        for i, (t, v, w) in enumerate(local):
            root = self.vertex_classes[4 * t + v]
            vertices[root].add(corners.find(i))
            edges[root].add(sides.find(i))
            if self.gluings[t][w] is None:
                boundary[root] += 1
        for vertex in self.vertex_classes:
            faces[vertex] += 1
        answer = {}
        for vertex, count in faces.items():
            chi = len(vertices[vertex]) - len(edges[vertex]) + count
            expected = 1 if boundary[vertex] else 2
            if chi != expected:
                raise ValueError('A vertex link is not a sphere or disk; '
                                 'ideal or singular vertices are unsupported')
            answer[vertex] = {'vertices': len(vertices[vertex]),
                              'edges': len(edges[vertex]), 'triangles': count,
                              'boundary_edges': boundary[vertex], 'chi': chi}
        return answer

    def edge_value(self, cocycle: tuple[int, ...] | list[int],
                   tetrahedron: int, a: int, b: int) -> int:
        if a == b:
            return 0
        edge, sign = self.edge_map[6 * tetrahedron + EDGE_INDEX[tuple(sorted((a, b)))]]
        return (1 if a < b else -1) * sign * cocycle[edge]

    def cocycle_equations(self) -> list[list[int]]:
        equations = []
        for t in range(self.tetrahedra):
            for a, b, c in combinations(range(4), 3):
                row = [0] * self.edge_count
                for u, v, coefficient in ((a, b, 1), (b, c, 1), (a, c, -1)):
                    edge, sign = self.edge_map[6 * t + EDGE_INDEX[u, v]]
                    row[edge] += coefficient * sign
                equations.append(row)
        return equations

    def rational_cohomology_basis(self) -> list[tuple[int, ...]]:
        """Integral cocycles whose classes form a basis of H^1(M;Q).

        A maximal-tree gauge removes coboundaries. The output is NOT asserted
        to be a saturated integral cohomology basis.
        """
        vertices = sorted(set(self.vertex_classes))
        vertex_index = {v: i for i, v in enumerate(vertices)}
        forest, tree = DSU(len(vertices)), set()
        for i, (a, b) in enumerate(self.edge_endpoints):
            u, v = vertex_index[a], vertex_index[b]
            if forest.find(u) != forest.find(v):
                forest.union(u, v)
                tree.add(i)
        free = [i for i in range(self.edge_count) if i not in tree]
        matrix = [[row[i] for i in free] for row in self.cocycle_equations()]
        answer = []
        for kernel_vector in integer_nullspace(matrix, len(free)):
            vector = [0] * self.edge_count
            for i, value in zip(free, kernel_vector):
                vector[i] = value
            answer.append(tuple(vector))
        return answer

    @staticmethod
    def face_arcs(coordinates: tuple[int, ...] | list[int], face: int) -> dict[int, int]:
        vertices = set(range(4)) - {face}
        arcs = {v: coordinates[v] for v in vertices}
        for q, side in enumerate(QUAD_SIDES):
            cut = vertices & side
            singleton = cut if len(cut) == 1 else vertices - cut
            arcs[next(iter(singleton))] += coordinates[4 + q]
        return arcs

    def check_normal_coordinates(self, coordinates: tuple | list) -> None:
        if len(coordinates) != self.tetrahedra:
            raise ValueError('One normal-coordinate row is required per tetrahedron')
        for row in coordinates:
            if len(row) != 7 or any(type(x) is not int or x < 0 for x in row):
                raise ValueError('Normal coordinates must be seven nonnegative integers')
            if sum(x != 0 for x in row[4:]) > 1:
                raise ValueError('Quadrilateral compatibility is violated')
        for t, f, u, p in self.pairings():
            left = self.face_arcs(coordinates[t], f)
            right = self.face_arcs(coordinates[u], p[f])
            if any(left[v] != right[p[v]] for v in left):
                raise ValueError('Normal matching equations are violated')

    def dual_surface(self, cocycle: tuple[int, ...] | list[int]) -> NormalSurface:
        """Take half-integral levels of local integer vertex heights, compressed.

        No iteration depends on the magnitude of the cocycle coordinates.
        The result can have many components and arbitrarily high complexity.
        """
        if len(cocycle) != self.edge_count or any(type(x) is not int for x in cocycle):
            raise ValueError('One integer is required for each oriented global edge')
        for row in self.cocycle_equations():
            if sum(a * b for a, b in zip(row, cocycle)):
                raise ValueError('The cochain is not closed on every triangular face')
        coordinates = []
        for t in range(self.tetrahedra):
            heights = [0] + [self.edge_value(cocycle, t, 0, v) for v in range(1, 4)]
            order = sorted(range(4), key=lambda v: (heights[v], v))
            row = [0] * 7
            for cut in range(1, 4):
                count = heights[order[cut]] - heights[order[cut - 1]]
                if cut == 1:
                    row[order[0]] += count
                elif cut == 3:
                    row[order[3]] += count
                else:
                    lower = frozenset(order[:2])
                    partition = lower if 0 in lower else frozenset(range(4)) - lower
                    row[4 + QUAD_SIDES.index(partition)] += count
            coordinates.append(tuple(row))
        self.check_normal_coordinates(coordinates)
        discs = sum(sum(row) for row in coordinates)
        arcs = sum(sum(self.face_arcs(coordinates[t], f).values())
                   for t, f in self.unique_faces())
        points = sum(abs(x) for x in cocycle)
        return NormalSurface(tuple(cocycle), tuple(coordinates), points - arcs + discs)


def one_tetrahedron_ball() -> Triangulation:
    return Triangulation([[None, None, None, None]])


def one_tetrahedron_solid_torus() -> Triangulation:
    """The standard one-tetrahedron layered solid torus, with two boundary faces."""
    return Triangulation([[(0, (1, 2, 3, 0)), (0, (3, 0, 1, 2)), None, None]])
