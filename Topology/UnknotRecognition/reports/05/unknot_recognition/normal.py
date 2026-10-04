"""Compressed cocycle-dual normal surfaces in explicit simplicial 3-manifolds.

This kernel does not cut or normalize a hierarchy. It accepts ordinary finite
simplicial complexes, NOT generalized face-pairing/ideal triangulations. Integer
normal coordinates are never expanded into individual disks. A generated
surface may be disconnected; we do not pretend that Euler characteristic or a
primitive cohomology class proves connectedness.
"""
from __future__ import annotations

from collections import defaultdict
from itertools import combinations
from typing import Sequence

from .algebra import DisjointSet, rational_nullspace


QUAD_PARTITIONS = ((0, 1), (0, 2), (0, 3))


def _connected(vertices: set[int], edges: Sequence[tuple[int, int]]) -> bool:
    if not vertices:
        return True
    adjacency = {v: [] for v in vertices}
    for a, b in edges:
        adjacency[a].append(b)
        adjacency[b].append(a)
    seen = {next(iter(vertices))}
    stack = list(seen)
    while stack:
        for vertex in adjacency[stack.pop()]:
            if vertex not in seen:
                seen.add(vertex)
                stack.append(vertex)
    return seen == vertices


class SimplicialTriangulation:
    def __init__(self, tetrahedra: Sequence[Sequence[int]]):
        raw = tuple(tuple(tet) for tet in tetrahedra)
        if not raw or any(len(tet) != 4 or len(set(tet)) != 4 for tet in raw):
            raise ValueError("Provide at least one tetrahedron with four distinct vertices.")
        if any(type(v) is not int for tet in raw for v in tet):
            raise ValueError("Vertex labels must be integers.")
        self.tetrahedra = tuple(sorted(tuple(sorted(tet)) for tet in raw))
        if len(set(self.tetrahedra)) != len(self.tetrahedra):
            raise ValueError("Duplicate tetrahedra are not allowed.")
        self.vertices = tuple(sorted({v for tet in self.tetrahedra for v in tet}))
        self.edges = tuple(sorted({edge for tet in self.tetrahedra for edge in combinations(tet, 2)}))
        self.edge_index = {edge: i for i, edge in enumerate(self.edges)}
        self.face_incidence: dict[tuple[int, int, int], list[tuple[int, int]]] = defaultdict(list)
        for i, tet in enumerate(self.tetrahedra):
            for omitted in range(4):
                face = tet[:omitted] + tet[omitted + 1:]
                self.face_incidence[face].append((i, (-1) ** omitted))
        if any(len(incidence) > 2 for incidence in self.face_incidence.values()):
            raise ValueError("More than two tetrahedra meet at a face.")
        if not _connected(set(self.vertices), self.edges):
            raise ValueError("The triangulation must be connected.")
        self._check_orientable()
        for vertex in self.vertices:
            link = [tuple(v for v in tet if v != vertex)
                    for tet in self.tetrahedra if vertex in tet]
            self._check_sphere_or_disk(link)
        self.faces = tuple(sorted(self.face_incidence))

    def _check_orientable(self) -> None:
        adjacency: list[list[tuple[int, int]]] = [[] for _ in self.tetrahedra]
        for incidence in self.face_incidence.values():
            if len(incidence) == 2:
                (a, sa), (b, sb) = incidence
                relation = -sa * sb
                adjacency[a].append((b, relation))
                adjacency[b].append((a, relation))
        orientations: dict[int, int] = {}
        for root in range(len(adjacency)):
            if root in orientations:
                continue
            orientations[root] = 1
            stack = [root]
            while stack:
                vertex = stack.pop()
                for other, relation in adjacency[vertex]:
                    target = orientations[vertex] * relation
                    if other in orientations:
                        if orientations[other] != target:
                            raise ValueError("The 3-complex is non-orientable.")
                    else:
                        orientations[other] = target
                        stack.append(other)

    @staticmethod
    def _check_sphere_or_disk(triangles: list[tuple[int, ...]]) -> None:
        vertices = {v for triangle in triangles for v in triangle}
        incidence: dict[tuple[int, int], int] = defaultdict(int)
        for triangle in triangles:
            for edge in combinations(triangle, 2):
                incidence[edge] += 1
        if any(count > 2 for count in incidence.values()) or not _connected(vertices, tuple(incidence)):
            raise ValueError("A vertex link is not a connected surface.")
        for vertex in vertices:
            fan_edges = [tuple(v for v in triangle if v != vertex)
                         for triangle in triangles if vertex in triangle]
            fan_vertices = {v for edge in fan_edges for v in edge}
            degree: dict[int, int] = defaultdict(int)
            for a, b in fan_edges:
                degree[a] += 1
                degree[b] += 1
            ends = sum(value == 1 for value in degree.values())
            if (not _connected(fan_vertices, fan_edges) or ends not in (0, 2)
                    or any(value not in (1, 2) for value in degree.values())):
                raise ValueError("A vertex-link fan is neither a circle nor an interval.")
        boundary = [edge for edge, count in incidence.items() if count == 1]
        chi = len(vertices) - len(incidence) + len(triangles)
        if not boundary:
            if chi != 2:
                raise ValueError("An interior vertex link is not a sphere.")
        else:
            boundary_vertices = {v for edge in boundary for v in edge}
            degrees = defaultdict(int)
            for a, b in boundary:
                degrees[a] += 1
                degrees[b] += 1
            if (chi != 1 or not _connected(boundary_vertices, boundary)
                    or any(degrees[v] != 2 for v in boundary_vertices)):
                raise ValueError("A boundary vertex link is not a disk.")

    def cocycle_basis(self) -> tuple[tuple[int, ...], ...]:
        """A Q-basis of H^1 represented by integral, spanning-tree-zero cocycles."""
        index = {v: i for i, v in enumerate(self.vertices)}
        dsu = DisjointSet(len(index))
        tree = set()
        for i, (a, b) in enumerate(self.edges):
            if dsu.find(index[a]) != dsu.find(index[b]):
                dsu.union(index[a], index[b])
                tree.add(i)
        free_edges = [i for i in range(len(self.edges)) if i not in tree]
        free_index = {edge: i for i, edge in enumerate(free_edges)}
        equations = []
        for a, b, c in self.faces:
            row = [0] * len(free_edges)
            for edge, sign in (((a, b), 1), ((b, c), 1), ((a, c), -1)):
                i = self.edge_index[edge]
                if i in free_index:
                    row[free_index[i]] += sign
            equations.append(row)
        basis = rational_nullspace(equations, len(free_edges))
        result = []
        for vector in basis:
            expanded = [0] * len(self.edges)
            for index, edge in enumerate(free_edges):
                expanded[edge] = vector[index]
            result.append(tuple(expanded))
        return tuple(result)

    def check_cocycle(self, cocycle: Sequence[int]) -> None:
        if len(cocycle) != len(self.edges) or any(type(x) is not int for x in cocycle):
            raise ValueError("One integer coefficient is required per oriented global edge.")
        for a, b, c in self.faces:
            if (cocycle[self.edge_index[a, b]] + cocycle[self.edge_index[b, c]]
                    != cocycle[self.edge_index[a, c]]):
                raise ValueError("The cochain does not close around each triangle.")

    def normal_from_cocycle(self, cocycle: Sequence[int]) -> tuple[tuple[int, ...], ...]:
        """Half-integer levels of affine local lifts of a map M -> R/Z."""
        self.check_cocycle(cocycle)
        rows = []
        for tet in self.tetrahedra:
            heights = [0] + [cocycle[self.edge_index[tet[0], v]] for v in tet[1:]]
            order = sorted(range(4), key=lambda i: (heights[i], i))
            row = [0] * 7
            for k in (1, 2, 3):
                gap = heights[order[k]] - heights[order[k - 1]]
                if k == 1:
                    disk_type = order[0]
                elif k == 3:
                    disk_type = order[-1]
                else:
                    pair = set(order[:2])
                    if 0 not in pair:
                        pair = set(range(4)) - pair
                    disk_type = 4 + QUAD_PARTITIONS.index(tuple(sorted(pair)))
                row[disk_type] += gap
            rows.append(tuple(row))
        result = tuple(rows)
        summary = self.normal_summary(result)
        if summary["edge_intersections"] != [abs(x) for x in cocycle]:
            raise ArithmeticError("Dual surface has inconsistent edge-intersection counts.")
        return result

    @staticmethod
    def _partition(disk_type: int) -> set[int]:
        return {disk_type} if disk_type < 4 else set(QUAD_PARTITIONS[disk_type - 4])

    def normal_summary(self, coordinates: Sequence[Sequence[int]]) -> dict:
        rows = tuple(tuple(row) for row in coordinates)
        if len(rows) != len(self.tetrahedra) or any(len(row) != 7 for row in rows):
            raise ValueError("Each tetrahedron requires four triangle and three quad counts.")
        if any(type(x) is not int or x < 0 for row in rows for x in row):
            raise ValueError("Normal coordinates must be non-negative integers.")
        if any(sum(x != 0 for x in row[4:]) > 1 for row in rows):
            raise ValueError("Incompatible quadrilateral types in one tetrahedron.")
        face_arcs: dict[tuple[int, int, int], list[tuple[int, ...]]] = defaultdict(list)
        edge_counts: dict[tuple[int, int], int] = {}
        total_arcs = sum(3 * sum(row[:4]) + 4 * sum(row[4:]) for row in rows)
        disks = sum(sum(row) for row in rows)
        for tet, row in zip(self.tetrahedra, rows):
            for i, j in combinations(range(4), 2):
                count = sum(number for disk_type, number in enumerate(row)
                            if (i in self._partition(disk_type)) != (j in self._partition(disk_type)))
                edge = (tet[i], tet[j])
                if edge in edge_counts and edge_counts[edge] != count:
                    raise ValueError("Edge-intersection counts disagree between tetrahedra.")
                edge_counts[edge] = count
            for omitted in range(4):
                indices = [i for i in range(4) if i != omitted]
                face = tuple(tet[i] for i in indices)
                arcs = [0] * 3
                for disk_type, number in enumerate(row):
                    part = self._partition(disk_type)
                    inside = [i for i in indices if i in part]
                    outside = [i for i in indices if i not in part]
                    if inside and outside:
                        singleton = inside[0] if len(inside) == 1 else outside[0]
                        arcs[indices.index(singleton)] += number
                face_arcs[face].append(tuple(arcs))
        boundary_arcs = 0
        for face, copies in face_arcs.items():
            if len(copies) == 2:
                if copies[0] != copies[1]:
                    raise ValueError("The normal matching equations fail across a face.")
            else:
                boundary_arcs += sum(copies[0])
        if (total_arcs + boundary_arcs) % 2:
            raise ArithmeticError("Non-integral normal cell-edge count.")
        surface_edges = (total_arcs + boundary_arcs) // 2
        surface_vertices = sum(edge_counts.values())
        return {
            "disks": disks, "surface_cell_vertices": surface_vertices,
            "surface_cell_edges": surface_edges,
            "euler_characteristic": surface_vertices - surface_edges + disks,
            "boundary_normal_arcs": boundary_arcs,
            "edge_intersections": [edge_counts[e] for e in self.edges],
            "coordinate_bits": sum(max(1, x.bit_length()) for row in rows for x in row),
            "connectedness": "not computed",
        }


def solid_torus_example(segments: int = 3) -> SimplicialTriangulation:
    """The staircase triangulation of (a triangle) x (a polygonal circle)."""
    if type(segments) is not int or segments < 3:
        raise ValueError("At least three circle segments are required.")
    tetrahedra = []
    for i in range(segments):
        a, b = sorted((i, (i + 1) % segments))
        a0, a1, a2 = (3 * a + j for j in range(3))
        b0, b1, b2 = (3 * b + j for j in range(3))
        tetrahedra.extend(((a0, b0, b1, b2), (a0, a1, b1, b2), (a0, a1, a2, b2)))
    return SimplicialTriangulation(tetrahedra)
