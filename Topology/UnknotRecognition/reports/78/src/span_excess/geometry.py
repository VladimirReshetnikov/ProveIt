"""Genuine simplicial solid-torus fixtures and a literal normal-polygon oracle.

These product fixtures are not a native diagram-to-exterior implementation.
The oracle intentionally expands normal pieces and is used only in tests.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
from collections import defaultdict
from .prepare import prepare_model


class DSU:
    def __init__(self):
        self.parent = {}

    def find(self, x):
        p = self.parent
        p.setdefault(x, x)
        while x != p[x]:
            p[x] = p[p[x]]
            x = p[x]
        return x

    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a != b:
            self.parent[b] = a


@dataclass(frozen=True)
class SolidTorus:
    segments: int
    disk_vertices: int
    tetrahedra: tuple[tuple[int, ...], ...]
    heights: tuple[tuple[int, ...], ...]
    generator_edges: tuple[tuple[int, int], ...]

    @property
    def n(self):
        return self.segments*self.disk_vertices

    def incidence(self):
        faces = defaultdict(list)
        edges = {}
        for t, (vs, hs) in enumerate(zip(self.tetrahedra, self.heights)):
            for inds in combinations(range(4), 3):
                key = tuple(sorted(vs[i] for i in inds))
                faces[key].append((t, inds))
            for i, j in combinations(range(4), 2):
                a, b, c = vs[i], vs[j], hs[j]-hs[i]
                if a > b:
                    a, b, c = b, a, -c
                key = (a, b)
                if key in edges and edges[key] != c:
                    raise ValueError("incoherent product edge heights")
                edges[key] = c
        if any(len(inc) not in (1, 2) for inc in faces.values()):
            raise ValueError("nonmanifold product face")
        degree = defaultdict(int)
        for face in faces:
            for edge in combinations(face, 2):
                degree[edge] += 1
        return faces, edges, degree

    def model(self):
        faces, edge_values, degree = self.incidence()
        weighted = [(a, b, c, degree[(a, b)]-2)
                    for (a, b), c in sorted(edge_values.items())]
        return prepare_model(self.n, self.tetrahedra, self.heights, weighted)

    def to_dict(self):
        from dataclasses import asdict
        return asdict(self)


def product_solid_torus(segments=3, central_vertex=False):
    if type(segments) is not int or segments < 3:
        raise ValueError("at least three circle edges are required")
    dv = 4 if central_vertex else 3
    triangles = ((0, 1, 3), (1, 2, 3), (0, 2, 3)) if central_vertex else ((0, 1, 2),)
    tets, heights = [], []
    for s in range(segments):
        nxt = (s+1) % segments
        for a, b, c in triangles:
            bottom = [s*dv+a, s*dv+b, s*dv+c]
            top = [nxt*dv+a, nxt*dv+b, nxt*dv+c]
            # Staircase triangulation of the product of an edge and a triangle.
            patterns = ((bottom[0], bottom[1], bottom[2], top[2]),
                        (bottom[0], bottom[1], top[1], top[2]),
                        (bottom[0], top[0], top[1], top[2]))
            masks = ((0, 0, 0, 1), (0, 0, 1, 1), (0, 1, 1, 1))
            for tet, mask in zip(patterns, masks):
                tets.append(tet)
                heights.append(tuple(x if s == segments-1 else 0 for x in mask))
    generator = tuple((s*dv, ((s+1) % segments)*dv) for s in range(segments))
    return SolidTorus(segments, dv, tuple(tets), tuple(heights), generator)


def expand_surface(geom: SolidTorus, potential, max_pieces=100000):
    """Independent global polygon gluing and per-component Euler/class counts."""
    if len(potential) != geom.n or any(type(x) is not int for x in potential):
        raise ValueError("invalid potential")
    faces, edges, degree = geom.incidence()
    adjusted = [tuple(h+potential[v] for v, h in zip(vs, hs))
                for vs, hs in zip(geom.tetrahedra, geom.heights)]
    total = sum(max(a)-min(a) for a in adjusted)
    if total > max_pieces:
        raise ValueError("literal oracle piece cap exceeded")
    polygon_vertices, polygon_edges, edge_incidence = [], [], defaultdict(list)
    dsu = DSU()
    for t, (vs, a) in enumerate(zip(geom.tetrahedra, adjusted)):
        for level in range(min(a), max(a)):
            pid = len(polygon_vertices)
            dsu.find(pid)
            points = {}
            for i, j in combinations(range(4), 2):
                if min(a[i], a[j]) <= level < max(a[i], a[j]):
                    first, second = (i, j) if vs[i] < vs[j] else (j, i)
                    index = level-a[first] if a[second] > a[first] else a[first]-level-1
                    points[(i, j)] = ((vs[first], vs[second]), index)
            if len(points) not in (3, 4):
                raise ArithmeticError("a normal polygon must have three or four sides")
            arcs = []
            for inds in combinations(range(4), 3):
                ends = [point for (i, j), point in points.items() if i in inds and j in inds]
                if len(ends) == 2:
                    face = tuple(sorted(vs[i] for i in inds))
                    arc = (face, tuple(sorted(ends)))
                    arcs.append(arc)
                    edge_incidence[arc].append(pid)
                elif ends:
                    raise ArithmeticError("invalid triangular face intersection")
            polygon_vertices.append(set(points.values()))
            polygon_edges.append(set(arcs))
    for arc, inc in edge_incidence.items():
        if len(inc) != len(faces[arc[0]]):
            raise ArithmeticError("surface face matching failed")
        for pid in inc[1:]:
            dsu.union(inc[0], pid)
    records = {}
    for pid, (verts, arcs) in enumerate(zip(polygon_vertices, polygon_edges)):
        root = dsu.find(pid)
        r = records.setdefault(root, {'vertices': set(), 'edges': set(), 'polygons': []})
        r['vertices'].update(verts)
        r['edges'].update(arcs)
        r['polygons'].append(pid)
    answer = []
    for r in records.values():
        boundary = [arc for arc in r['edges'] if len(faces[arc[0]]) == 1]
        boundary_dsu, valence = DSU(), defaultdict(int)
        for _, (a, b) in boundary:
            boundary_dsu.union(a, b)
            valence[a] += 1
            valence[b] += 1
        if any(x != 2 for x in valence.values()):
            raise ArithmeticError("boundary is not a disjoint union of circles")
        bc = len({boundary_dsu.find(x) for x in valence})
        signed_class = 0
        for u, v in geom.generator_edges:
            edge = tuple(sorted((u, v)))
            c = edges[edge]+potential[edge[1]]-potential[edge[0]]
            sign = (1 if c > 0 else -1 if c < 0 else 0)*(1 if u < v else -1)
            signed_class += sign*sum(point[0] == edge for point in r['vertices'])
        chi = len(r['vertices'])-len(r['edges'])+len(r['polygons'])
        twice_genus = 2-bc-chi
        if twice_genus < 0 or twice_genus % 2:
            raise ArithmeticError("invalid orientable component Euler characteristic")
        answer.append({'pieces': len(r['polygons']), 'vertices': len(r['vertices']),
                       'edges': len(r['edges']), 'euler': chi, 'boundary': bc,
                       'genus': twice_genus//2, 'class': signed_class})
    return {'pieces': total, 'euler': sum(r['euler'] for r in answer),
            'components': sorted(answer, key=lambda r: (r['class'], r['pieces'], r['euler']))}
