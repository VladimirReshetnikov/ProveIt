"""Validated geometry of supplied binary-encoded normal surfaces.

The manifold validator is adapted from report 36's normal_disk_certificate.py
at ProveIt 58ee11a97d5fd7f21647c57eefaf3ecc007931d6 (MIT-0).
This module adds general interval-orbit connectivity and topology. It supports
finite connected compact orientable tetrahedral triangulations with exactly
one torus boundary; it does not establish provenance from a knot diagram.
No normal disc, edge intersection point, or sheet is expanded.
"""

from collections import deque
from itertools import combinations
from .integer_codec import encoded_integer
from .interval_orbits import IntervalPairing


class NormalOrbitError(ValueError):
    """Malformed or unsupported triangulation or normal coordinates."""


_EDGES = tuple(combinations(range(4), 2))
_EDGE_INDEX = {edge: i for i, edge in enumerate(_EDGES)}
_DIRECTED = tuple((a, b) for a in range(4) for b in range(4) if a != b)
_DIRECTED_INDEX = {edge: i for i, edge in enumerate(_DIRECTED)}


def _edge(t, a, b):
    return 6 * t + _EDGE_INDEX[tuple(sorted((a, b)))]


def _directed(t, a, b):
    return 12 * t + _DIRECTED_INDEX[a, b]


def _quad(a, b):
    """Quadrilateral type disjoint from edge {a,b}."""
    if a == 0:
        return b - 1
    if b == 0:
        return a - 1
    return next(v - 1 for v in range(1, 4) if v not in (a, b))


class _UnionFind:
    def __init__(self, size):
        self.parent = list(range(size))
        self.size = [1] * size
        self.parity = [0] * size

    def find(self, x):
        parent = self.parent[x]
        if parent != x:
            root, parity = self.find(parent)
            self.parity[x] ^= parity
            self.parent[x] = root
        return self.parent[x], self.parity[x]

    def join(self, x, y, parity=0):
        x, px = self.find(x)
        y, py = self.find(y)
        if x == y:
            if px ^ py != parity:
                raise NormalOrbitError('a triangulation edge is identified with its reverse')
            return
        if self.size[x] < self.size[y]:
            x, y = y, x
            px, py = py, px
        self.parent[y] = x
        self.parity[y] = px ^ py ^ parity
        self.size[x] += self.size[y]


def _permutation_sign(permutation):
    inversions = sum(permutation[i] > permutation[j]
                     for i in range(4) for j in range(i + 1, 4))
    return -1 if inversions % 2 else 1


def _prepare(triangulation, check):
    """Validate the finite manifold and reconstruct every combinatorial datum."""
    check()
    if (type(triangulation) is not dict or set(triangulation) != {'tetrahedra'}
            or type(triangulation['tetrahedra']) is not list
            or not triangulation['tetrahedra']):
        raise NormalOrbitError('expected a nonempty tetrahedra array')
    tetrahedra = triangulation['tetrahedra']
    n = len(tetrahedra)
    for t, faces in enumerate(tetrahedra):
        check()
        if type(faces) is not list or len(faces) != 4:
            raise NormalOrbitError('each tetrahedron must have four face records')
        for f, record in enumerate(faces):
            if record is None:
                continue
            if (type(record) is not dict
                    or set(record) != {'tetrahedron', 'permutation'}
                    or type(record['tetrahedron']) is not int
                    or not 0 <= record['tetrahedron'] < n
                    or type(record['permutation']) is not list
                    or len(record['permutation']) != 4
                    or any(type(v) is not int for v in record['permutation'])
                    or set(record['permutation']) != set(range(4))):
                raise NormalOrbitError('invalid face pairing record')
            if record['tetrahedron'] == t and record['permutation'][f] == f:
                raise NormalOrbitError('a face cannot be paired with itself')
    pairs = []
    boundary_faces = []
    adjacency = [[] for _ in range(n)]
    for t, faces in enumerate(tetrahedra):
        check()
        for f, record in enumerate(faces):
            if record is None:
                boundary_faces.append((t, f))
                continue
            u, permutation = record['tetrahedron'], record['permutation']
            g = permutation[f]
            back = tetrahedra[u][g]
            if (back is None or back['tetrahedron'] != t
                    or any(back['permutation'][permutation[v]] != v
                           for v in range(4))):
                raise NormalOrbitError('face pairings must be reciprocal')
            adjacency[t].append((u, -_permutation_sign(permutation)))
            if (t, f) < (u, g):
                pairs.append((t, f, u, g, permutation))
    orientations = {0: 1}
    queue = deque([0])
    while queue:
        check()
        t = queue.popleft()
        for u, multiplier in adjacency[t]:
            value = multiplier * orientations[t]
            if u in orientations:
                if orientations[u] != value:
                    raise NormalOrbitError('triangulation is not orientable')
            else:
                orientations[u] = value
                queue.append(u)
    if len(orientations) != n:
        raise NormalOrbitError('triangulation is not connected through faces')

    vertices = _UnionFind(4 * n)
    edges = _UnionFind(6 * n)
    directed_edges = _UnionFind(12 * n)
    link_edges = _UnionFind(12 * n)
    matching = []
    for t, f, u, g, permutation in pairs:
        check()
        face_vertices = [v for v in range(4) if v != f]
        for v in face_vertices:
            vertices.join(4 * t + v, 4 * u + permutation[v])
            link_edges.join(_directed(t, v, f),
                            _directed(u, permutation[v], g))
            row = {}
            for index, value in ((7 * t + v, 1),
                                 (7 * t + 4 + _quad(f, v), 1),
                                 (7 * u + permutation[v], -1),
                                 (7 * u + 4 + _quad(g, permutation[v]), -1)):
                row[index] = row.get(index, 0) + value
            matching.append({i: value for i, value in row.items() if value})
        for a, b in combinations(face_vertices, 2):
            edges.join(_edge(t, a, b), _edge(u, permutation[a], permutation[b]),
                       int(permutation[a] > permutation[b]))
            directed_edges.join(_directed(t, a, b),
                                _directed(u, permutation[a], permutation[b]))
            directed_edges.join(_directed(t, b, a),
                                _directed(u, permutation[b], permutation[a]))

    vertex_roots = [vertices.find(i)[0] for i in range(4 * n)]
    edge_roots = [edges.find(i)[0] for i in range(6 * n)]
    boundary_incidence = {}
    for boundary_id, (t, f) in enumerate(boundary_faces):
        check()
        for a, b in combinations((v for v in range(4) if v != f), 2):
            root = edge_roots[_edge(t, a, b)]
            boundary_incidence.setdefault(root, []).append(boundary_id)
    if any(len(faces) != 2 for faces in boundary_incidence.values()):
        raise NormalOrbitError('an edge link is not a circle or an interval')

    # A local edge contributes a segment to its link.  Face pairings pair
    # segment endpoints, so each connected edge link is a circle or interval
    # exactly when it has zero or two unpaired endpoints.  Reverse-edge
    # identifications have already been excluded.  These checks also ensure
    # that all vertex links are surfaces.  Their Euler characteristics now
    # distinguish finite manifold vertices from singular or ideal vertices.
    vertex_links = {}
    for t in range(n):
        check()
        for v in range(4):
            root = vertex_roots[4 * t + v]
            record = vertex_links.setdefault(root, {'faces': 0, 'edges': set(),
                                                     'vertices': set(), 'boundary': 0})
            record['faces'] += 1
            for w in range(4):
                if w == v:
                    continue
                record['vertices'].add(directed_edges.find(_directed(t, v, w))[0])
                record['edges'].add(link_edges.find(_directed(t, v, w))[0])
                record['boundary'] += int(tetrahedra[t][w] is None)
    for record in vertex_links.values():
        chi = len(record['vertices']) - len(record['edges']) + record['faces']
        if chi != (1 if record['boundary'] else 2):
            raise NormalOrbitError('a vertex link is not a sphere or a disc')

    if not boundary_faces:
        raise NormalOrbitError('triangulation has no finite boundary')
    boundary_components = _UnionFind(len(boundary_faces))
    for faces in boundary_incidence.values():
        boundary_components.join(faces[0], faces[1])
    if len({boundary_components.find(i)[0] for i in range(len(boundary_faces))}) != 1:
        raise NormalOrbitError('triangulation must have one boundary component')
    boundary_vertices = {vertex_roots[4 * t + v]
                         for t, f in boundary_faces for v in range(4) if v != f}
    boundary_chi = len(boundary_vertices) - len(boundary_incidence) + len(boundary_faces)
    if boundary_chi != 0:
        raise NormalOrbitError('the boundary component is not a torus')
    endpoints = {}
    for t in range(n):
        for a, b in _EDGES:
            endpoints[edge_roots[_edge(t, a, b)]] = (
                vertex_roots[4 * t + a], vertex_roots[4 * t + b])
    return dict(tetrahedra=tetrahedra, pairs=pairs, boundary_faces=boundary_faces,
                vertex_roots=vertex_roots, edge_roots=edge_roots,
                boundary_incidence=boundary_incidence, endpoints=endpoints,
                matching=matching, vertices=len(vertex_links),
                edges=len(set(edge_roots)),
                edge_orientations=[edges.find(i)[1] for i in range(6 * n)])


def _coordinates(prepared, coordinates, check):
    """Check all matching and quadrilateral equations; retain arbitrary scale."""
    n = len(prepared['tetrahedra'])
    if (type(coordinates) is not list or len(coordinates) != n
            or any(type(row) is not list or len(row) != 7 for row in coordinates)):
        raise NormalOrbitError('expected seven coordinates per tetrahedron')
    rows = []
    for row in coordinates:
        check()
        try:
            values = [encoded_integer(value) for value in row]
        except ValueError as exc:
            raise NormalOrbitError('coordinates must be integers or signed hexadecimal strings') from exc
        if any(value < 0 for value in values):
            raise NormalOrbitError('normal coordinates must be nonnegative')
        if sum(bool(value) for value in values[4:]) > 1:
            raise NormalOrbitError('quadrilateral constraints fail')
        rows.append(values)
    flat = [value for row in rows for value in row]
    for equation in prepared['matching']:
        check()
        if sum(value * flat[index] for index, value in equation.items()):
            raise NormalOrbitError('normal matching equations fail')
    weights = {}
    for t, row in enumerate(rows):
        check()
        for a, b in _EDGES:
            value = row[a] + row[b] + sum(row[4:]) - row[4 + _quad(a, b)]
            root = prepared['edge_roots'][_edge(t, a, b)]
            if root in weights and weights[root] != value:
                raise NormalOrbitError('normal edge weights disagree under face gluing')
            weights[root] = value
    faces = prepared['boundary_faces'] + [(t, f) for t, f, _, _, _ in prepared['pairs']]
    def arc_count(t, f):
        return sum(rows[t][v] for v in range(4) if v != f) + sum(rows[t][4:])
    boundary_arcs = sum(arc_count(t, f) for t, f in prepared['boundary_faces'])
    surface_edges = sum(arc_count(t, f) for t, f in faces)
    disks = sum(flat)
    return dict(rows=rows, weights=weights, faces=faces,
                euler_characteristic=sum(weights.values()) - surface_edges + disks,
                normal_disks=disks, boundary_arcs=boundary_arcs,
                maximum_coordinate_bits=max((value.bit_length() for value in flat), default=0))


def _arc_system(prepared, analysed, *, boundary=False, scale=1, check=lambda: None):
    """Represent normal arcs by at most three interval pairings per face.

    A point on an edge is indexed from a fixed global edge orientation.
    At a face corner v, the m endpoints nearest v on its two incident
    edges are paired in their common order from v. Edge orientation is
    obtained from the parity union-find, never from vertex labels (which
    can coincide in a one-vertex triangulation).
    """
    check()
    roots = sorted(prepared['boundary_incidence'] if boundary else analysed['weights'])
    offsets, total = {}, 0
    for root in roots:
        check()
        offsets[root] = total
        total += scale * analysed['weights'][root]
    faces = prepared['boundary_faces'] if boundary else analysed['faces']
    pairings = []
    for t, f in faces:
        check()
        vertices = [v for v in range(4) if v != f]
        for v in vertices:
            a, b = [u for u in vertices if u != v]
            count = scale * (analysed['rows'][t][v]
                             + analysed['rows'][t][4 + _quad(f, v)])
            if not count:
                continue
            intervals = []
            for u in (a, b):
                local = _edge(t, v, u)
                root = prepared['edge_roots'][local]
                backwards = prepared['edge_orientations'][local] ^ int(v > u)
                weight = scale * analysed['weights'][root]
                if count > weight:
                    raise ArithmeticError('arc count exceeds its incident edge weight')
                start = offsets[root] + (weight - count if backwards else 0)
                intervals.append((start, start + count - 1, backwards))
            x, y = intervals
            pairings.append(IntervalPairing(x[0], x[1], y[0], y[1],
                                           reverse=bool(x[2] ^ y[2])))
    return total, pairings


def normal_arc_pairings(triangulation, coordinates, *, boundary=False,
                        check=lambda: None):
    """Return (number_of_points, interval_pairings) after native validation.

    Both a full normal surface and its boundary are supported. The empty
    surface yields (0, []). The supported ambient manifold is a finite
    connected compact orientable 3-manifold with one torus boundary.
    """
    if type(boundary) is not bool:
        raise ValueError('boundary must be a boolean')
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    return _arc_system(prepared, analysed, boundary=boundary, check=check)


def _boundary_graph(prepared, analysed, check):
    """Reconstruct the mod-two boundary cocycle in fixed edge order."""
    graph = []
    for edge in sorted(prepared['boundary_incidence']):
        check()
        a, b = prepared['endpoints'][edge]
        graph.append((a, b, analysed['weights'][edge] & 1))
    return graph


def _fingerprint(triangulation, analysed, check):
    """Bind exact face records and normalized coordinates without decimal limits."""
    from hashlib import sha256
    import json
    rows = []
    for row in analysed['rows']:
        check()
        rows.append([hex(value) for value in row])
    body = json.dumps({'triangulation': triangulation, 'coordinates': rows},
                      sort_keys=True, separators=(',', ':'))
    return sha256(body.encode()).hexdigest()


# The statistics of the orbit scheduler are deliberately not mathematical claims.
_TOPOLOGY_FIELDS = ('components', 'orientable_components', 'nonorientable_components',
                    'boundary_components', 'euler_characteristic', 'normal_disks',
                    'compressing_disk', 'genus', 'crosscaps')
