"""Check a primitive extreme normal disc without expanding its coordinates.

The input is a *finite* tetrahedral triangulation, encoded by face pairings.
This module independently checks that it is a connected compact orientable
3-manifold with one torus boundary, then checks a normal compressing disc.
It does not prove that the triangulation is the exterior of a supplied knot.
In particular, its successful result is not a PD-level unknot certificate.

Normal coordinates are rows [T0,T1,T2,T3,Q01|23,Q02|13,Q03|12].  A primitive
integral point on an extreme ray is connected: its component vectors lie on
the same ray, and primitivity makes their positive scale factors integers.
This classical normal-surface argument replaces component enumeration.
Full rank modulo one checked small prime certifies the required rational
rank.  Euler characteristic one and nonempty boundary then imply a disc.
On the checked boundary torus, intersection parity is a cocycle; it is not
a coboundary precisely when the single simple boundary curve is essential.

Neither a successful check nor a failed check provides a running-time bound
for finding this witness, performing triangulation conversion, or deciding
all knots.  There is no dependency on Regina in this verifier.
"""

from collections import deque
from itertools import combinations
from math import gcd, isqrt


class NormalDiskError(ValueError):
    """Malformed input or a failed normal-disc certificate condition."""


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
                raise NormalDiskError('a triangulation edge is identified with its reverse')
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
        raise NormalDiskError('expected a nonempty tetrahedra array')
    tetrahedra = triangulation['tetrahedra']
    n = len(tetrahedra)
    for t, faces in enumerate(tetrahedra):
        check()
        if type(faces) is not list or len(faces) != 4:
            raise NormalDiskError('each tetrahedron must have four face records')
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
                raise NormalDiskError('invalid face pairing record')
            if record['tetrahedron'] == t and record['permutation'][f] == f:
                raise NormalDiskError('a face cannot be paired with itself')
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
                raise NormalDiskError('face pairings must be reciprocal')
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
                    raise NormalDiskError('triangulation is not orientable')
            else:
                orientations[u] = value
                queue.append(u)
    if len(orientations) != n:
        raise NormalDiskError('triangulation is not connected through faces')

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
        raise NormalDiskError('an edge link is not a circle or an interval')

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
            raise NormalDiskError('a vertex link is not a sphere or a disc')

    if not boundary_faces:
        raise NormalDiskError('triangulation has no finite boundary')
    boundary_components = _UnionFind(len(boundary_faces))
    for faces in boundary_incidence.values():
        boundary_components.join(faces[0], faces[1])
    if len({boundary_components.find(i)[0] for i in range(len(boundary_faces))}) != 1:
        raise NormalDiskError('triangulation must have one boundary component')
    boundary_vertices = {vertex_roots[4 * t + v]
                         for t, f in boundary_faces for v in range(4) if v != f}
    boundary_chi = len(boundary_vertices) - len(boundary_incidence) + len(boundary_faces)
    if boundary_chi != 0:
        raise NormalDiskError('the boundary component is not a torus')
    endpoints = {}
    for t in range(n):
        for a, b in _EDGES:
            endpoints[edge_roots[_edge(t, a, b)]] = (
                vertex_roots[4 * t + a], vertex_roots[4 * t + b])
    return dict(tetrahedra=tetrahedra, pairs=pairs, boundary_faces=boundary_faces,
                vertex_roots=vertex_roots, edge_roots=edge_roots,
                boundary_incidence=boundary_incidence, endpoints=endpoints,
                matching=matching, vertices=len(vertex_links),
                edges=len(set(edge_roots)))


def _analyse_coordinates(prepared, coordinates, check):
    n = len(prepared['tetrahedra'])
    if (type(coordinates) is not list or len(coordinates) != n
            or any(type(row) is not list or len(row) != 7 for row in coordinates)
            or any(type(value) is not int or value < 0
                   for row in coordinates for value in row)):
        raise NormalDiskError('expected seven nonnegative integer coordinates per tetrahedron')
    flat = [value for row in coordinates for value in row]
    support = [i for i, value in enumerate(flat) if value]
    if not support:
        raise NormalDiskError('the surface is empty')
    if any(sum(value != 0 for value in row[4:]) > 1 for row in coordinates):
        raise NormalDiskError('quadrilateral constraints fail')
    for row in prepared['matching']:
        check()
        if sum(value * flat[i] for i, value in row.items()) != 0:
            raise NormalDiskError('normal matching equations fail')
    divisor = 0
    for value in flat:
        divisor = gcd(divisor, value)
    if divisor != 1:
        raise NormalDiskError('the normal vector is not primitive')

    edge_weights = {}
    for t, row in enumerate(coordinates):
        check()
        for a, b in _EDGES:
            value = row[a] + row[b] + sum(row[4:]) - row[4 + _quad(a, b)]
            root = prepared['edge_roots'][_edge(t, a, b)]
            if root in edge_weights and edge_weights[root] != value:
                raise NormalDiskError('normal edge weights disagree under gluing')
            edge_weights[root] = value

    def face_arcs(t, f):
        row = coordinates[t]
        return sum(row[v] for v in range(4) if v != f) + sum(row[4:])

    boundary_arcs = sum(face_arcs(t, f) for t, f in prepared['boundary_faces'])
    surface_edges = boundary_arcs + sum(face_arcs(t, f)
                                       for t, f, _, _, _ in prepared['pairs'])
    disks = sum(flat)
    chi = sum(edge_weights.values()) - surface_edges + disks
    if chi != 1:
        raise NormalDiskError('the surface does not have Euler characteristic one')
    if boundary_arcs == 0:
        raise NormalDiskError('the surface has no boundary')

    # Intersection parities form the Poincare-dual cocycle on the primal
    # boundary triangulation.  Test directly whether a vertex potential
    # solves c(uv)=potential(u)+potential(v), including loop edges.
    graph = {}
    for edge in prepared['boundary_incidence']:
        a, b = prepared['endpoints'][edge]
        parity = edge_weights[edge] % 2
        graph.setdefault(a, []).append((b, parity))
        graph.setdefault(b, []).append((a, parity))
    for t, f in prepared['boundary_faces']:
        parity = sum(edge_weights[prepared['edge_roots'][_edge(t, a, b)]]
                     for a, b in combinations((v for v in range(4) if v != f), 2)) % 2
        if parity:
            raise NormalDiskError('boundary intersection parities are not a cocycle')
    potentials = {}
    nonzero_class = False
    for start in graph:
        if start in potentials:
            continue
        potentials[start] = 0
        queue = deque([start])
        while queue:
            check()
            a = queue.popleft()
            for b, parity in graph[a]:
                value = potentials[a] ^ parity
                if b in potentials:
                    if potentials[b] != value:
                        nonzero_class = True
                else:
                    potentials[b] = value
                    queue.append(b)
    if not nonzero_class:
        raise NormalDiskError('the boundary parity cocycle is a coboundary')
    support_index = {index: i for i, index in enumerate(support)}
    restricted_rows = [{support_index[i]: value for i, value in row.items()
                        if i in support_index} for row in prepared['matching']]
    return dict(coordinates=coordinates, support=support, rows=restricted_rows,
                euler_characteristic=chi, normal_disks=disks,
                boundary_arcs=boundary_arcs,
                maximum_coordinate_bits=max(value.bit_length() for value in flat))


def _prime_bound(support_size):
    return 32 * (support_size + 1) ** 2


def _is_prime(value):
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    return all(value % divisor for divisor in range(3, isqrt(value) + 1, 2))


def _rank_mod(rows, columns, prime, check):
    if prime == 2:
        # Packed exact row reduction also keeps very large binary-coordinate
        # witnesses useful in practice.  This is ordinary elimination over F2.
        pivots = {}
        for sparse in rows:
            check()
            row = 0
            for i, value in sparse.items():
                if value % 2:
                    row ^= 1 << i
            while row:
                column = row.bit_length() - 1
                if column in pivots:
                    row ^= pivots[column]
                else:
                    pivots[column] = row
                    break
        return len(pivots)
    pivots = {}
    for sparse in rows:
        check()
        row = [0] * columns
        for i, value in sparse.items():
            row[i] = value % prime
        for column in range(columns):
            if row[column] == 0:
                continue
            if column in pivots:
                factor = row[column]
                pivot = pivots[column]
                for j in range(column, columns):
                    row[j] = (row[j] - factor * pivot[j]) % prime
            else:
                inverse = pow(row[column], prime - 2, prime)
                for j in range(column, columns):
                    row[j] = row[j] * inverse % prime
                pivots[column] = row
                break
    return len(pivots)


def audit_normal_disk_certificate(triangulation, certificate, *, check=lambda: None):
    """Return verified relative evidence; raise NormalDiskError on rejection.

    The tetrahedra dictionary is reconstructed and validated independently.
    The certificate has exactly version, normal_coordinates and rank_prime.
    Integers are actual Python integers (Booleans are rejected).  A prime is
    restricted to O(t^2) so its primality check has polynomial bit cost.
    ``check`` is called cooperatively and its cancellation exception propagates.
    """
    if (type(certificate) is not dict
            or set(certificate) != {'version', 'normal_coordinates', 'rank_prime'}
            or type(certificate['version']) is not int or certificate['version'] != 1):
        raise NormalDiskError('invalid normal-disc certificate schema')
    prepared = _prepare(triangulation, check)
    analysed = _analyse_coordinates(prepared, certificate['normal_coordinates'], check)
    size = len(analysed['support'])
    prime = certificate['rank_prime']
    if (type(prime) is not int or not 2 <= prime <= _prime_bound(size)
            or not _is_prime(prime)):
        raise NormalDiskError('rank modulus must be a prime within the checked size bound')
    rank = _rank_mod(analysed['rows'], size, prime, check)
    if rank != size - 1:
        raise NormalDiskError('support matrix does not have certified nullity one')
    check()
    return dict(status='CERTIFIED_COMPRESSING_DISK', tetrahedra=len(prepared['tetrahedra']),
                triangulation_vertices=prepared['vertices'],
                triangulation_edges=prepared['edges'],
                matching_equations=len(prepared['matching']), support_size=size,
                rank_prime=prime, rank=rank,
                normal_disks=analysed['normal_disks'],
                maximum_coordinate_bits=analysed['maximum_coordinate_bits'],
                boundary_normal_arcs=analysed['boundary_arcs'], euler_characteristic=1,
                boundary_homology_mod2='nonzero',
                trust='checked disc in the supplied finite triangulation; '
                      'no correspondence with an input knot is asserted')


def verify_normal_disk_certificate(triangulation, certificate, *, check=lambda: None):
    """Return a Boolean; callback cancellation still propagates."""
    try:
        audit_normal_disk_certificate(triangulation, certificate, check=check)
    except NormalDiskError:
        return False
    return True


def normal_disk_certificate(triangulation, coordinates, *, check=lambda: None):
    """Certify a supplied extreme normal disc; do not search for a surface.

    Return None when these coordinates fail a certificate condition.  The
    finite triangulation itself is validated first, and malformed or unsuitable
    triangulations raise NormalDiskError.  For an admissible primitive extreme
    vector passing the topological tests, a good prime exists among the first
    s primes, where s is the support size: a nonzero (s-1)-minor has absolute
    value at most 2**(s-1).  Every matching row has Euclidean norm at most two.
    The first s primes lie below 32*(s+1)**2; a central-binomial-coefficient
    estimate suffices to establish this generous elementary bound.
    """
    prepared = _prepare(triangulation, check)
    try:
        analysed = _analyse_coordinates(prepared, coordinates, check)
    except NormalDiskError:
        return None
    size = len(analysed['support'])
    tested = 0
    for prime in range(2, _prime_bound(size) + 1):
        check()
        if not _is_prime(prime):
            continue
        tested += 1
        if _rank_mod(analysed['rows'], size, prime, check) == size - 1:
            return dict(version=1, normal_coordinates=[list(row) for row in coordinates],
                        rank_prime=prime)
        if tested == size:
            return None
    raise AssertionError('elementary prime supply bound failed')
