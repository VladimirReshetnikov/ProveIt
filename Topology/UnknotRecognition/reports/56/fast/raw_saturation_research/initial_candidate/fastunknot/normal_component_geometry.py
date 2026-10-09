"""Integral cell weights and boundary homology for binary normal surfaces.

The validated manifold contract is inherited from normal_surface_geometry:
finite, compact, connected, orientable, with one torus boundary.  No knot
diagram provenance is asserted.  Every interval is half open.
"""

from collections import deque
from itertools import combinations

from .normal_surface_geometry import _EDGES, _edge, _quad, _arc_system


class _Forest:
    def __init__(self, vertices):
        self.parent = {vertex: vertex for vertex in vertices}
        self.size = {vertex: 1 for vertex in vertices}

    def find(self, vertex):
        while self.parent[vertex] != vertex:
            self.parent[vertex] = self.parent[self.parent[vertex]]
            vertex = self.parent[vertex]
        return vertex

    def join(self, left, right):
        left, right = self.find(left), self.find(right)
        if left == right:
            return False
        if self.size[left] < self.size[right]:
            left, right = right, left
        self.parent[right] = left
        self.size[left] += self.size[right]
        return True


def boundary_homology_basis(prepared, check=lambda: None):
    """Two primal cycles from a tree and disjoint dual tree on the torus."""
    edges = sorted(prepared['boundary_incidence'])
    vertices = sorted({v for edge in edges for v in prepared['endpoints'][edge]})
    primal = _Forest(vertices)
    tree, adjacency = set(), {v: [] for v in vertices}
    for edge in edges:
        check()
        left, right = prepared['endpoints'][edge]
        if primal.join(left, right):
            tree.add(edge)
            adjacency[left].append((right, edge))
            adjacency[right].append((left, edge))
    faces = prepared['boundary_faces']
    dual = _Forest(range(len(faces)))
    cotree = set()
    for edge in edges:
        check()
        if edge not in tree and dual.join(*prepared['boundary_incidence'][edge]):
            cotree.add(edge)
    if len(tree) != len(vertices)-1 or len(cotree) != len(faces)-1:
        raise ArithmeticError('boundary tree-cotree construction disconnected')
    remaining = [edge for edge in edges if edge not in tree | cotree]
    if len(remaining) != 2:
        raise ArithmeticError('a torus tree-cotree decomposition has two leftovers')
    cycles = []
    for edge in remaining:
        start, target = prepared['endpoints'][edge]
        previous = {start: None}
        queue = deque([start])
        while target not in previous:
            check()
            vertex = queue.popleft()
            for neighbour, used in adjacency[vertex]:
                if neighbour not in previous:
                    previous[neighbour] = vertex, used
                    queue.append(neighbour)
        cycle = {edge}
        vertex = target
        while vertex != start:
            vertex, used = previous[vertex]
            cycle.add(used)
        cycles.append(sorted(cycle))
    return cycles


def valid_boundary_basis(prepared, cycles, check=lambda: None):
    """Independently check cycles and quotient rank using binary elimination.

    This checks a homology basis without calling the tree-cotree producer.
    Repeated edges of a triangular face are combined modulo two.
    """
    if (type(cycles) is not list or len(cycles) != 2
            or any(type(cycle) is not list for cycle in cycles)):
        return False
    edges = sorted(prepared['boundary_incidence'])
    indices = {edge: index for index, edge in enumerate(edges)}
    vectors = []
    for cycle in cycles:
        check()
        if (any(type(edge) is not int or edge not in indices for edge in cycle)
                or len(cycle) != len(set(cycle))):
            return False
        odd, vector = set(), 0
        for edge in cycle:
            vector ^= 1 << indices[edge]
            for vertex in prepared['endpoints'][edge]:
                if vertex in odd:
                    odd.remove(vertex)
                else:
                    odd.add(vertex)
        if odd:
            return False
        vectors.append(vector)
    pivots = {}

    def insert(vector):
        while vector:
            pivot = vector.bit_length()-1
            if pivot in pivots:
                vector ^= pivots[pivot]
            else:
                pivots[pivot] = vector
                return True
        return False

    for tetrahedron, face in prepared['boundary_faces']:
        check()
        vector = 0
        for left, right in combinations((v for v in range(4) if v != face), 2):
            edge = prepared['edge_roots'][_edge(tetrahedron, left, right)]
            vector ^= 1 << indices[edge]
        insert(vector)
    return all(insert(vector) for vector in vectors)


def _edge_offsets(analysed, check):
    offsets, total = {}, 0
    for edge in sorted(analysed['weights']):
        check()
        offsets[edge] = total
        total += analysed['weights'][edge]
    return offsets, total


def disk_corner_intervals(prepared, analysed, offsets, check=lambda: None):
    """One consecutive set of corner points for each nonempty disk type.

    An entry is (flat_coordinate_index, start, stop).  Exactly one vertex
    is chosen on every normal disk, irrespective of face identifications.
    """
    answer = []

    def interval(tetrahedron, left, right, start, count):
        local = _edge(tetrahedron, left, right)
        root = prepared['edge_roots'][local]
        reverse = prepared['edge_orientations'][local] ^ int(left > right)
        if reverse:
            start = analysed['weights'][root]-start-count
        lo = offsets[root]+start
        return lo, lo+count

    for tetrahedron, row in enumerate(analysed['rows']):
        check()
        for vertex in range(4):
            if row[vertex]:
                neighbour = next(v for v in range(4) if v != vertex)
                lo, hi = interval(tetrahedron, vertex, neighbour, 0, row[vertex])
                answer.append((7*tetrahedron+vertex, lo, hi))
        for quadrilateral in range(3):
            count = row[4+quadrilateral]
            if count:
                left, right = next((a, b) for a, b in _EDGES
                                   if _quad(a, b) != quadrilateral)
                lo, hi = interval(tetrahedron, left, right, row[left], count)
                answer.append((7*tetrahedron+4+quadrilateral, lo, hi))
    return answer


def component_weight_system(prepared, analysed, *, mode='disk', basis=None,
                            check=lambda: None):
    """Build the maintained arc relation and query-specific additive weights.

    disk: (Euler characteristic, two integral boundary intersection counts).
    summary: the above, plus normal disk count and boundary point count.
    coordinates: all 7t normal coordinates; used as the full-vector reference.
    The last mode also permits extraction of actual component normal vectors.
    """
    if mode not in ('disk', 'summary', 'coordinates'):
        raise ValueError('mode must be disk, summary, or coordinates')
    if basis is None:
        basis = boundary_homology_basis(prepared, check)
    size, pairings = _arc_system(prepared, analysed, check=check)
    offsets, total = _edge_offsets(analysed, check)
    if total != size:
        raise ArithmeticError('edge universe sizes disagree')
    corners = disk_corner_intervals(prepared, analysed, offsets, check)
    dimension = 7*len(analysed['rows']) if mode == 'coordinates' else (3 if mode == 'disk' else 5)
    weights = []

    def add(lo, hi, entries):
        if lo == hi:
            return
        value = [0]*dimension
        for index, amount in entries:
            value[index] += amount
        weights.append((lo, hi, value))

    if mode == 'coordinates':
        for index, lo, hi in corners:
            check()
            add(lo, hi, [(index, 1)])
    else:
        # One unit per vertex, one debit per face arc, one credit per disk.
        add(0, size, [(0, 1)])
        for pairing in pairings:
            check()
            add(pairing.a, pairing.b+1, [(0, -1)])
        for _, lo, hi in corners:
            check()
            add(lo, hi, [(0, 1)] + ([(3, 1)] if mode == 'summary' else []))
        for index, cycle in enumerate(basis):
            for edge in cycle:
                check()
                add(offsets[edge], offsets[edge]+analysed['weights'][edge], [(1+index, 1)])
        if mode == 'summary':
            for edge in sorted(prepared['boundary_incidence']):
                check()
                add(offsets[edge], offsets[edge]+analysed['weights'][edge], [(4, 1)])
    return dict(size=size, pairings=pairings, weights=weights,
                dimension=dimension, basis=basis)


def full_vector_signature(prepared, vector, basis, check=lambda: None):
    """Linear Euler/boundary evaluation on a connected component vector."""
    from .normal_surface_geometry import _coordinates
    count = len(prepared['tetrahedra'])
    if len(vector) != 7*count:
        raise ValueError('component coordinate dimension differs')
    rows = [list(vector[7*t:7*t+7]) for t in range(count)]
    analysed = _coordinates(prepared, rows, check)
    values = [analysed['euler_characteristic']]
    values.extend(sum(analysed['weights'][edge] for edge in cycle) for cycle in basis)
    values.extend([analysed['normal_disks'], analysed['boundary_arcs']])
    return values, rows
