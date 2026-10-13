"""Independent replay of a finite normal-ray crushing quotient.

Crushed face states form a degree-two graph; connected components, rather than
the producer's face tracer, reconstruct the surviving face identifications.
Erased components may be cycles.  Every quotient component is checked as a
finite orientable manifold, including components discarded from the successor.

This certificate is conditional geometry.  Neither one torus boundary nor a
successful quotient replay authenticates a classical knot exterior or proves
unknottedness.  Diagram provenance and the crushing theorem belong to a chain
verifier above this API.  No peripheral marking is transported here.
"""

from collections import deque
from itertools import combinations
from types import SimpleNamespace

from .normal_surface_geometry import _prepare, _coordinates
from .source_kernel_verify import SourceKernelVerifier


_EDGES = tuple(combinations(range(4), 2))
_EDGE_IDS = {edge: i for i, edge in enumerate(_EDGES)}


def _edge(t, a, b):
    return 6*t+_EDGE_IDS[tuple(sorted((a, b)))]


class _DisjointSets:
    def __init__(self, size):
        self.parent = list(range(size))
        self.weight = [1]*size
        self.sign = [0]*size

    def find(self, x):
        root, parity = x, 0
        while root != self.parent[root]:
            parity ^= self.sign[root]
            root = self.parent[root]
        total = parity
        while x != root:
            parent, step = self.parent[x], self.sign[x]
            self.parent[x], self.sign[x] = root, parity
            parity ^= step
            x = parent
        return root, total

    def root_sign(self, x):
        return self.find(x)

    def join(self, a, b, parity=0):
        a, x = self.root_sign(a)
        b, y = self.root_sign(b)
        if a == b:
            if x ^ y != parity:
                raise ValueError('an edge is identified with its reverse')
            return
        if self.weight[a] < self.weight[b]:
            a, b = b, a
        self.parent[b] = a
        self.sign[b] = x ^ y ^ parity
        self.weight[a] += self.weight[b]

    def root(self, x):
        return self.root_sign(x)[0]


def _sign(permutation):
    return -1 if sum(permutation[i] > permutation[j]
                     for i in range(4) for j in range(i+1, 4)) % 2 else 1


def quotient_census(quotient, *, check=lambda: None):
    """Validate every finite orientable component and list boundary Euler data.

    Empty triangulations are valid.  Component tetrahedron lists and boundary
    Euler lists are sorted; components are ordered by their smallest label.
    Invalid face data, reverse edges, singular/ideal vertices, or nonorientable
    components raise ValueError.  Caller cancellation propagates unchanged.
    """
    check()
    if (type(quotient) is not dict or set(quotient) != {'tetrahedra'}
            or type(quotient['tetrahedra']) is not list):
        raise ValueError('expected a tetrahedra array')
    tetrahedra = quotient['tetrahedra']
    n = len(tetrahedra)
    for t, faces in enumerate(tetrahedra):
        check()
        if type(faces) is not list or len(faces) != 4:
            raise ValueError('each tetrahedron requires four face records')
        for f, record in enumerate(faces):
            if record is None:
                continue
            if (type(record) is not dict or set(record) != {'tetrahedron', 'permutation'}
                    or type(record['tetrahedron']) is not int
                    or not 0 <= record['tetrahedron'] < n
                    or type(record['permutation']) is not list
                    or len(record['permutation']) != 4
                    or any(type(v) is not int for v in record['permutation'])
                    or set(record['permutation']) != set(range(4))):
                raise ValueError('invalid face record')
            if record['tetrahedron'] == t and record['permutation'][f] == f:
                raise ValueError('a face cannot be paired to itself')
    adjacency = [[] for _ in range(n)]
    pairs, boundary = [], []
    for t, faces in enumerate(tetrahedra):
        check()
        for f, record in enumerate(faces):
            if record is None:
                boundary.append((t, f))
                continue
            u, p = record['tetrahedron'], record['permutation']
            g = p[f]
            back = tetrahedra[u][g]
            if (back is None or back['tetrahedron'] != t
                    or any(back['permutation'][p[v]] != v for v in range(4))):
                raise ValueError('face pairings must be reciprocal')
            adjacency[t].append((u, -_sign(p)))
            if (t, f) < (u, g):
                pairs.append((t, f, u, g, p))
    components, owner, orientation = [], {}, {}
    for root in range(n):
        check()
        if root in owner:
            continue
        number = len(components)
        todo, ids = deque((root,)), []
        owner[root], orientation[root] = number, 1
        while todo:
            check()
            t = todo.popleft()
            ids.append(t)
            for u, multiplier in adjacency[t]:
                value = multiplier*orientation[t]
                if u in owner:
                    if orientation[u] != value:
                        raise ValueError('quotient component is not orientable')
                else:
                    owner[u], orientation[u] = number, value
                    todo.append(u)
        components.append(dict(tetrahedra=sorted(ids), boundary_euler=[]))

    vertices, edges = _DisjointSets(4*n), _DisjointSets(6*n)
    for t, f, u, g, p in pairs:
        check()
        face = tuple(v for v in range(4) if v != f)
        for v in face:
            vertices.join(4*t+v, 4*u+p[v])
        for a, b in combinations(face, 2):
            edges.join(_edge(t, a, b), _edge(u, p[a], p[b]), int(p[a] > p[b]))
    vr = tuple(vertices.root(j) for j in range(4*n))
    er = tuple(edges.root(j) for j in range(6*n))
    link_faces, link_boundary, link_vertices = ([0]*(4*n) for _ in range(3))
    boundary_edges = {}
    for bid, (t, f) in enumerate(boundary):
        check()
        face = tuple(v for v in range(4) if v != f)
        for v in face:
            link_boundary[vr[4*t+v]] += 1
        for a, b in combinations(face, 2):
            boundary_edges.setdefault(er[_edge(t, a, b)], []).append(bid)
    if any(len(ends) != 2 for ends in boundary_edges.values()):
        raise ValueError('edge link is not a circle or interval')
    endpoints = {}
    for t in range(n):
        check()
        for v in range(4):
            link_faces[vr[4*t+v]] += 1
        for j, (a, b) in enumerate(_EDGES):
            endpoints[er[6*t+j]] = (vr[4*t+a], vr[4*t+b])
    for a, b in endpoints.values():
        link_vertices[a] += 1
        link_vertices[b] += 1
    for j, count in enumerate(link_faces):
        check()
        if count and 2*link_vertices[j]-count-link_boundary[j] != (2 if link_boundary[j] else 4):
            raise ValueError('vertex link is not a sphere or disc')

    boundary_sets = _DisjointSets(len(boundary))
    for ends in boundary_edges.values():
        check()
        boundary_sets.join(*ends)
    face_groups = {}
    for bid in range(len(boundary)):
        face_groups.setdefault(boundary_sets.root(bid), []).append(bid)
    for ids in face_groups.values():
        check()
        bv, be = set(), set()
        for bid in ids:
            t, f = boundary[bid]
            face = tuple(v for v in range(4) if v != f)
            bv.update(vr[4*t+v] for v in face)
            be.update(er[_edge(t, a, b)] for a, b in combinations(face, 2))
        component = owner[boundary[ids[0]][0]]
        components[component]['boundary_euler'].append(len(bv)-len(be)+len(ids))
    for component in components:
        component['boundary_euler'].sort()
    return components


def _graph_quotient(tetrahedra, rows, check):
    """Collapse labelled components of the independent face-state graph."""
    n = len(tetrahedra)
    quads = [next((q for q in range(3) if row[4+q]), None) for row in rows]
    retained = [t for t, q in enumerate(quads) if q is None]
    numbers = {t: i for i, t in enumerate(retained)}
    graph = [[] for _ in range(4*n)]

    def edge(a, b, p):
        inverse = tuple(p.index(v) for v in range(4))
        graph[a].append((b, tuple(p)))
        graph[b].append((a, inverse))

    for t, faces in enumerate(tetrahedra):
        check()
        for f, record in enumerate(faces):
            if record is not None:
                u, p = record['tetrahedron'], record['permutation']
                a, b = 4*t+f, 4*u+p[f]
                if a < b:
                    edge(a, b, p)
        q = quads[t]
        if q is not None:
            first = (0, q+1)
            second = tuple(v for v in range(4) if v not in first)
            for a, b in (first, second):
                flip = list(range(4))
                flip[a], flip[b] = b, a
                edge(4*t+a, 4*t+b, flip)
    output = [[None]*4 for _ in retained]
    seen = set()
    for root in range(4*n):
        check()
        if root in seen:
            continue
        seen.add(root)
        component = [root]
        for node in component:
            check()
            if len(graph[node]) > 2:
                raise ValueError('invalid crushing face-state degree')
            for other, _ in graph[node]:
                if other not in seen:
                    seen.add(other)
                    component.append(other)
        surviving = sorted(node for node in component if node//4 in numbers)
        # An erased component may be an isolated cycle, with arbitrary
        # permutation holonomy. It creates no surviving face pairing.
        if not surviving:
            continue
        ends = [node for node in component if len(graph[node]) < 2]
        if len(surviving) == 1:
            if surviving[0] not in ends or len(ends) not in (1, 2):
                raise ValueError('surviving face reaches no graph endpoint')
            continue
        if len(surviving) != 2 or set(ends) != set(surviving):
            raise ValueError('crushing component has inconsistent endpoints')
        first, last = surviving
        potentials = {first: tuple(range(4))}
        todo = deque((first,))
        while todo:
            check()
            node = todo.popleft()
            for other, p in graph[node]:
                value = tuple(p[v] for v in potentials[node])
                if other in potentials:
                    if potentials[other] != value:
                        raise ValueError('inconsistent retained component permutations')
                else:
                    potentials[other] = value
                    todo.append(other)
        p = potentials[last]
        t, f = divmod(first, 4)
        u, g = divmod(last, 4)
        if p[f] != g:
            raise ValueError('quotient permutation does not map its paired face')
        output[numbers[t]][f] = dict(tetrahedron=numbers[u], permutation=list(p))
        output[numbers[u]][g] = dict(tetrahedron=numbers[t],
                                    permutation=[p.index(v) for v in range(4)])
    return retained, dict(tetrahedra=output)


def _same(actual, expected):
    """Strict JSON comparison: booleans are never integer labels."""
    if type(actual) is not type(expected):
        return False
    if type(expected) is dict:
        return actual.keys() == expected.keys() and all(_same(actual[k], v) for k, v in expected.items())
    if type(expected) is list:
        return len(actual) == len(expected) and all(_same(a, b) for a, b in zip(actual, expected))
    return actual == expected


def _successor(quotient, components, check):
    selected = None
    for i, component in enumerate(components):
        check()
        boundary = component['boundary_euler']
        if boundary == [0]:
            if selected is not None:
                raise ValueError('more than one torus-boundary component')
            selected = i
        elif any(chi != 2 for chi in boundary):
            raise ValueError('unexpected boundary after conditional knot-exterior crushing')
    if selected is None:
        return None, None
    ids = components[selected]['tetrahedra']
    renumber = {t: i for i, t in enumerate(ids)}
    output = []
    for t in ids:
        check()
        output.append([None if record is None else dict(
            tetrahedron=renumber[record['tetrahedron']], permutation=list(record['permutation']))
            for record in quotient['tetrahedra'][t]])
    return selected, dict(tetrahedra=output)


def verify_normal_crushing(triangulation, packet, *, check=lambda: None):
    """Replay a strict shrinking quotient; make no standalone knot verdict."""
    failed = False

    def poll():
        nonlocal failed
        try:
            check()
        except BaseException:
            failed = True
            raise

    poll()
    try:
        if (type(packet) is not dict or set(packet) != {
                'schema', 'coordinates', 'retained_tetrahedra', 'triangulation',
                'components', 'torus_component', 'successor'}
                or packet['schema'] != 'normal-ray-crushing-v1'):
            return False
        prepared = _prepare(triangulation, poll)
        analysed = _coordinates(prepared, packet['coordinates'], poll)
        rows = analysed['rows']
        n = len(rows)
        if analysed['euler_characteristic'] <= 0 or not any(any(row[4:]) for row in rows):
            return False
        flat = tuple(v for row in rows for v in row)
        support = tuple(j for j,x in enumerate(flat) if x)
        equations = []
        for sparse in prepared['matching']:
            poll()
            equations.append(tuple(sparse.get(j, 0) for j in support))
        source = SimpleNamespace(n=len(support), equations=tuple(equations), conflicts=())
        # This is the positive-support face of the FULL matching cone. Every
        # original equation remains; no extra linear constraint can fake
        # extremality. Reverse-pivot elimination is independent of the producer.
        verifier = SourceKernelVerifier(source, check=poll, cache_size=0)
        if not verifier.verify(tuple(flat[j] for j in support), (1,)*len(support), check=poll):
            return False
        retained, quotient = _graph_quotient(prepared['tetrahedra'], rows, poll)
        if len(retained) >= n or not _same(packet['retained_tetrahedra'], retained):
            return False
        if not _same(packet['triangulation'], quotient):
            return False
        components = quotient_census(quotient, check=poll)
        selected, successor = _successor(quotient, components, poll)
        return (_same(packet['components'], components)
                and _same(packet['torus_component'], selected)
                and _same(packet['successor'], successor))
    except (ValueError, TypeError, KeyError, IndexError, ArithmeticError, AttributeError):
        if failed:
            raise
        return False
