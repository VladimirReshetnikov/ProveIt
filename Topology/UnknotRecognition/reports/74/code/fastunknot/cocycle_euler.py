"""Maximize Euler characteristic on an entire certified minimum-span face.

This remains a restricted surface family, not an unknot decision procedure.
All global edge face-incidence counts must be at least two. The returned
surface uses the existing span format; positive knot claims still require
an independent source-bound disc, annulus or planar verifier.
"""
from collections import Counter
from itertools import combinations
from .integer_codec import encoded_integer
from .normal_cocycle import _Budget, local_coordinates
from .normal_surface_geometry import _prepare, _coordinates, _EDGES, _edge, NormalOrbitError
from .cocycle_span_verify import verify_cocycle_span
from .cocycle_euler_flow import _minimize_difference


def _euler_model(prepared, heights, certificate, check):
    vertices = [prepared['vertex_roots'][4*t:4*t+4]
                for t in range(len(prepared['tetrahedra']))]
    if not verify_cocycle_span(vertices, heights, certificate, check=check):
        raise ValueError('a valid minimum-span certificate is required')
    h = [[encoded_integer(x) for x in row] for row in heights]
    labels = [encoded_integer(x) for x in certificate['vertex_ids']]
    index = {v: i for i, v in enumerate(labels)}
    initial = [encoded_integer(x) for x in certificate['potential']]
    global_edges = {}
    for t, row in enumerate(h):
        check()
        for j, (a, b) in enumerate(_EDGES):
            check()
            local = 6*t+j
            u, v, c = vertices[t][a], vertices[t][b], row[b]-row[a]
            if prepared['edge_orientations'][local]:
                u, v, c = v, u, -c
            root = prepared['edge_roots'][local]
            if root in global_edges and global_edges[root] != (u, v, c):
                raise NormalOrbitError('height differences do not define a global cocycle')
            global_edges[root] = u, v, c
    degree = Counter()
    faces = prepared['boundary_faces']+[(t, f) for t, f, u, g, p in prepared['pairs']]
    for t, f in faces:
        check()
        for a, b in combinations([v for v in range(4) if v != f], 2):
            degree[prepared['edge_roots'][_edge(t, a, b)]] += 1
    edges = []
    for root, (a, b, c) in sorted(global_edges.items()):
        check()
        if degree[root] < 2:
            raise NormalOrbitError('Euler objective has a negative edge weight')
        edges.append([index[a], index[b], c, degree[root]-2])
    low = {t: i for t, i, s, j in certificate['matching']}
    high = {s: j for t, i, s, j in certificate['matching']}
    constraints = []
    for t, (vs, hs) in enumerate(zip(vertices, h)):
        check()
        l, u = low[t], high[t]
        for i in range(4):
            constraints.append([index[vs[i]], index[vs[l]], hs[i]-hs[l]])
            constraints.append([index[vs[u]], index[vs[i]], hs[u]-hs[i]])
    return vertices, h, edges, constraints, initial


def maximize_cocycle_face_euler(triangulation, heights, certificate, *, max_work=None, check=lambda: None):
    """Return an exact optimum and arithmetic dual, without a knot verdict.

    With N tetrahedra, the new network has O(N) nodes/arcs and sends O(N)
    integral units. Its O(N) shortest-path augmentations take O(N^2 log N)
    indexed graph operations, independently of height magnitude. Validation
    and Python container costs are additional. All positive topology/source
    checks remain the responsibility of the existing certificate consumer.
    """
    budget = _Budget(check, max_work)
    prepared = _prepare(triangulation, budget.tick)
    vertices, h, edges, constraints, initial = _euler_model(prepared, heights, certificate, budget.tick)
    before = _coordinates(prepared, certificate['coordinates'], budget.tick)
    result = _minimize_difference(len(initial), edges, constraints, initial, budget.tick)
    optimum = result['certificate']
    lookup = dict(zip(map(encoded_integer, certificate['vertex_ids']), optimum['potential']))
    coordinates = []
    for vs, hs in zip(vertices, h):
        budget.tick()
        coordinates.append(local_coordinates([x+lookup[v] for v, x in zip(vs, hs)]))
    surface = dict(certificate, potential=optimum['potential'], coordinates=coordinates)
    if not verify_cocycle_span(vertices, h, surface, check=budget.tick):
        raise ArithmeticError('Euler optimum left the certified minimum-span face')
    after = _coordinates(prepared, coordinates, budget.tick)
    if 2*after['euler_characteristic'] != 2*after['normal_disks']-optimum['objective']:
        raise ArithmeticError('Euler edge objective disagrees with normal cell count')
    if after['euler_characteristic'] < before['euler_characteristic']:
        raise ArithmeticError('Euler optimum is worse than its starting surface')
    return dict(certificate=surface, optimality_certificate=optimum,
                initial_euler_characteristic=before['euler_characteristic'],
                euler_characteristic=after['euler_characteristic'],
                stats=dict(result['stats'], work=budget.work))
