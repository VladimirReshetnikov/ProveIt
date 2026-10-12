"""Bounded monotone boundary shellings of a finite torus-boundary manifold.

Use embedded tetrahedra whose intersection with the boundary is exactly a
nonempty proper union of facets. Initial global vertex/edge classes persist
on surviving corners; shellings never split their links. Only discovery
lives here. The separate replay module imports no producer routine.
"""
from heapq import heappop, heappush
from .normal_cocycle import _Budget
from .normal_surface_geometry import _prepare, _EDGES, _edge


def shell_boundary(triangulation, *, max_moves=None, max_work=None, check=lambda: None):
    if max_moves is not None and (type(max_moves) is not int or max_moves < 0):
        raise ValueError('max_moves must be a nonnegative integer or None')
    budget = _Budget(check, max_work)
    p = _prepare(triangulation, budget.tick)
    rows = [list(row) for row in p['tetrahedra']]
    n = len(rows)
    vertices, edges = p['vertex_roots'], p['edge_roots']
    vertex_faces, edge_faces = [0]*(4*n), [0]*(6*n)
    vertex_tets, edge_tets = [[] for _ in vertices], [[] for _ in edges]
    for t in range(n):
        budget.tick()
        for v in set(vertices[4*t:4*t+4]):vertex_tets[v].append(t)
        for e in set(edges[6*t:6*t+6]):edge_tets[e].append(t)

    def count_face(t, f, delta):
        for v in range(4):
            if v != f:vertex_faces[vertices[4*t+v]] += delta
        for a, b in _EDGES:
            if f not in (a, b):edge_faces[edges[_edge(t,a,b)]] += delta

    for t, f in p['boundary_faces']:
        budget.tick()
        count_face(t, f, 1)

    def eligible(t):
        budget.tick()
        row = rows[t]
        if row is None or len(set(vertices[4*t:4*t+4])) != 4:return 0
        boundary = [f for f, r in enumerate(row) if r is None]
        if not 0 < len(boundary) < 4:return 0
        # Test equality of boundary subcomplexes, including lower faces.
        for v in range(4):
            if vertex_faces[vertices[4*t+v]] and not any(f != v for f in boundary):return 0
        for a,b in _EDGES:
            if edge_faces[edges[_edge(t,a,b)]] and not any(f not in (a,b) for f in boundary):return 0
        return len(boundary)

    versions, heap = [0]*n, []
    for t in range(n):
        b = eligible(t)
        if b:heappush(heap, (-b,t,0))
    moves, kinds, visits = [], [0]*4, 0
    while heap and (max_moves is None or len(moves) < max_moves):
        budget.tick()
        negative, t, version = heappop(heap)
        if rows[t] is None or version != versions[t]:continue
        b = eligible(t)
        if b != -negative:raise ArithmeticError('stale shelling eligibility')
        old_vertices = {v:bool(vertex_faces[v]) for v in vertices[4*t:4*t+4]}
        old_edges = {e:bool(edge_faces[e]) for e in edges[6*t:6*t+6]}
        affected = set()
        for f, record in enumerate(rows[t]):
            budget.tick()
            count_face(t,f,-1 if record is None else 1)
            if record is not None:
                u, g = record['tetrahedron'], record['permutation'][f]
                if u == t or rows[u] is None:raise ArithmeticError('invalid shelling neighbor')
                rows[u][g] = None
                affected.add(u)
        rows[t] = None
        moves.append(t);kinds[b] += 1
        for v, was_boundary in old_vertices.items():
            if bool(vertex_faces[v]) != was_boundary:affected.update(vertex_tets[v])
        for e, was_boundary in old_edges.items():
            if bool(edge_faces[e]) != was_boundary:affected.update(edge_tets[e])
        for u in sorted(affected):
            budget.tick();visits += 1
            if rows[u] is not None:
                versions[u] += 1
                b = eligible(u)
                if b:heappush(heap,(-b,u,versions[u]))
    survivors = [t for t in range(n) if rows[t] is not None]
    index = {t:i for i,t in enumerate(survivors)}
    result = []
    for t in survivors:
        budget.tick()
        result.append([None if r is None else dict(tetrahedron=index[r['tetrahedron']],
                      permutation=list(r['permutation'])) for r in rows[t]])
    return dict(triangulation=dict(tetrahedra=result),moves=moves,
                stats=dict(work=budget.work,initial_tetrahedra=n,remaining_tetrahedra=len(result),
                           moves=len(moves),boundary_one=kinds[1],boundary_two=kinds[2],
                           boundary_three=kinds[3],affected_visits=visits))
