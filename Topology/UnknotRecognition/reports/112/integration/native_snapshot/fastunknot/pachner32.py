"""A canonical 3-2 replacement about an interior degree-three edge.

The three tetrahedra must be distinct. Global vertices may be identified;
the formal bipyramid is replaced relative to its six boundary facets.
"""
from .normal_cocycle import _Budget
from .normal_surface_geometry import _prepare, _edge, _EDGES, NormalOrbitError


def pachner_32(triangulation, tetrahedron, vertices, *, max_work=None, check=lambda:None):
    """Return a fresh triangulation and a formal-region replacement proof."""
    if (type(tetrahedron) is not int or tetrahedron < 0
            or type(vertices) is not list or len(vertices) != 2
            or any(type(v) is not int or not 0 <= v < 4 for v in vertices)
            or vertices[0] == vertices[1]):
        raise ValueError('expected a tetrahedron index and two distinct local vertices')
    budget = _Budget(check,max_work)
    p = _prepare(triangulation,budget.tick)
    rows = p['tetrahedra']
    if tetrahedron >= len(rows):
        raise ValueError('tetrahedron index is out of range')
    root = p['edge_roots'][_edge(tetrahedron,*vertices)]
    occurrences = []
    for local,edge in enumerate(p['edge_roots']):
        budget.tick()
        if edge == root:
            occurrences.append((local//6,*_EDGES[local%6]))
    if len(occurrences) != 3 or len({t for t,a,b in occurrences}) != 3:
        raise NormalOrbitError('3-2 move requires an edge of degree three in distinct tetrahedra')
    selected = {t for t,a,b in occurrences}
    a,b = vertices
    labels = [-1]*4
    labels[a],labels[b] = 3,4
    for i,v in enumerate(v for v in range(4) if v not in vertices):
        labels[v] = i
    region = {tetrahedron:labels}
    # Propagate the two apex labels and the shared belt vertex through each
    # interior face. The new corner is the third belt label. Every interior
    # face is then checked again after all three tetrahedra are labelled.
    queue = [tetrahedron]
    for t in queue:
        for f in range(4):
            budget.tick()
            if region[t][f] in (3,4):
                continue
            r = rows[t][f]
            if r is None or r['tetrahedron'] not in selected:
                raise NormalOrbitError('3-2 edge is not an interior triangular bipyramid')
            u,perm = r['tetrahedron'],r['permutation']
            if u not in region:
                other = [-1]*4
                for v in range(4):
                    if v != f:other[perm[v]] = region[t][v]
                present = set(region[t]) & {0,1,2}
                other[perm[f]] = next(iter({0,1,2}-present))
                region[u] = other
                queue.append(u)
            elif any(region[t][v] != region[u][perm[v]] for v in range(4) if v != f):
                raise NormalOrbitError('3-2 edge has inconsistent belt identifications')
    expected = {frozenset((3,4,0,1)),frozenset((3,4,1,2)),frozenset((3,4,2,0))}
    if set(region) != selected or {frozenset(row) for row in region.values()} != expected:
        raise NormalOrbitError('3-2 edge does not have a three-triangle link')
    new = ((0,1,2,3),(0,1,2,4))
    survivors = [t for t in range(len(rows)) if t not in region]
    index = {t:i for i,t in enumerate(survivors)}
    start = len(survivors)
    result = []
    for t in survivors:
        budget.tick()
        result.append([None if r is None or r['tetrahedron'] in region else
                       dict(tetrahedron=index[r['tetrahedron']],permutation=list(r['permutation'])) for r in rows[t]])
    result.extend([[None]*4 for _ in new])
    facets = {}
    for i,labels in enumerate(new):
        for f in range(4):
            facets.setdefault(tuple(sorted(labels[v] for v in range(4) if v != f)),[]).append((start+i,f))

    def join(t,f,u,g,mapping):
        perm = [g]*4
        for v,w in mapping:perm[v] = w
        result[t][f] = dict(tetrahedron=u,permutation=perm)
        result[u][g] = dict(tetrahedron=t,permutation=[perm.index(v) for v in range(4)])

    join(start,3,start+1,3,[(v,v) for v in range(3)])
    boundary = {}
    for t,labels in region.items():
        for f in range(4):
            if labels[f] in (3,4):
                key = tuple(sorted(labels[v] for v in range(4) if v != f))
                boundary[t,f] = facets[key][0]
    for (t,f),(target,g) in boundary.items():
        budget.tick()
        r = rows[t][f]
        if r is None:continue
        u,perm = r['tetrahedron'],r['permutation']
        if u in region:
            other,k = boundary[u,perm[f]]
            mapping = [(new[target-start].index(region[t][v]),new[other-start].index(region[u][perm[v]]))
                       for v in range(4) if v != f]
        else:
            other,k = index[u],perm[f]
            mapping = [(new[target-start].index(region[t][v]),perm[v]) for v in range(4) if v != f]
        join(target,g,other,k,mapping)
    budget.tick()
    proof = dict(schema='pachner-32-v1',region=[dict(tetrahedron=t,vertices=region[t]) for t in sorted(region)])
    return dict(triangulation=dict(tetrahedra=result),certificate=proof,
                stats=dict(work=budget.work,initial_tetrahedra=len(rows),remaining_tetrahedra=len(result)))
