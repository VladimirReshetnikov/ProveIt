"""Independent replay of embedded boundary shellings in stable source indices.

No simplifier or external topology engine is imported. Vertex and edge
classes on surviving corners persist because their links remain connected
(or disappear) in these legal shellings.
"""
from .normal_surface_geometry import _prepare, _EDGES, _edge, NormalOrbitError


def verify_boundary_shellings(before, after, moves, *, check=lambda: None):
    check()
    try:p = _prepare(before,check)
    except NormalOrbitError:return False
    n = len(p['tetrahedra'])
    if (type(moves) is not list or len(moves) >= n
            or any(type(t) is not int or not 0 <= t < n for t in moves)):
        return False
    rows = [list(row) for row in p['tetrahedra']]
    vr, er = p['vertex_roots'], p['edge_roots']
    vb, eb = {}, {}
    for t, f in p['boundary_faces']:
        check()
        for v in range(4):
            if v != f:vb[vr[4*t+v]] = vb.get(vr[4*t+v],0)+1
        for a,b in _EDGES:
            if f not in (a,b):eb[er[_edge(t,a,b)]] = eb.get(er[_edge(t,a,b)],0)+1
    for t in moves:
        check()
        if rows[t] is None or len(set(vr[4*t:4*t+4])) != 4:return False
        boundary = [f for f,r in enumerate(rows[t]) if r is None]
        b = len(boundary)
        if not 1 <= b <= 3:return False
        if b == 1 and vb.get(vr[4*t+boundary[0]],0):return False
        if b == 2 and eb.get(er[_edge(t,*boundary)],0):return False
        # For one boundary facet the opposite vertex must be interior;
        # for two, their opposite edge must be interior. With three there
        # is no lower-dimensional boundary intersection left to exclude.
        removed_faces, exposed_faces = [], []
        for f,r in enumerate(rows[t]):
            check()
            if r is None:removed_faces.append((t,f))
            else:
                u,g = r['tetrahedron'],r['permutation'][f]
                if u == t or rows[u] is None:return False
                rows[u][g] = None
                exposed_faces.append((u,g))
        rows[t] = None
        for faces,sign in ((removed_faces,-1),(exposed_faces,1)):
            for u,f in faces:
                check()
                for v in range(4):
                    if v != f:
                        key=vr[4*u+v];vb[key]=vb.get(key,0)+sign
                for a,b in _EDGES:
                    if f not in (a,b):
                        key=er[_edge(u,a,b)];eb[key]=eb.get(key,0)+sign
    survivors = [t for t in range(n) if rows[t] is not None]
    if (type(after) is not dict or set(after) != {'tetrahedra'}
            or type(after['tetrahedra']) is not list or len(after['tetrahedra']) != len(survivors)):
        return False
    index = {t:i for i,t in enumerate(survivors)}
    for t,supplied in zip(survivors,after['tetrahedra']):
        check()
        if type(supplied) is not list or len(supplied) != 4:return False
        for r,s in zip(rows[t],supplied):
            if r is None:
                if s is not None:return False
            elif (type(s) is not dict or set(s) != {'tetrahedron','permutation'}
                  or type(s['tetrahedron']) is not int or s['tetrahedron'] != index[r['tetrahedron']]
                  or type(s['permutation']) is not list or len(s['permutation']) != 4
                  or any(type(v) is not int for v in s['permutation'])
                  or s['permutation'] != r['permutation']):return False
    check()
    return True
