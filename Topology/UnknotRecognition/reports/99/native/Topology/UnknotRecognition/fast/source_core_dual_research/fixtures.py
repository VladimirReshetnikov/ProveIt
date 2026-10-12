"""Pure-Python finite 1-to-4 subdivisions for multiple interior vertices."""

from normal_orbit_research.fixtures import layered_torus


def subdivide_first_tetrahedron(raw):
    """Stellar-subdivide tetrahedron zero, retaining all old face gluings.

    The four children are indexed by their outer old face.  Local vertex zero
    is the new centre; the remaining local vertices are the sorted vertices
    on that old face.  This is an actual relative tetrahedral subdivision.
    """
    old = raw['tetrahedra']
    start = len(old) - 1
    labels = [[4] + [v for v in range(4) if v != f] for f in range(4)]
    inverses = [{v: j for j, v in enumerate(row)} for row in labels]
    new = []
    for tet in old[1:]:
        faces = []
        for f, record in enumerate(tet):
            if record is None:
                faces.append(None)
                continue
            u, p = record['tetrahedron'], record['permutation']
            if u:
                faces.append(dict(tetrahedron=u - 1, permutation=p.copy()))
            else:
                target = p[f]
                perm = [0 if v == f else inverses[target][p[v]] for v in range(4)]
                faces.append(dict(tetrahedron=start + target, permutation=perm))
        new.append(faces)
    for face, row in enumerate(labels):
        record = old[0][face]
        if record is None:
            faces = [None]
        else:
            u, p = record['tetrahedron'], record['permutation']
            if u:
                perm = [p[face]] + [p[v] for v in row[1:]]
                faces = [dict(tetrahedron=u - 1, permutation=perm)]
            else:
                target = p[face]
                perm = [0] + [inverses[target][p[v]] for v in row[1:]]
                faces = [dict(tetrahedron=start + target, permutation=perm)]
        for omitted in row[1:]:
            target = omitted
            perm = [inverses[target][face] if v == omitted else inverses[target][v]
                    for v in row]
            faces.append(dict(tetrahedron=start + target, permutation=perm))
        new.append(faces)
    return {'tetrahedra': new}


def stellar_torus(interior_vertices):
    """Return a genus-one source with k interior vertices and 1+3k cells."""
    if type(interior_vertices) is not int or interior_vertices < 0:
        raise ValueError('interior_vertices must be a nonnegative integer')
    raw, _ = layered_torus(1)
    for _ in range(interior_vertices):
        raw = subdivide_first_tetrahedron(raw)
    return raw, [[0] * 7 for _ in raw['tetrahedra']]
