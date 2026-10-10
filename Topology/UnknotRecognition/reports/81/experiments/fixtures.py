"""Reproducible genuine triangulations and canonical ray hashes.

The layered-torus face convention follows the preceding Minimum Envelopes
package (2026-10-09).  Two boundary tetrahedra supply a three-parameter sector.
"""

from hashlib import sha256
import json


def double_capped_fibonacci(n, cap_types=(1, 1)):
    if type(n) is not int or n < 1:
        raise ValueError('n must be positive')
    if len(cap_types) != 2 or any(type(x) is not int or x not in (0, 1, 2)
                                  for x in cap_types):
        raise ValueError('two quadrilateral types are required')
    faces = [[None] * 4 for _ in range(n + 2)]

    def join(i, f, j, p):
        g = p[f]
        faces[i][f] = dict(tetrahedron=j, permutation=list(p))
        faces[j][g] = dict(tetrahedron=i, permutation=[p.index(v) for v in range(4)])

    for i in range(n - 1):
        join(i, 0, i + 1, [2, 1, 3, 0])
        join(i, 1, i + 1, [0, 3, 1, 2])
    join(n - 1, 0, n - 1, [1, 2, 3, 0])
    join(0, 2, n, [0, 1, 2, 3])
    join(0, 3, n + 1, [0, 1, 2, 3])
    return dict(id=f'double_cap_{n}_{cap_types[0]}_{cap_types[1]}',
                triangulation=dict(tetrahedra=faces),
                allowed_types=[(i, 2) for i in range(n)]
                    + [(n, cap_types[0]), (n + 1, cap_types[1])])


def vector_key(rows):
    return tuple(x for row in rows for x in row)


def ray_digest(rows):
    wire = json.dumps(sorted(vector_key(row) for row in rows),
                      separators=(',', ':')).encode('ascii')
    return sha256(wire).hexdigest()


def occupied(rows):
    return tuple((i, q) for i, row in enumerate(rows) for q in range(3) if row[4 + q])


def to_regina(raw):
    import regina
    tri = regina.Triangulation3()
    for _ in raw['tetrahedra']:
        tri.newTetrahedron()
    for i, faces in enumerate(raw['tetrahedra']):
        for f, pair in enumerate(faces):
            if pair is not None and tri.tetrahedron(i).adjacentTetrahedron(f) is None:
                tri.tetrahedron(i).join(f, tri.tetrahedron(pair['tetrahedron']),
                                       regina.Perm4(*pair['permutation']))
    return tri


def fresh_standard(raw):
    import regina
    tri = to_regina(raw)
    assert tri.isValid() and tri.isOrientable() and not tri.isIdeal()
    surfaces = regina.NormalSurfaces(tri, regina.NormalCoords.Standard)
    return {tuple(int(str(surface.triangles(i, j))) if j < 4
                  else int(str(surface.quads(i, j - 4)))
                  for i in range(tri.size()) for j in range(7))
            for surface in surfaces}
