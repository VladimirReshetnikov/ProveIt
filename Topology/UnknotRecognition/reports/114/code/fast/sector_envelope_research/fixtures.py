"""Exact capped Fibonacci solid tori and retained source utilities.

The base face pairings follow the fibonacci_fixture.py file distributed in
the incoming 2026-10-09 dual-certificates report.  The added tetrahedron is a
3-ball attached along a boundary triangle, so it preserves the solid torus.
"""

from hashlib import sha256
import json


def capped_fibonacci(base_tetrahedra, cap_type=1):
    if type(base_tetrahedra) is not int or base_tetrahedra < 1:
        raise ValueError('base_tetrahedra must be a positive integer')
    if type(cap_type) is not int or cap_type not in (0, 1, 2):
        raise ValueError('cap_type must be 0, 1, or 2')
    n = base_tetrahedra
    faces = [[None] * 4 for _ in range(n + 1)]

    def join(source, face, target, permutation):
        opposite = permutation[face]
        inverse = [permutation.index(v) for v in range(4)]
        faces[source][face] = dict(tetrahedron=target, permutation=permutation)
        faces[target][opposite] = dict(tetrahedron=source, permutation=inverse)

    for tetrahedron in range(n - 1):
        join(tetrahedron, 0, tetrahedron + 1, [2, 1, 3, 0])
        join(tetrahedron, 1, tetrahedron + 1, [0, 3, 1, 2])
    join(n - 1, 0, n - 1, [1, 2, 3, 0])
    join(0, 2, n, [0, 1, 2, 3])
    return dict(triangulation=dict(tetrahedra=faces),
                allowed_types=[(i, 2) for i in range(n)] + [(n, cap_type)],
                base_tetrahedra=n, cap_type=cap_type)


def vector_key(rows):
    return tuple(value for row in rows for value in row)


def ray_digest(rays):
    canonical = sorted(vector_key(rows) for rows in rays)
    wire = json.dumps(canonical, separators=(',', ':')).encode('ascii')
    return sha256(wire).hexdigest()


def to_regina(raw):
    import regina
    triangulation = regina.Triangulation3()
    for _ in raw['tetrahedra']:
        triangulation.newTetrahedron()
    for i, faces in enumerate(raw['tetrahedra']):
        for face, target in enumerate(faces):
            if target is None:
                continue
            tetrahedron = triangulation.tetrahedron(i)
            if tetrahedron.adjacentTetrahedron(face) is None:
                tetrahedron.join(face, triangulation.tetrahedron(target['tetrahedron']),
                                 regina.Perm4(*target['permutation']))
    return triangulation
