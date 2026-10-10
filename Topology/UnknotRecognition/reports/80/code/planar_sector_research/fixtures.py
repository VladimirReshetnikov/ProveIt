"""Exact source fixtures and small independent oracle utilities.

``capped_fibonacci`` and the conversion/digest utilities are retained, with
attribution, from ``sector_envelope_research/fixtures.py`` in the incoming
``unknot_minimum_envelopes_20261009`` bundle (SHA-256
04a51853b437baec84226f87d3f1f4d87e35693aa3ea2339de6b80e8d923b6dc).
The second cap in ``double_capped_fibonacci`` is the present extension.

The base face pairings in that bundle follow the earlier
``fibonacci_fixture.py`` dual-certificates artifact.  Each cap is a tetrahedral
3-ball glued along one boundary triangle, preserving the solid torus.
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


def double_capped_fibonacci(base_tetrahedra, first_cap_type=1,
                            second_cap_type=1):
    """Two caps on the two original boundary faces of a Fibonacci solid torus.

    With both cap types 1, the supplied sector has matching nullity three and
    seven non-link standard rays.  This is a source family, not a synthetic
    post-elimination kernel.  The audit verifies its claims separately.
    """
    if type(second_cap_type) is not int or second_cap_type not in (0, 1, 2):
        raise ValueError('second_cap_type must be 0, 1, or 2')
    source = capped_fibonacci(base_tetrahedra, first_cap_type)
    faces = source['triangulation']['tetrahedra']
    second = len(faces)
    faces.append([None] * 4)
    faces[0][3] = dict(tetrahedron=second, permutation=[0, 1, 2, 3])
    faces[second][3] = dict(tetrahedron=0, permutation=[0, 1, 2, 3])
    source['allowed_types'].append((second, second_cap_type))
    source['first_cap_type'] = source.pop('cap_type')
    source['second_cap_type'] = second_cap_type
    return source


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


def fresh_standard(raw):
    """Complete standard-coordinate vertex list from the optional Regina oracle."""
    import regina
    triangulation = to_regina(raw)
    surfaces = regina.NormalSurfaces(triangulation, regina.NormalCoords.Standard)
    answer = []
    for index in range(surfaces.size()):
        surface = surfaces.surface(index)
        rows = [[int(str(surface.triangles(t, v))) for v in range(4)] +
                [int(str(surface.quads(t, q))) for q in range(3)]
                for t in range(triangulation.size())]
        answer.append(rows)
    return answer
