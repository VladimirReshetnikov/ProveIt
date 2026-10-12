"""Connected solid-torus sources with many independent Q-matching blocks.

The initial nine-tetrahedron torus is the staircase triangulation of
a triangular disk times a three-edge circle.  All its boundary triangles
are embedded.  Each subsequent three-tet piece is a triangular bipyramid
ball, attached along an embedded boundary triangle.  Attaching these balls
preserves the solid torus.

For a triangular equator the allowed quadrilaterals are (1, 1, 2), giving
q_0 + q_1 = q_2 in each ball.  An equator of size s instead gives
q_0 + q_1 = q_2 + ... + q_(s-1).  At s=4 every coordinate inequality is
an irredundant facet.  All Q coordinates outside these balls are forbidden.
"""


def capped_bipyramid_chain(balls, equator=3):
    if type(balls) is not int or balls < 0:
        raise ValueError('balls must be a nonnegative integer')
    if type(equator) is not int or equator < 3:
        raise ValueError('equator must be an integer at least three')
    simplices = []
    for level in range(3):
        a, b, c = (3 * level + j for j in range(3))
        upper_a, upper_b, upper_c = (3 * ((level + 1) % 3) + j for j in range(3))
        simplices.extend(((a, b, c, upper_c), (a, b, upper_b, upper_c),
                          (a, upper_a, upper_b, upper_c)))
    faces = [[None] * 4 for _ in simplices]

    def join(t, face, u, opposite, permutation=None):
        if faces[t][face] is not None or faces[u][opposite] is not None:
            raise ArithmeticError('fixture attempts to pair an occupied face')
        if permutation is None:
            permutation = [opposite] * 4
            for a, b in zip((v for v in range(4) if v != face),
                            (v for v in range(4) if v != opposite)):
                permutation[a] = b
        inverse = [permutation.index(v) for v in range(4)]
        faces[t][face] = dict(tetrahedron=u, permutation=permutation)
        faces[u][opposite] = dict(tetrahedron=t, permutation=inverse)

    pending = {}
    for t, simplex in enumerate(simplices):
        for face in range(4):
            key = tuple(sorted(vertex for local, vertex in enumerate(simplex) if local != face))
            if key not in pending:
                pending[key] = (t, face)
                continue
            u, opposite = pending.pop(key)
            other = simplices[u]
            permutation = [other.index(vertex) if local != face else opposite
                           for local, vertex in enumerate(simplex)]
            join(t, face, u, opposite, permutation)
    port = min(pending.values())
    support = []
    for _ in range(balls):
        new = len(faces)
        faces.extend([[None] * 4 for _ in range(equator)])
        # Tetrahedra (D,E,V_i,V_(i+1)) around the interior edge DE.
        for local in range(equator):
            join(new + local, 2, new + (local + 1) % equator, 3, [0, 1, 3, 2])
        join(*port, new, 0)
        port = (new + 1, 1)
        support.extend((new + local, typ)
                       for local, typ in enumerate((1, 1) + (2,) * (equator - 2)))
    return dict(triangulation=dict(tetrahedra=faces), allowed_types=support,
                balls=balls, equator=equator)


def fibonacci_solid_torus(tetrahedra):
    """Uncapped retained layered family, reproduced without optional packages."""
    if type(tetrahedra) is not int or tetrahedra < 1:
        raise ValueError('tetrahedra must be positive')
    faces = [[None] * 4 for _ in range(tetrahedra)]

    def join(t, face, u, permutation):
        opposite = permutation[face]
        faces[t][face] = dict(tetrahedron=u, permutation=permutation)
        faces[u][opposite] = dict(tetrahedron=t,
                                  permutation=[permutation.index(v) for v in range(4)])

    for t in range(tetrahedra - 1):
        join(t, 0, t + 1, [2, 1, 3, 0])
        join(t, 1, t + 1, [0, 3, 1, 2])
    join(tetrahedra - 1, 0, tetrahedra - 1, [1, 2, 3, 0])
    return dict(tetrahedra=faces)
