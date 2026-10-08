"""Exact layered-solid-torus inputs for normal-disc certificate experiments.

This generator uses only integer arithmetic.  The optional Regina adapters
are independent cross-checks and are not needed to regenerate the fixtures.
"""


def fibonacci(index):
    if type(index) is not int or index < 0:
        raise ValueError('a nonnegative Fibonacci index is required')
    left, right = 0, 1
    for _ in range(index):
        left, right = right, left + right
    return left


def layered_torus(tetrahedra):
    """Return a face pairing and a primitive normal meridian vector.

    The boundary slopes are F_(t+1), F_(t+2), F_(t+3); the last
    tetrahedron is the core of the solid torus.  The vector contains
    F_(t+5)-5 normal discs but has just 7t binary integer coordinates.
    """
    if type(tetrahedra) is not int or tetrahedra < 1:
        raise ValueError('a positive tetrahedron count is required')
    numbers = [fibonacci(i) for i in range(tetrahedra + 6)]
    faces, coordinates = [], []
    for index in range(tetrahedra):
        if index + 1 == tetrahedra:
            row = [dict(tetrahedron=index, permutation=[1, 2, 3, 0]),
                   dict(tetrahedron=index, permutation=[3, 0, 1, 2])]
        else:
            row = [dict(tetrahedron=index + 1, permutation=[2, 1, 3, 0]),
                   dict(tetrahedron=index + 1, permutation=[0, 3, 1, 2])]
        if index == 0:
            row.extend([None, None])
        else:
            row.extend([dict(tetrahedron=index - 1, permutation=[3, 1, 0, 2]),
                        dict(tetrahedron=index - 1, permutation=[0, 2, 3, 1])])
        faces.append(row)
        height = tetrahedra - index
        coordinates.append([numbers[height + 1], numbers[height + 1],
                            0, 0, 0, 0, numbers[height]])
    assert sum(map(sum, coordinates)) == numbers[tetrahedra + 5] - 5
    return {'tetrahedra': faces}, coordinates


def regina_triangulation(face_pairing):
    """Import a supplied face pairing, without using its construction history."""
    import regina

    result = regina.Triangulation3()
    for _ in face_pairing['tetrahedra']:
        result.newTetrahedron()
    for index, row in enumerate(face_pairing['tetrahedra']):
        for face, gluing in enumerate(row):
            if gluing is not None and result.tetrahedron(index).adjacentTetrahedron(face) is None:
                result.tetrahedron(index).join(
                    face, result.tetrahedron(gluing['tetrahedron']),
                    regina.Perm4(*gluing['permutation']))
    return result


def regina_surface(triangulation, coordinates):
    import regina

    vector = [regina.LargeInteger(str(value)) for row in coordinates for value in row]
    return regina.NormalSurface(triangulation, regina.NormalCoords.Standard, vector)


def export_triangulation(triangulation):
    return {'tetrahedra': [[
        None if tetrahedron.adjacentTetrahedron(face) is None else dict(
            tetrahedron=tetrahedron.adjacentTetrahedron(face).index(),
            permutation=[tetrahedron.adjacentGluing(face)[vertex] for vertex in range(4)])
        for face in range(4)] for tetrahedron in triangulation.tetrahedra()]}


def export_surface(surface):
    return [[int(str(surface.triangles(tetrahedron, vertex))) for vertex in range(4)] +
            [int(str(surface.quads(tetrahedron, quadrilateral))) for quadrilateral in range(3)]
            for tetrahedron in range(surface.triangulation().size())]
