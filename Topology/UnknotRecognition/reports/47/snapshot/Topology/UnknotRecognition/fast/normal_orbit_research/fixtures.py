"""Reproducible normal-surface fixtures and optional independent Regina adapters.

The Fibonacci layered-solid-torus family is the pre-existing fixture from
ProveIt's 20261008_compressed_certificates research package, normal_disks.tex.
It is reused for testing a new gluing extractor, not claimed as a new family.
"""


def layered_torus(size):
    if type(size) is not int or size < 1:
        raise ValueError("positive number of tetrahedra required")
    fib = [0, 1]
    for _ in range(size + 4):
        fib.append(fib[-1] + fib[-2])
    faces = [[None] * 4 for _ in range(size)]

    def pair(tetrahedron, face, target, permutation):
        inverse = [permutation.index(vertex) for vertex in range(4)]
        faces[tetrahedron][face] = {"tetrahedron": target, "permutation": permutation}
        faces[target][permutation[face]] = {"tetrahedron": tetrahedron, "permutation": inverse}

    for tetrahedron in range(size - 1):
        pair(tetrahedron, 0, tetrahedron + 1, [2, 1, 3, 0])
        pair(tetrahedron, 1, tetrahedron + 1, [0, 3, 1, 2])
    pair(size - 1, 0, size - 1, [1, 2, 3, 0])
    coordinates = [[fib[remaining + 1], fib[remaining + 1], 0, 0, 0, 0, fib[remaining]]
                   for remaining in range(size, 0, -1)]
    return {"tetrahedra": faces}, coordinates


def regina_triangulation(raw):
    import regina
    result = regina.Triangulation3()
    for _ in raw["tetrahedra"]:
        result.newTetrahedron()
    for index, faces in enumerate(raw["tetrahedra"]):
        for face, pairing in enumerate(faces):
            if pairing is not None and result.tetrahedron(index).adjacentTetrahedron(face) is None:
                result.tetrahedron(index).join(face, result.tetrahedron(pairing["tetrahedron"]),
                                               regina.Perm4(*pairing["permutation"]))
    return result


def export_triangulation(triangulation):
    return {"tetrahedra": [[None if tetrahedron.adjacentTetrahedron(face) is None else {
        "tetrahedron": tetrahedron.adjacentTetrahedron(face).index(),
        "permutation": [tetrahedron.adjacentGluing(face)[vertex] for vertex in range(4)]}
        for face in range(4)] for tetrahedron in triangulation.tetrahedra()]}


def export_surface(surface):
    return [[int(str(surface.triangles(tetrahedron, vertex))) for vertex in range(4)] +
            [int(str(surface.quads(tetrahedron, quad))) for quad in range(3)]
            for tetrahedron in range(surface.triangulation().size())]


def regina_surface(triangulation, coordinates):
    import regina
    return regina.NormalSurface(triangulation, regina.NormalCoords.Standard,
                               [regina.LargeInteger(str(value)) for row in coordinates for value in row])


def regina_components(triangulation, coordinates):
    surface = regina_surface(triangulation, coordinates)
    answer = []
    for component in surface.components():
        flat = [value for row in export_surface(component) for value in row]
        answer.append({"coordinates": flat, "euler": int(str(component.eulerChar())),
                       "orientable": component.isOrientable(),
                       "boundaries": component.countBoundaries(), "discs": sum(flat)})
    return sorted(answer, key=lambda item: tuple(item["coordinates"]))
