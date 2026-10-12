"""Native source fixtures for dual 2/3 cancellation regression and benchmarks.

The stored loop fixture was exported from Regina 7.4 after one 2/3 Pachner
move on the existing interior-vertex solid torus. Regeneration and all
subsequent subdivisions below require only integer face-pairing operations.
"""

from copy import deepcopy

from fastunknot.normal_surface_geometry import _prepare, _quad
from normal_orbit_research.fixtures import interior_vertex_torus


def interior_loop_torus():
    """A five-tetrahedron solid torus with a loop at its interior vertex."""
    specifications = [
        [(4, [1, 2, 3, 0]), (2, [1, 0, 2, 3]), (1, [0, 1, 3, 2]), None],
        [(2, [3, 2, 0, 1]), (3, [1, 0, 2, 3]), None, (0, [0, 1, 3, 2])],
        [(0, [1, 0, 2, 3]), (4, [0, 3, 2, 1]), (3, [0, 1, 3, 2]),
         (1, [2, 3, 1, 0])],
        [(1, [1, 0, 2, 3]), (4, [0, 2, 1, 3]), (4, [1, 3, 0, 2]),
         (2, [0, 1, 3, 2])],
        [(3, [2, 0, 3, 1]), (0, [3, 0, 1, 2]), (3, [0, 2, 1, 3]),
         (2, [0, 3, 2, 1])],
    ]
    return {'tetrahedra': [[None if item is None else
                           dict(tetrahedron=item[0], permutation=item[1])
                           for item in row] for row in specifications]}


def stellar_subdivision(raw, tetrahedron):
    """Perform one exact interior 1/4 subdivision of a source tetrahedron."""
    faces = deepcopy(raw['tetrahedra'])
    original = deepcopy(faces[tetrahedron])
    n = len(faces)
    children = [tetrahedron, n, n + 1, n + 2]
    for t, row in enumerate(faces):
        if t == tetrahedron:
            continue
        for f, entry in enumerate(row):
            if entry is not None and entry['tetrahedron'] == tetrahedron:
                entry['tetrahedron'] = children[entry['permutation'][f]]
    faces.extend([None, None, None])
    for omitted, child in enumerate(children):
        row = []
        for face in range(4):
            if face == omitted:
                entry = deepcopy(original[face])
                if entry is not None and entry['tetrahedron'] == tetrahedron:
                    entry['tetrahedron'] = children[entry['permutation'][face]]
            else:
                permutation = list(range(4))
                permutation[face], permutation[omitted] = omitted, face
                entry = dict(tetrahedron=children[face], permutation=permutation)
            row.append(entry)
        faces[child] = row
    return {'tetrahedra': faces}


def nested_interior_torus(subdivisions):
    """Subdivide chambers with fewest boundary vertices, reaching the interior."""
    raw, _ = interior_vertex_torus()
    for _ in range(subdivisions):
        source = _prepare(raw, lambda: None)
        border = {source['vertex_roots'][4 * t + v]
                  for t, f in source['boundary_faces']
                  for v in range(4) if v != f}
        chosen = min(range(len(raw['tetrahedra'])), key=lambda t:
                     (sum(source['vertex_roots'][4 * t + v] in border
                          for v in range(4)), t))
        raw = stellar_subdivision(raw, chosen)
    return raw


def vertex_link_coordinates(raw, *, interior=0, boundary=0):
    """Sum equal numbers of source interior or boundary vertex links."""
    source = _prepare(raw, lambda: None)
    boundary_roots = {source['vertex_roots'][4 * t + v]
                      for t, f in source['boundary_faces']
                      for v in range(4) if v != f}
    return [[boundary if source['vertex_roots'][4 * t + v] in boundary_roots
             else interior for v in range(4)] + [0, 0, 0]
            for t in range(len(raw['tetrahedra']))]


def relabel(raw, rows, tetrahedra, vertices):
    """Relabel tetrahedra and their vertices without changing the normal cut."""
    n = len(rows)
    result, coordinates = [None] * n, [None] * n
    for t, old in enumerate(raw['tetrahedra']):
        p = vertices[t]
        faces = [None] * 4
        for f, gluing in enumerate(old):
            if gluing is None:
                continue
            u = gluing['tetrahedron']
            new_gluing = [None] * 4
            for v in range(4):
                new_gluing[p[v]] = vertices[u][gluing['permutation'][v]]
            faces[p[f]] = dict(tetrahedron=tetrahedra[u], permutation=new_gluing)
        row = [0] * 7
        for v in range(4):
            row[p[v]] = rows[t][v]
        for q in range(3):
            row[4 + _quad(p[0], p[q + 1])] = rows[t][4 + q]
        result[tetrahedra[t]], coordinates[tetrahedra[t]] = faces, row
    return {'tetrahedra': result}, coordinates
