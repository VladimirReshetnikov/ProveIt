"""Geometrically explicit boundary buds for unused-handle experiments.

Every new tetrahedron is attached along an embedded boundary triangle.
The first triangle has three distinct quotient vertices.  Subsequently,
the next triangle has two of those vertices and the new vertex, so it
remains embedded.  This is an elementary boundary shelling, preserves the
manifold, and gives one additional unused dual one-handle and zero-handle.
"""

from copy import deepcopy

from fastunknot.normal_surface_geometry import _prepare

from unused_handles import _exact_equal


def boundary_bud_chain(triangulation, count):
    if type(count) is not int or count < 0:
        raise ValueError('count must be a nonnegative integer')
    prepared = _prepare(triangulation, lambda: None)
    eligible = [
        (tetrahedron, face) for tetrahedron, face in prepared['boundary_faces']
        if len({prepared['vertex_roots'][4 * tetrahedron + vertex]
                for vertex in range(4) if vertex != face}) == 3
    ]
    if not eligible:
        raise ValueError('no embedded boundary triangle with distinct vertices')
    raw = deepcopy(triangulation)
    tetrahedron, face = eligible[0]
    moves = []
    for _ in range(count):
        new = len(raw['tetrahedra'])
        rows = [None] * 4
        rows[face] = dict(tetrahedron=tetrahedron, permutation=[0, 1, 2, 3])
        raw['tetrahedra'][tetrahedron][face] = dict(
            tetrahedron=new, permutation=[0, 1, 2, 3]
        )
        raw['tetrahedra'].append(rows)
        moves.append(dict(tetrahedron=tetrahedron, face=face, new_tetrahedron=new))
        tetrahedron, face = new, (face + 1) % 4
    return raw, dict(schema='boundary-bud-chain-v1', moves=moves)


def verify_boundary_bud_chain(original, extended, certificate):
    """Check reverse elementary shellings, independent of the forward producer."""
    try:
        return _verify_boundary_bud_chain(original, extended, certificate)
    except (KeyError, IndexError, TypeError, ValueError):
        return False


def _verify_boundary_bud_chain(original, extended, certificate):
    if type(certificate) is not dict or set(certificate) != {'schema', 'moves'}:
        return False
    if certificate['schema'] != 'boundary-bud-chain-v1':
        return False
    moves = certificate['moves']
    if type(moves) is not list:
        return False
    prepared = _prepare(original, lambda: None)
    raw = deepcopy(extended)
    for move in reversed(moves):
        if type(move) is not dict or set(move) != {'tetrahedron', 'face', 'new_tetrahedron'}:
            return False
        tetrahedron, face, new = (move[key] for key in
                                  ('tetrahedron', 'face', 'new_tetrahedron'))
        if any(type(value) is not int for value in (tetrahedron, face, new)):
            return False
        if new != len(raw['tetrahedra']) - 1 or not 0 <= tetrahedron < new or not 0 <= face < 4:
            return False
        row = raw['tetrahedra'][new]
        if type(row) is not list or len(row) != 4:
            return False
        attachments = [[side, record] for side, record in enumerate(row) if record is not None]
        if not _exact_equal(attachments, [[face, dict(
                tetrahedron=tetrahedron, permutation=[0, 1, 2, 3])]]):
            return False
        if not _exact_equal(raw['tetrahedra'][tetrahedron][face], dict(
            tetrahedron=new, permutation=[0, 1, 2, 3]
        )):
            return False
        raw['tetrahedra'].pop()
        raw['tetrahedra'][tetrahedron][face] = None
    if not _exact_equal(raw, original):
        return False
    if not moves:
        return True
    first = moves[0]
    face = first['face']
    tetrahedron = first['tetrahedron']
    if (tetrahedron, face) not in prepared['boundary_faces']:
        return False
    if len({prepared['vertex_roots'][4 * tetrahedron + vertex]
            for vertex in range(4) if vertex != face}) != 3:
        return False
    # Each forward attachment thereafter must use the immediately previous
    # tetrahedron on a different face.  It then has two old and one new vertex.
    for previous, following in zip(moves, moves[1:]):
        if following['tetrahedron'] != previous['new_tetrahedron']:
            return False
        if following['face'] == previous['face']:
            return False
    return True
