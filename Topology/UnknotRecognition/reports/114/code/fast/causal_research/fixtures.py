"""Exact six-tetrahedron descent gadgets in finite solid tori.

The named simplicial ball has two internal degree-four edges BC and CD.
An up move through BCD makes both edges degree three.  Collapsing them
reduces six original tetrahedra to five.  This module uses no Regina calls.
"""
from copy import deepcopy

from normal_orbit_research.fixtures import layered_torus


BALL_TETRAHEDRA = ('ABCD', 'EBCD', 'ABCX', 'EBCX', 'ACDY', 'ECDY')


def simplicial_ball():
    """Return the named six-tetrahedron ball and its inlet/outlet facets."""
    rows = [[None] * 4 for _ in BALL_TETRAHEDRA]
    facets = {}
    for i, tet in enumerate(BALL_TETRAHEDRA):
        for f in range(4):
            key = tuple(sorted(v for j, v in enumerate(tet) if j != f))
            facets.setdefault(key, []).append((i, f))
    for key, occurrences in facets.items():
        if len(occurrences) > 2:
            raise ArithmeticError('the supplied gadget is not a pseudomanifold')
        if len(occurrences) == 2:
            (a, f), (b, g) = occurrences
            perm = [g if j == f else BALL_TETRAHEDRA[b].index(v)
                    for j, v in enumerate(BALL_TETRAHEDRA[a])]
            rows[a][f] = dict(tetrahedron=b, permutation=perm)
            rows[b][g] = dict(tetrahedron=a,
                             permutation=[perm.index(j) for j in range(4)])
    return dict(tetrahedra=rows), (0, 2), (1, 2)


def attach_gadgets(count=1, *, base_tetrahedra=1):
    """Attach a chain of six-cell 3-balls to a layered solid torus.

    Every attachment identifies one boundary triangle, and all remaining
    boundary triangles are retained.  Each gadget has an untouched inlet
    ABD and outlet EBD.  Native finite-manifold validation and external
    Regina controls are performed by the audit, not trusted implicitly.
    """
    if type(count) is not int or count < 1:
        raise ValueError('count must be a positive integer')
    base, _ = layered_torus(base_tetrahedra)
    rows = deepcopy(base['tetrahedra'])
    anchor = next((i, f) for i, row in enumerate(rows)
                  for f, gluing in enumerate(row) if gluing is None)
    records = []
    for k in range(count):
        ball, inlet, outlet = simplicial_ball()
        start = len(rows)
        for row in ball['tetrahedra']:
            rows.append([None if entry is None else dict(
                tetrahedron=start + entry['tetrahedron'],
                permutation=list(entry['permutation'])) for entry in row])
        a, f = anchor
        b, g = start + inlet[0], inlet[1]
        target_vertices = [j for j in range(4) if j != g]
        perm = [g] * 4
        for j, image in zip((j for j in range(4) if j != f), target_vertices):
            perm[j] = image
        rows[a][f] = dict(tetrahedron=b, permutation=perm)
        rows[b][g] = dict(tetrahedron=a,
                         permutation=[perm.index(j) for j in range(4)])
        records.append(dict(index=k, tetrahedra=list(range(start, start + 6)),
                            inlet=[b, g], attachment=[a, f],
                            selected_up_face=[start, 0]))
        anchor = (start + outlet[0], outlet[1])
    return dict(triangulation=dict(tetrahedra=rows), base=base,
                named_ball=list(BALL_TETRAHEDRA), attachments=records)


def descent_gadgets(count=1, *, base_tetrahedra=1):
    """Return a native validated cochain source with count descent gadgets."""
    from fastunknot.normal_surface_geometry import _prepare
    from fastunknot.normal_cocycle import rank_one_cocycle_seed
    fixture = attach_gadgets(count, base_tetrahedra=base_tetrahedra)
    _prepare(fixture['triangulation'], lambda: None)
    fixture['heights'] = rank_one_cocycle_seed(fixture['triangulation'])['heights']
    return fixture
