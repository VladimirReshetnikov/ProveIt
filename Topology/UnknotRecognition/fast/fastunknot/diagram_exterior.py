"""Canonical finite knot exteriors, without an external topology engine.

The crossing cells are the Weeks bigon-collapse construction, expressed in
unoriented PD corners.  Each has finite poles 0,1 and knot vertices 2,3.
Truncating 2,3 and coning the face fans gives twenty finite tetrahedra per
cell.  See synthesis/diagram_exterior.tex for the topological justification.
This constructs geometry; it does not search for a normal compressing disc.
"""

from .diagram import Diagram


def _join(rows, t, f, u, permutation):
    g = permutation[f]
    if rows[t][f] is not None or rows[u][g] is not None:
        raise ArithmeticError('exterior face used twice')
    rows[t][f] = dict(tetrahedron=u, permutation=list(permutation))
    rows[u][g] = dict(tetrahedron=t,
                      permutation=[permutation.index(v) for v in range(4)])


def _corner_triangulation(diagram, check):
    # Revalidate even a Diagram assembled with the unchecked bare constructor.
    source = Diagram.from_pd(diagram.pd)
    check()
    # One Reidemeister-I curl represents the crossing-free circle.
    pd = source.pd or ((0, 1, 1, 0),)
    rows = [[None] * 4 for _ in range(4 * len(pd))]
    locations = {}
    for c, crossing in enumerate(pd):
        check()
        for j, edge in enumerate(crossing):
            locations.setdefault(edge, []).append((c, j))
            _join(rows, 4*c + (j-1) % 4, 1-j % 2,
                  4*c+j, (0, 1, 3, 2))
    for (c, j), (d, k) in locations.values():
        check()
        _join(rows, 4*c+j, 3, 4*d+(k-1) % 4, (0, 1, 3, 2))
        _join(rows, 4*d+k, 3, 4*c+(j-1) % 4, (0, 1, 3, 2))
    return rows


def _template():
    # Labels distinguish cell centres, old face centres, finite poles, and
    # directed-edge cut points.  They are local to one crossing cell.
    centre = ('c',)
    cells, old_faces = [], {}
    for f in range(4):
        cycle = [v for v in range(4) if v != f]
        polygon = []
        for i, v in enumerate(cycle):
            if v < 2:
                polygon.append(('v', v))
            else:
                polygon.extend((('e', v, cycle[(i-1) % 3]),
                                ('e', v, cycle[(i+1) % 3])))
        for i, point in enumerate(polygon):
            index = len(cells)
            cells.append((centre, ('f', f), point, polygon[(i+1) % len(polygon)]))
            old_faces[index] = f
    for v in (2, 3):
        cells.append((centre,) + tuple(('e', v, w) for w in range(4) if w != v))
    return tuple(cells), old_faces


def diagram_exterior(diagram, *, check=lambda: None):
    """Return the canonical compact exterior with 80*max(1,n) tetrahedra.

    ``diagram`` must supply a valid classical one-component PD.  Numbering is
    part of this API's contract.  No simplification or external engine runs.
    The returned face-pairing format is accepted by the native normal-surface
    APIs.  A cooperative cancellation callback is called throughout.
    """
    check()
    corners = _corner_triangulation(diagram, check)
    cells, old_faces = _template()
    width = len(cells)
    rows = [[None] * 4 for _ in range(width * len(corners))]
    internal, interfaces = {}, {}
    for i, cell in enumerate(cells):
        for f in range(4):
            face = frozenset(point for v, point in enumerate(cell) if v != f)
            if f == 0:
                if i in old_faces:
                    interfaces[old_faces[i], face] = i
            else:
                internal.setdefault(face, []).append((i, f))
    for c in range(len(corners)):
        check()
        for occurrences in internal.values():
            (i, f), (j, g) = occurrences
            permutation = [g if v == f else cells[j].index(point)
                           for v, point in enumerate(cells[i])]
            _join(rows, width*c+i, f, width*c+j, permutation)
        for (f, face), i in interfaces.items():
            record = corners[c][f]
            d, p = record['tetrahedron'], record['permutation']
            if (c, f) > (d, p[f]):
                continue
            def transport(point):
                return (point[0],) + tuple(p[v] for v in point[1:])
            mapped = frozenset(transport(point) for point in face)
            j = interfaces[p[f], mapped]
            permutation = [0] + [cells[j].index(transport(point))
                                  for point in cells[i][1:]]
            _join(rows, width*c+i, 0, width*d+j, permutation)
    check()
    return dict(tetrahedra=rows)
