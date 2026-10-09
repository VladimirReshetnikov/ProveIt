"""Canonical finite knot exteriors, without an external topology engine.

The crossing cells are the Weeks bigon-collapse construction, expressed in
unoriented PD corners.  Each has finite poles 0,1 and knot vertices 2,3.
Truncating 2,3 and pulling from pole 0 gives five finite tetrahedra per cell.
The earlier centred subdivision is also supported.  See
synthesis/diagram_exterior.tex for the topological justification.
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


def _template(subdivision):
    # Labels distinguish cell centres, old face centres, finite poles, and
    # directed-edge cut points.  They are local to one crossing cell.
    if subdivision == 'pulling':
        north, south = ('v', 0), ('v', 1)
        a, b, c = ('e', 2, 0), ('e', 2, 1), ('e', 2, 3)
        d, e, f = ('e', 3, 0), ('e', 3, 1), ('e', 3, 2)
        return ((north, south, b, c), (north, south, c, f),
                (north, south, f, e), (north, a, b, c), (north, d, e, f))
    centre = ('c',)
    cells = []
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
            cells.append((centre, ('f', f), point, polygon[(i+1) % len(polygon)]))
    for v in (2, 3):
        cells.append((centre,) + tuple(('e', v, w) for w in range(4) if w != v))
    return tuple(cells)


def diagram_exterior(diagram, *, subdivision='pulling', check=lambda: None):
    """Return the canonical compact exterior with 20*max(1,n) tetrahedra.

    ``diagram`` must supply a valid classical one-component PD.  Numbering is
    part of this API's contract.  No simplification or external engine runs.
    The returned face-pairing format is accepted by the native normal-surface
    APIs.  A cooperative cancellation callback is called throughout.
    ``subdivision='centred'`` retains the first 80*max(1,n) construction.
    """
    check()
    if subdivision not in ('pulling', 'centred'):
        raise ValueError('unknown exterior subdivision')
    corners = _corner_triangulation(diagram, check)
    cells = _template(subdivision)
    width = len(cells)
    rows = [[None] * 4 for _ in range(width * len(corners))]
    internal, interfaces = {}, {}
    def support(point):
        if point[0] == 'c':
            return set(range(4))
        if point[0] == 'f':
            return set(range(4)) - {point[1]}
        return set(point[1:])
    for i, cell in enumerate(cells):
        for f in range(4):
            face = frozenset(point for v, point in enumerate(cell) if v != f)
            missing = set(range(4)) - set().union(*(support(point) for point in face))
            if missing:
                side, = missing
                interfaces[side, face] = i, f
            elif (all(point[0] == 'e' for point in face)
                  and len({point[1] for point in face}) == 1):
                continue  # A knot-vertex truncation triangle stays boundary.
            else:
                internal.setdefault(face, []).append((i, f))
    for c in range(len(corners)):
        check()
        for occurrences in internal.values():
            (i, f), (j, g) = occurrences
            permutation = [g if v == f else cells[j].index(point)
                           for v, point in enumerate(cells[i])]
            _join(rows, width*c+i, f, width*c+j, permutation)
        for (side, face), (i, f) in interfaces.items():
            record = corners[c][side]
            d, p = record['tetrahedron'], record['permutation']
            if (c, side) > (d, p[side]):
                continue
            def transport(point):
                return (point[0],) + tuple(p[v] for v in point[1:])
            mapped = frozenset(transport(point) for point in face)
            j, g = interfaces[p[side], mapped]
            permutation = [g if v == f else cells[j].index(transport(point))
                           for v, point in enumerate(cells[i])]
            _join(rows, width*c+i, f, width*d+j, permutation)
    check()
    return dict(tetrahedra=rows)
