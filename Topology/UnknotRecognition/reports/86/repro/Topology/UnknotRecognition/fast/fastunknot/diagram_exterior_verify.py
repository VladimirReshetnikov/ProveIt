"""Independent local-coordinate replay of the canonical diagram exterior.

No construction routines or external topology engine are imported.  The
checker uses integer barycentric coordinates in a tetrahedron of total 12,
with knot vertices cut at coordinate 8.  It accepts canonical numbering only.
"""

from .diagram import Diagram, DiagramError


def _local_geometry(subdivision='pulling'):
    north, south = (12, 0, 0, 0), (0, 12, 0, 0)
    a, b, c = (4, 0, 8, 0), (0, 4, 8, 0), (0, 0, 8, 4)
    d, e, f = (4, 0, 0, 8), (0, 4, 0, 8), (0, 0, 4, 8)
    if subdivision == 'pulling':
        # Pull the old face opposite north from south, and cone those three
        # triangles and the two cut triangles to north.
        base = (b, c, f, e)
        return [(north, south, left, right) for left, right in zip(base, base[1:])] + [
            (north, a, b, c), (north, d, e, f)]
    polygons = ((south, b, c, f, e), (north, a, c, f, d),
                (north, south, e, d), (north, south, b, a))
    centre = (3, 3, 3, 3)
    tetrahedra = []
    for opposite, polygon in enumerate(polygons):
        middle = tuple(0 if v == opposite else 4 for v in range(4))
        for left, right in zip(polygon, polygon[1:] + polygon[:1]):
            tetrahedra.append((centre, middle, left, right))
    tetrahedra.extend(((centre, a, b, c), (centre, d, e, f)))
    return tetrahedra


def verify_diagram_exterior(diagram, triangulation, *, check=lambda: None):
    """Check every face against the source PD and the finite geometric cells.

    A true result certifies this canonical face pairing as a compact exterior
    of the supplied classical knot, under the Weeks construction theorem.
    Both the current pulling and original centred subdivisions are accepted.
    It does not certify a disc, a solid torus, or arbitrary retriangulations.
    Malformed data return False; cancellation raised by ``check`` propagates.
    """
    check()
    try:
        source = Diagram.from_pd(diagram.pd)
    except (DiagramError, AttributeError, TypeError):
        return False
    pd = source.pd or ((0, 1, 1, 0),)
    if (type(triangulation) is not dict or set(triangulation) != {'tetrahedra'}
            or type(triangulation['tetrahedra']) is not list
            or len(triangulation['tetrahedra']) not in (20 * len(pd), 80 * len(pd))):
        return False
    rows = triangulation['tetrahedra']
    for row in rows:
        check()
        if type(row) is not list or len(row) != 4:
            return False
        for record in row:
            if record is not None and (
                    type(record) is not dict
                    or set(record) != {'tetrahedron', 'permutation'}
                    or type(record['tetrahedron']) is not int
                    or not 0 <= record['tetrahedron'] < len(rows)
                    or type(record['permutation']) is not list
                    or len(record['permutation']) != 4
                    or any(type(v) is not int for v in record['permutation'])
                    or sorted(record['permutation']) != [0, 1, 2, 3]):
                return False
    edges = {}
    for i, crossing in enumerate(pd):
        check()
        for j, label in enumerate(crossing):
            edges.setdefault(label, []).append((i, j))
    mates = {}
    for x, y in edges.values():
        check()
        mates[x], mates[y] = y, x
    cells = _local_geometry('pulling' if len(rows) == 20*len(pd) else 'centred')
    width = len(cells)
    interior, exterior, sides, boundary = {}, {}, {}, set()
    for t, cell in enumerate(cells):
        for f in range(4):
            key = tuple(sorted(point for v, point in enumerate(cell) if v != f))
            zero = [v for v in range(4) if all(point[v] == 0 for point in key)]
            if zero:
                side, = zero
                sides[t, f] = side
                exterior[key] = t, f
            elif any(all(point[v] == 8 for point in key) for v in (2, 3)):
                boundary.add((t, f))
            else:
                interior.setdefault(key, []).append((t, f))

    for c in range(4 * len(pd)):
        check()
        crossing, corner = divmod(c, 4)
        neighbours = [None] * 4
        for f in (0, 1):
            shift = 1 if corner % 2 == f else -1
            neighbours[f] = 4*crossing + (corner+shift) % 4
        d, k = mates[crossing, (corner+1) % 4]
        neighbours[2] = 4*d+k
        d, k = mates[crossing, corner]
        neighbours[3] = 4*d+(k-1) % 4
        for t, cell in enumerate(cells):
            for f in range(4):
                record = rows[width*c+t][f]
                if (t, f) in boundary:
                    if record is not None:
                        return False
                    continue
                if record is None:
                    return False
                points = [point for v, point in enumerate(cell) if v != f]
                if (t, f) not in sides:
                    key = tuple(sorted(points))
                    (u, g), = (entry for entry in interior[key] if entry != (t, f))
                    target = c
                else:
                    # All three face points have one zero coordinate: this
                    # determines which original tetrahedral face is crossed.
                    side = sides[t, f]
                    target = neighbours[side]
                    points = [(p[0], p[1], p[3], p[2]) for p in points]
                    u, g = exterior[tuple(sorted(points))]
                permutation = [g] * 4
                for v, point in zip((v for v in range(4) if v != f), points):
                    permutation[v] = cells[u].index(point)
                if (record['tetrahedron'] != width*target+u
                        or record['permutation'] != permutation):
                    return False
    check()
    return True
