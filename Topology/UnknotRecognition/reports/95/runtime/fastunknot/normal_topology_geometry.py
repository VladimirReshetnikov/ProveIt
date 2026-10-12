"""Two additive weights for a normal surface's component topology.

Shared trusted geometry only: validation, normal arc conventions, cell
ownership and the inclusion of boundary edge points in full edge points.
All intervals are half open; no normal point or disk is expanded.
"""

from .normal_surface_geometry import _arc_system
from .normal_component_geometry import disk_corner_intervals, _edge_offsets


def embed_boundary_intervals(prepared, analysed, intervals, check=lambda: None):
    """Embed a sorted boundary-universe interval union in the full universe."""
    offsets, _ = _edge_offsets(analysed, check)
    blocks, endpoint = [], 0
    for edge in sorted(prepared['boundary_incidence']):
        check()
        length = analysed['weights'][edge]
        if length:
            blocks.append((endpoint, endpoint + length, offsets[edge]))
        endpoint += length
    result, cursor = [], 0
    previous = 0
    for lo, hi in intervals:
        check()
        if (type(lo) is not int or type(hi) is not int
                or not 0 <= lo < hi <= endpoint or lo < previous):
            raise ValueError('boundary marks must be a sorted disjoint interval union')
        previous = hi
        while cursor < len(blocks) and blocks[cursor][1] <= lo:
            check()
            cursor += 1
        index = cursor
        while index < len(blocks) and blocks[index][0] < hi:
            check()
            start, stop, image = blocks[index]
            left, right = max(lo, start), min(hi, stop)
            if left < right:
                left, right = image + left - start, image + right - start
                if result and result[-1][1] == left:
                    result[-1] = (result[-1][0], right)
                else:
                    result.append((left, right))
            index += 1
    return result


def topology_weight_system(prepared, analysed, boundary_marks, *, scale=1,
                           check=lambda: None):
    """Weights (Euler characteristic, boundary-circle markers), dimension two.

    At scale two every old point has adjacent lifts 2j and 2j+1. Lifting
    a mark selects one point on each of the two lifts of its boundary circle.
    Euler cell ownership lifts in the same way.
    """
    if type(scale) is not int or scale not in (1, 2):
        raise ValueError('only the original surface and its double are used')
    size, pairings = _arc_system(prepared, analysed, check=check)
    offsets, total = _edge_offsets(analysed, check)
    if size != total:
        raise ArithmeticError('full edge universes disagree')
    weights = []

    def add(lo, hi, value):
        if lo < hi:
            weights.append((scale * lo, scale * hi, value))

    add(0, size, (1, 0))
    for pairing in pairings:
        check()
        add(pairing.a, pairing.b + 1, (-1, 0))
    for _, lo, hi in disk_corner_intervals(prepared, analysed, offsets, check):
        check()
        add(lo, hi, (1, 0))
    embedded = embed_boundary_intervals(prepared, analysed, boundary_marks, check)
    for lo, hi in embedded:
        check()
        add(lo, hi, (0, 1))
    if scale == 2:
        size, pairings = _arc_system(prepared, analysed, scale=2, check=check)
    return dict(size=size, pairings=pairings, weights=weights, dimension=2,
                boundary_marker_intervals=len(embedded))


def vertex_link_totals(prepared, links, check=lambda: None):
    """Classify the already validated manifold vertices as boundary/interior."""
    boundary = set()
    for tetrahedron, face in prepared['boundary_faces']:
        check()
        boundary.update(prepared['vertex_roots'][4 * tetrahedron + vertex]
                        for vertex in range(4) if vertex != face)
    disks = spheres = 0
    for record in links:
        check()
        if record['vertex'] in boundary:
            disks += record['multiplicity']
        else:
            spheres += record['multiplicity']
    return disks, spheres


def spectrum_summary(rows, check=lambda: None):
    """Totals derived from a canonical list of connected topological types."""
    total = orientable = nonorientable = boundary = euler = 0
    for row in rows:
        check()
        count = row['multiplicity']
        total += count
        if row['orientable']:
            orientable += count
        else:
            nonorientable += count
        boundary += count * row['boundary_components']
        euler += count * row['chi']
    return dict(components=total, orientable_components=orientable,
                nonorientable_components=nonorientable,
                boundary_components=boundary, euler_characteristic=euler,
                topology_spectrum=rows)
