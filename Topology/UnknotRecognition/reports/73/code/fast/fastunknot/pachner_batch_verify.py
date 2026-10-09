"""Independent boundary-port and coarea replay for simultaneous 3--2 moves.

This checker imports no Pachner producer, candidate selector, cochain
transport producer, or local normal-coordinate constructor.  Each region
is verified as a formal ball, and all external gluings are compared using
stable tagged ports.  Shared faces and ambient vertex identifications are
therefore retained, not assumed absent.
"""
from itertools import combinations

from .integer_codec import encoded_integer
from .normal_surface_geometry import _prepare, _coordinates, _edge, _EDGES, NormalOrbitError
from .cocycle_transport_verify import _shield_callback, _read_heights, _check_signed_edges


def _read_regions(value, count, check):
    if type(value) is not list:
        return None
    regions, used, last = [], set(), -1
    expected = {frozenset((0, 1, 3, 4)), frozenset((1, 2, 3, 4)),
                frozenset((0, 2, 3, 4))}
    for entries in value:
        check()
        if type(entries) is not list or len(entries) != 3:
            return None
        region, previous = {}, -1
        for item in entries:
            if type(item) is not dict or set(item) != {'tetrahedron', 'vertices'}:
                return None
            t, row = item['tetrahedron'], item['vertices']
            if (type(t) is not int or not previous < t < count or t in used
                    or type(row) is not list or len(row) != 4
                    or any(type(v) is not int or not 0 <= v < 5 for v in row)
                    or len(set(row)) != 4):
                return None
            region[t], previous = row, t
            used.add(t)
        if ({frozenset(row) for row in region.values()} != expected
                or min(region) <= last):
            return None
        last = min(region)
        regions.append(region)
    return regions, used


def _ports(rows, regions, outside, check):
    """Check each formal internal face, then tag every remaining face."""
    addresses, vertex_labels = {}, {}
    for t, original in outside.items():
        check()
        for f in range(4):
            addresses[t, f] = ('outside', original, f)
            vertex_labels[t, f] = tuple(range(4))
    for i, region in enumerate(regions):
        occurrences = {}
        for t, labels in region.items():
            for f in range(4):
                key = tuple(sorted(labels[v] for v in range(4) if v != f))
                occurrences.setdefault(key, []).append((t, f))
        boundary = 0
        for key, places in occurrences.items():
            check()
            if len(places) == 2:
                (t, f), (u, g) = places
                record = rows[t][f]
                if (record is None or record['tetrahedron'] != u
                        or record['permutation'][f] != g
                        or any(region[t][v] != region[u][record['permutation'][v]]
                               for v in range(4) if v != f)):
                    return None
            elif len(places) == 1:
                boundary += 1
                t, f = places[0]
                addresses[t, f] = ('region', i, key)
                vertex_labels[t, f] = region[t]
            else:
                return None
        if boundary != 6:
            return None
    signatures = {}
    for (t, f), key in addresses.items():
        check()
        record = rows[t][f]
        if record is None:
            signatures[key] = ('boundary',)
            continue
        u, p = record['tetrahedron'], record['permutation']
        target = (u, p[f])
        if target not in addresses:
            return None
        labels, other = vertex_labels[t, f], vertex_labels[target]
        mapping = tuple(sorted((labels[v], other[p[v]]) for v in range(4) if v != f))
        signatures[key] = (addresses[target], mapping)
    return signatures


def _coherent_data(old, new, regions, survivors, source, evidence, check):
    fields = {'bipyramid_heights', 'heights', 'coordinates',
              'euler_jump', 'normal_disc_jump'}
    if type(evidence) is not dict or set(evidence) != fields:
        return False
    h = _read_heights(source, len(old['tetrahedra']), check)
    k = _read_heights(evidence['heights'], len(new['tetrahedra']), check)
    fives = evidence['bipyramid_heights']
    if (h is None or k is None or type(fives) is not list
            or len(fives) != len(regions) or not _check_signed_edges(old, h, check)):
        return False
    try:
        euler = encoded_integer(evidence['euler_jump'])
        pieces = encoded_integer(evidence['normal_disc_jump'])
    except ValueError:
        return False
    for i, region in enumerate(regions):
        check()
        five = fives[i]
        if type(five) is not list or len(five) != 5:
            return False
        try:
            five = [encoded_integer(x) for x in five]
        except ValueError:
            return False
        if five[0] != 0:
            return False
        for t, labels in region.items():
            for a, b in combinations(range(4), 2):
                if h[t][b] - h[t][a] != five[labels[b]] - five[labels[a]]:
                    return False
        start = len(survivors) + 2 * i
        for j, labels in enumerate(((0, 1, 2, 3), (0, 1, 2, 4))):
            if k[start + j] != [five[v] - five[labels[0]] for v in labels]:
                return False
    for j, t in enumerate(survivors):
        check()
        if k[j] != [x - h[t][0] for x in h[t]]:
            return False
    if not _check_signed_edges(new, k, check):
        return False
    try:
        analysed = _coordinates(new, evidence['coordinates'], check)
    except NormalOrbitError:
        return False
    for t, row in enumerate(k):
        check()
        for j, (a, b) in enumerate(_EDGES):
            root = new['edge_roots'][6 * t + j]
            if analysed['weights'][root] != abs(row[b] - row[a]):
                return False
    weights = {}
    old_pieces = 0
    for t, row in enumerate(h):
        check()
        old_pieces += max(row) - min(row)
        for j, (a, b) in enumerate(_EDGES):
            weights[old['edge_roots'][6 * t + j]] = abs(row[b] - row[a])
    old_arcs = 0
    faces = old['boundary_faces'] + [(t, f) for t, f, u, g, p in old['pairs']]
    for t, f in faces:
        check()
        values = [h[t][v] for v in range(4) if v != f]
        old_arcs += max(values) - min(values)
    old_euler = sum(weights.values()) - old_arcs + old_pieces
    check()
    return (analysed['euler_characteristic'] - old_euler == euler
            and analysed['normal_disks'] - old_pieces == pieces)


@_shield_callback
def verify_pachner_32_batch(before, after, certificate, heights=None, *,
                            check=lambda: None):
    """Replay a canonical simultaneous replacement without its producer."""
    check()
    expected = {'schema', 'regions'} | ({'cocycle'} if heights is not None else set())
    if (type(certificate) is not dict or set(certificate) != expected
            or certificate['schema'] != 'pachner-32-batch-v1'):
        return False
    try:
        old = _prepare(before, check)
        new = _prepare(after, check)
    except NormalOrbitError:
        return False
    parsed = _read_regions(certificate['regions'], len(old['tetrahedra']), check)
    if parsed is None:
        return False
    regions, removed = parsed
    if len(new['tetrahedra']) != len(old['tetrahedra']) - len(regions):
        return False
    counts = {}
    for root in old['edge_roots']:
        check()
        counts[root] = counts.get(root, 0) + 1
    centres = set()
    for region in regions:
        check()
        roots = {old['edge_roots'][_edge(t, labels.index(3), labels.index(4))]
                 for t, labels in region.items()}
        if len(roots) != 1:
            return False
        root = next(iter(roots))
        if counts[root] != 3 or root in centres:
            return False
        centres.add(root)
    survivors = [t for t in range(len(old['tetrahedra'])) if t not in removed]
    replacement = [{len(survivors) + 2 * i: (0, 1, 2, 3),
                    len(survivors) + 2 * i + 1: (0, 1, 2, 4)}
                   for i in range(len(regions))]
    source_ports = _ports(old['tetrahedra'], regions, {t: t for t in survivors}, check)
    target_ports = _ports(new['tetrahedra'], replacement,
                          {i: t for i, t in enumerate(survivors)}, check)
    if source_ports is None or target_ports is None or source_ports != target_ports:
        return False
    if heights is None:
        return True
    return _coherent_data(old, new, regions, survivors, heights,
                          certificate['cocycle'], check)
