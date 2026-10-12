"""Independent source reconstruction for labelled normal chamber graphs.

No chamber-graph exporter, complement producer, graph decoder or orbit search
is imported.  Representative sides come from the independent raw cut-cell
reference; chamber pairings come from the independent face-region reference.
The established finite source validator and normal arc system are shared.
"""

from .integer_codec import certificate_equal, encoded_integer
from .interval_orbit_verify import verify_orbit_certificate
from .normal_cut_cells_verify import _reference_cells
from .normal_cut_complement_verify import _reference_chambers
from .normal_surface_geometry import _arc_system, _coordinates, _edge, _fingerprint, _prepare
from .weighted_orbit_verify import verify_weighted_orbit_certificate


def _decode_representatives(rows, records, check):
    if type(records) is not list:
        return None
    decoded = []
    for record in records:
        check()
        if type(record) is not dict or set(record) != {'tetrahedron', 'column', 'rank'}:
            return None
        try:
            t, c, r = (encoded_integer(record[key]) for key in ('tetrahedron', 'column', 'rank'))
        except ValueError:
            return None
        if not (0 <= t < len(rows) and 0 <= c < 7 and 0 <= r < rows[t][c]):
            return None
        decoded.append((t, c, r))
    return decoded


def _source_markers(prepared, analysed, representatives, check):
    cells = _reference_cells(prepared, analysed, check)
    families = {(f['tetrahedron'], f['column'], f['side']): f
                for f in cells['faces'] if f['kind'] == 'horizontal'}
    carriers = {}
    for item in cells['face_incidence']:
        check()
        if item['kind'] == 'horizontal':
            key = item['tetrahedron'], item['column'], item['side']
            carriers.setdefault(key, []).append(item)
    offsets, size = {}, 0
    for edge in sorted(analysed['weights']):
        check()
        offsets[edge] = size
        size += analysed['weights'][edge]
    result = []
    for label, (t, c, r) in enumerate(representatives):
        check()
        family = families[t, c, 0]
        # Select the same source edge as the public marker convention, then
        # derive its point through a genuine independently oriented face arc.
        anchor = c if c < 4 else 0
        other = min(v for v in range(4) if v != anchor and
                    (c < 4 or v != c - 3))
        arc = next(a for a in family['cycle'] if a['kind'] == 'normal_arc'
                   and a['corner'] == anchor and a['face'] != other)
        local_rank = arc['rank'][0] * r + arc['rank'][1]
        local = _edge(t, anchor, other)
        edge = prepared['edge_roots'][local]
        reverse = bool(prepared['edge_orientations'][local]) != (anchor > other)
        vertex = offsets[edge] + (analysed['weights'][edge] - 1 - local_rank
                                  if reverse else local_rank)
        sides = []
        for side in (0, 1):
            point = families[t, c, side]['start'] + r
            candidates = [a for a in carriers[t, c, side]
                          if a['face_start'] <= point < a['face_stop']]
            if len(candidates) != 1:
                raise ArithmeticError('the reference normal face has no unique chamber')
            slope, offset = candidates[0]['chamber']
            sides.append(slope * point + offset)
        result.append(dict(label=label, surface_point=vertex,
                           negative_chamber=sides[0], positive_chamber=sides[1]))
    return size, cells['chamber_points'], result


def _expected_graph(histogram, components, check):
    values = []
    for entry in histogram:
        check()
        try:
            value = encoded_integer(entry['weight'][0])
            multiplicity = encoded_integer(entry['orbits'])
        except (ValueError, KeyError, IndexError, TypeError):
            return None
        if value <= 0 or multiplicity != 1 or value >= 1 << (2 * components):
            return None
        values.append(value)
    values.sort(key=lambda x: (x & -x).bit_length())
    owners = []
    for side in range(2 * components):
        check()
        where = [v for v, value in enumerate(values) if value & (1 << side)]
        if len(where) != 1:
            return None
        owners.append(where[0])
    edges = [[owners[2 * i], owners[2 * i + 1]] for i in range(components)]
    if not values:
        return None
    neighbours = {v: [] for v in range(len(values))}
    for a, b in edges:
        check()
        neighbours[a].append(b)
        neighbours[b].append(a)
    found, pending = {0}, [0]
    for vertex in pending:
        check()
        for other in neighbours[vertex]:
            if other not in found:
                found.add(other)
                pending.append(other)
    if len(found) != len(values):
        return None
    return dict(vertices=len(values), edges=edges, chamber_masks=values,
                cycle_rank=components - len(values) + 1)


def verify_normal_chamber_graph(triangulation, coordinates, certificate, *,
                                max_operations=None, check=lambda: None):
    """Verify source-bound component labels, coorientability and every edge.

    The operation limit bounds the combined number of recorded orbit events,
    rather than elapsed time.  A limit or malformed certificate returns False.
    Source errors and cancellation callbacks propagate as in native verifiers.
    Successful replay proves the chamber graph; it does not authenticate a
    subsequent edit, support footprint or geometric dual-loop description.
    """
    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('max_operations must be a nonnegative integer or None')
    fields = {'schema', 'input_sha256', 'representatives', 'markers', 'graph', 'proofs'}
    if type(certificate) is not dict or set(certificate) != fields:
        return False
    if certificate['schema'] != 'normal-chamber-graph-v1':
        return False
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    if certificate['input_sha256'] != _fingerprint(triangulation, analysed, check):
        return False
    reps = _decode_representatives(analysed['rows'], certificate['representatives'], check)
    if reps is None:
        return False
    proofs = certificate['proofs']
    if analysed['normal_disks'] == 0:
        expected = dict(vertices=1, edges=[], chamber_masks=[0], cycle_rank=0)
        return (reps == [] and certificate_equal(certificate['markers'], [])
                and proofs == {} and certificate_equal(certificate['graph'], expected))
    components = len(reps)
    if not components or type(proofs) is not dict or set(proofs) != {
            'surface_labels', 'orientation_double', 'chamber_sides'}:
        return False
    traces = []
    for key in ('surface_labels', 'orientation_double', 'chamber_sides'):
        check()
        proof = proofs[key]
        if type(proof) is not dict:
            return False
        trace = proof if key == 'orientation_double' else proof.get('orbit_proof')
        if type(trace) is not dict or type(trace.get('operations')) is not list:
            return False
        traces.append(trace)
    if max_operations is not None and sum(len(t['operations']) for t in traces) > max_operations:
        return False
    points, chamber_points, marks = _source_markers(prepared, analysed, reps, check)
    if not certificate_equal(certificate['markers'], marks):
        return False
    size, pairs = _arc_system(prepared, analysed, check=check)
    if size != points:
        return False
    weights = [(m['surface_point'], m['surface_point'] + 1, [1 << i])
               for i, m in enumerate(marks)]
    labelled = proofs['surface_labels']
    if not verify_weighted_orbit_certificate(size, pairs, weights, labelled,
                                             dimension=1, check=check):
        return False
    expected = [dict(weight=[1 << i], orbits=1) for i in range(components)]
    if not certificate_equal(labelled['histogram'], expected):
        return False
    size, pairs = _arc_system(prepared, analysed, scale=2, check=check)
    doubled = proofs['orientation_double']
    if not verify_orbit_certificate(size, pairs, doubled, check=check):
        return False
    try:
        double_components = encoded_integer(doubled['orbit_count'])
    except (ValueError, KeyError):
        return False
    if double_components != 2 * components:
        return False
    size, pairs = _reference_chambers(prepared, analysed['rows'], check)
    if size != chamber_points:
        return False
    weights = []
    for i, m in enumerate(marks):
        check()
        for bit, key in ((2 * i, 'negative_chamber'), (2 * i + 1, 'positive_chamber')):
            point = m[key]
            weights.append((point, point + 1, [1 << bit]))
    sides = proofs['chamber_sides']
    if not verify_weighted_orbit_certificate(size, pairs, weights, sides,
                                             dimension=1, check=check):
        return False
    graph = _expected_graph(sides['histogram'], components, check)
    check()
    return graph is not None and certificate_equal(certificate['graph'], graph)
