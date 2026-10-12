"""Independent source reconstruction and replay for cyclic port certificates."""

from .integer_codec import encoded_integer, certificate_equal
from .interval_orbits import IntervalPairing
from .normal_surface_geometry import _prepare, _coordinates
from .normal_parallelity_reference import _reference_parallelity
from .normal_parallelity_verify import (
    verify_normal_cut_parallelity, _reference_queries, _reference_summary,
)
from .weighted_orbit_verify import verify_weighted_orbit_certificate


def _proof_length(certificate):
    if type(certificate) is not dict:
        return None
    proof = certificate.get('orbit_proof')
    if type(proof) is not dict or type(proof.get('operations')) is not list:
        return None
    return len(proof['operations'])


def _independent_queries(geometry, check):
    vertices, _, _, _, _, fibres, _ = _reference_queries(geometry, check)
    paths = vertices.copy()
    path_weights, fibre_weights = [], []
    polygons = geometry['polygons']
    size = geometry['polygon_points']
    for edge in geometry['free_edges']:
        check()
        polygon = polygons[edge['polygon']]
        corners = polygon['corner_starts']
        first, last = edge['rank_start'], edge['rank_stop'] - 1
        start = corners[edge['edge']]
        end = corners[(edge['edge'] + 1) % len(corners)]
        if edge['original_boundary']:
            paths.append(IntervalPairing(start + first - 1, start + last - 1,
                                         end + first - 1, end + last - 1))
            path_weights.append((start + first - 1, start + last, [0, 1]))
        else:
            port = edge['port']
            for label, point in ((2 * port, start + first - 1),
                                 (2 * port + 1, end + first - 1)):
                path_weights.append((point, point + 1, [2 ** label, 0]))
            point = polygon['start'] + first - 1
            fibre_weights.append((point, point + 1, [2 ** (2 * port)]))
            fibre_weights.append((point + size, point + size + 1,
                                  [2 ** (2 * port + 1)]))
    return paths, path_weights, fibres, fibre_weights


def _independent_words(certificate, number, check):
    neighbours = [None] * (2 * number)
    distances = [None] * (2 * number)
    for record in certificate['histogram']:
        check()
        mask, distance = map(encoded_integer, record['weight'])
        if mask == 0:
            continue
        if mask < 0 or mask.bit_length() > 2 * number or distance < 0:
            return None
        labels = [i for i in range(2 * number) if (mask >> i) & 1]
        if len(labels) != 2 or encoded_integer(record['orbits']) != 1:
            return None
        a, b = labels
        if neighbours[a] is not None or neighbours[b] is not None:
            return None
        neighbours[a], neighbours[b] = b, a
        distances[a] = distances[b] = distance
    if any(value is None for value in neighbours):
        return None
    used, result = set(), []
    for port in range(number):
        if port in used:
            continue
        walk, point = [], 2 * port
        while point // 2 not in used:
            check()
            used.add(point // 2)
            other = point + 1 if point % 2 == 0 else point - 1
            walk.append(dict(port=point // 2, entry_endpoint=point % 2,
                             original_edges_after=distances[other]))
            point = neighbours[other]
        if point != 2 * port:
            return None
        result.append(walk)
    return result


def _independent_gauges(certificate, profiles, number, check):
    blocks, owner = [], {}
    for record in certificate['histogram']:
        check()
        mask = encoded_integer(record['weight'][0])
        if mask == 0:
            continue
        if (mask < 0 or mask.bit_length() > 2 * number
                or encoded_integer(record['orbits']) != 1):
            return None
        block = {i for i in range(2 * number) if (mask >> i) & 1}
        if block & owner.keys():
            return None
        for token in block:
            owner[token] = len(blocks)
        blocks.append(block)
    if set(owner) != set(range(2 * number)):
        return None
    result = []
    for profile in profiles:
        check()
        ports = profile['core_ports']
        if not ports:
            continue
        anchor = min(ports)
        left, right = blocks[owner[2 * anchor]], blocks[owner[2 * anchor + 1]]
        tokens = {2 * port + sheet for port in ports for sheet in (0, 1)}
        if profile['product']:
            if left & right or left | right != tokens:
                return None
            gauges = []
            for port in ports:
                candidates = [sheet for sheet in (0, 1) if 2 * port + sheet in left]
                if len(candidates) != 1:
                    return None
                gauges.append([port, candidates[0]])
        else:
            if left != tokens or right != tokens:
                return None
            gauges = None
        result.append(dict(core_ports=ports, product=profile['product'],
                           anchor_port=anchor, gauges=gauges))
    return result


def _independent_templates(words, gauges, profiles, check):
    orientation = {port: bit for group in gauges if group['product']
                   for port, bit in group['gauges']}
    result = []
    for profile in profiles:
        check()
        ports = profile['core_ports']
        if (not ports or not profile['product'] or profile['genus'] != 0
                or profile['boundary_components'] != 1):
            continue
        selected = [word for word in words if any(r['port'] in ports for r in word)]
        if len(selected) != 1 or sorted(r['port'] for r in selected[0]) != sorted(ports):
            return None
        labels = []
        for record in selected[0]:
            labels.append(dict(kind='core_port', port=record['port'],
                               entry_endpoint=record['entry_endpoint'],
                               fibre_flip=orientation[record['port']]))
            if record['original_edges_after'] > 0:
                labels.append(dict(kind='original_boundary',
                                   source_edge_count=record['original_edges_after']))
        sides = []
        for index, label in enumerate(labels):
            subdivisions = 4 - len(labels) if index == 0 and len(labels) < 3 else 1
            for piece in range(subdivisions):
                sides.append(dict(label, parameter=[piece, piece + 1, subdivisions]))
        count = len(sides)
        triangles = [[count, index, (index + 1) % count] for index in range(count)]
        tetrahedra = []
        for index in range(count):
            a, b = sorted([index, (index + 1) % count])
            # The fan centre count has the largest base vertex label.
            tetrahedra.append([a, b, count, 2 * count + 1])
            tetrahedra.append([a, b, b + count + 1, 2 * count + 1])
            tetrahedra.append([a, a + count + 1, b + count + 1, 2 * count + 1])
        pattern = []
        for index, side in enumerate(sides):
            if side['kind'] == 'original_boundary':
                pattern.append([index, (index + 1) % count])
                pattern.append([index + count + 1, (index + 1) % count + count + 1])
        result.append(dict(core_ports=ports, boundary_sides=sides,
                           base_triangles=triangles, product_tetrahedra=tetrahedra,
                           first_cut_pattern_edges=pattern))
    return result


def verify_parallelity_port_words(triangulation, coordinates, certificate, *,
                                  max_operations=None, check=lambda: None):
    """Replay all six source-bound queries and independently reconstruct outputs.

    Malformed/altered certificates return False.  Cancellation exceptions from
    check propagate.  The operation cap covers all supplied orbit-proof traces;
    it is not a bit-operation or elapsed-time budget.
    """
    check()
    if max_operations is not None and (type(max_operations) is not int
                                       or max_operations < 0):
        raise ValueError('max_operations must be nonnegative or None')
    fields = {'schema', 'source', 'port_paths', 'port_fibres', 'boundary_words',
              'fibre_gauges', 'disc_templates'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] != 'parallelity-port-words-v1'):
        return False
    source = certificate['source']
    if type(source) is not dict:
        return False
    lengths = []
    for field in ('vertex_selector', 'boundary_selector', 'polygon_weights', 'fibre_cover'):
        part = source.get(field)
        if type(part) is not dict:
            return False
        if field.endswith('selector'):
            part = part.get('weighted_certificate')
        length = _proof_length(part)
        if length is None:
            return False
        lengths.append(length)
    for field in ('port_paths', 'port_fibres'):
        length = _proof_length(certificate[field])
        if length is None:
            return False
        lengths.append(length)
    if max_operations is not None and sum(lengths) > max_operations:
        return False
    if not verify_normal_cut_parallelity(triangulation, coordinates, source, check=check):
        return False
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    geometry = _reference_parallelity(prepared, analysed, check)
    summary = _reference_summary(
        geometry, source['vertex_selector'], source['boundary_selector'],
        source['polygon_weights'], source['fibre_cover'],
        analysed['euler_characteristic'], check)
    paths, endpoint_weights, cover, fibre_weights = _independent_queries(geometry, check)
    if not verify_weighted_orbit_certificate(
            geometry['corner_points'], paths, endpoint_weights,
            certificate['port_paths'], dimension=2, check=check):
        return False
    if not verify_weighted_orbit_certificate(
            2 * geometry['polygon_points'], cover, fibre_weights,
            certificate['port_fibres'], dimension=1, check=check):
        return False
    number = len(geometry['ports'])
    profiles = summary['base_profiles']
    words = _independent_words(certificate['port_paths'], number, check)
    if words is None or not certificate_equal(certificate['boundary_words'], words):
        return False
    gauges = _independent_gauges(certificate['port_fibres'], profiles, number, check)
    if gauges is None or not certificate_equal(certificate['fibre_gauges'], gauges):
        return False
    templates = _independent_templates(words, gauges, profiles, check)
    return templates is not None and certificate_equal(certificate['disc_templates'], templates)
