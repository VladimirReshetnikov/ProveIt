"""Cyclic attachment charts for compressed source parallelity bundles.

The input surface and bundle geometry are constructed by normal_cut_parallelity.
Two further interval-orbit queries recover boundary order, empty versus nonempty
boundary gaps, and relative fibre orientations.  Disc products are replaced by
small combinatorial product triangulations, preserving their attachment charts.
This is a supplied-surface operation, not an admissible hierarchy or knot test.
"""

from .interval_orbits import IntervalPairing
from .normal_parallelity import normal_cut_parallelity, _systems
from .weighted_orbits import weighted_orbit_histogram


def _port_queries(geometry, check):
    vertex, _, _, _, _, cover, _ = _systems(geometry, check)
    paths = list(vertex)
    endpoints, fibres = [], []
    polygons = geometry['polygons']
    size = geometry['polygon_points']
    seen = set()
    for edge in geometry['free_edges']:
        check()
        polygon = polygons[edge['polygon']]
        first, stop = edge['rank_start'], edge['rank_stop']
        degree = len(polygon['edges'])
        left = polygon['corner_starts'][edge['edge']] + first - 1
        right = polygon['corner_starts'][(edge['edge'] + 1) % degree] + first - 1
        if edge['original_boundary']:
            paths.append(IntervalPairing(left, left + stop - first - 1,
                                         right, right + stop - first - 1))
            # One mark per free edge, not per endpoint.  Zero counts matter:
            # they distinguish adjacent ports from separated attachments.
            endpoints.append((left, left + stop - first, [0, 1]))
        else:
            port = edge['port']
            if stop != first + 1 or port in seen:
                raise ArithmeticError('a core port must be a unique singleton')
            seen.add(port)
            for end, point in enumerate((left, right)):
                endpoints.append((point, point + 1, [1 << (2 * port + end), 0]))
            point = polygon['start'] + first - 1
            for sheet in (0, 1):
                fibres.append((point + sheet * size, point + sheet * size + 1,
                               [1 << (2 * port + sheet)]))
    if seen != set(range(len(geometry['ports']))):
        raise ArithmeticError('the source port list is incomplete')
    return paths, endpoints, cover, fibres


def _boundary_words(histogram, number, check):
    matching, lengths = {}, {}
    for row in histogram:
        check()
        mask, length = row['weight']
        if not mask:
            continue
        if (mask < 0 or mask.bit_length() > 2 * number or mask.bit_count() != 2
                or row['orbits'] != 1 or length < 0):
            raise ArithmeticError('punctured boundary has an invalid endpoint profile')
        first = (mask & -mask).bit_length() - 1
        second = (mask ^ (1 << first)).bit_length() - 1
        if first in matching or second in matching:
            raise ArithmeticError('a boundary endpoint occurs in several paths')
        matching[first], matching[second] = second, first
        lengths[first] = lengths[second] = length
    if set(matching) != set(range(2 * number)):
        raise ArithmeticError('some boundary endpoints are missing')
    words, unseen = [], set(range(number))
    while unseen:
        first = 2 * min(unseen)
        endpoint, word = first, []
        while True:
            check()
            port, end = divmod(endpoint, 2)
            if port not in unseen:
                raise ArithmeticError('the port boundary walk repeats a port')
            unseen.remove(port)
            word.append(dict(port=port, entry_endpoint=end,
                             original_edges_after=lengths[endpoint ^ 1]))
            endpoint = matching[endpoint ^ 1]
            if endpoint == first:
                break
        words.append(word)
    return words


def _fibre_gauges(histogram, profiles, number, check):
    masks = {}
    for row in histogram:
        check()
        mask = row['weight'][0]
        if not mask:
            continue
        if mask < 0 or mask.bit_length() > 2 * number or row['orbits'] != 1:
            raise ArithmeticError('invalid marked fibre-cover component')
        for token in range(2 * number):
            if mask & (1 << token):
                if token in masks:
                    raise ArithmeticError('a fibre mark occurs in several components')
                masks[token] = mask
    if set(masks) != set(range(2 * number)):
        raise ArithmeticError('some fibre marks are missing')
    output = []
    for profile in profiles:
        check()
        ports = profile['core_ports']
        if not ports:
            continue
        anchor = min(ports)
        whole = sum(3 << (2 * port) for port in ports)
        zero, one = masks[2 * anchor], masks[2 * anchor + 1]
        if profile['product']:
            if zero & one or zero | one != whole:
                raise ArithmeticError('product fibre cover has invalid sheet blocks')
            gauges = []
            for port in ports:
                bits = (zero >> (2 * port)) & 3
                if bits not in (1, 2):
                    raise ArithmeticError('product chart has no unique fibre gauge')
                gauges.append([port, bits - 1])
        else:
            if zero != whole or one != whole:
                raise ArithmeticError('twisted fibre cover is not connected')
            gauges = None
        output.append(dict(core_ports=ports, product=profile['product'],
                           anchor_port=anchor, gauges=gauges))
    return output


def _disc_templates(words, gauges, profiles, check):
    """Produce a PL disc-times-interval model with exact port chart labels.

    Original-boundary runs are coalesced.  Their source subdivisions are not
    retained as marked data.  Product triangulation uses a global vertex order,
    so adjacent triangular prisms have consistent triangulated square faces.
    """
    gauge_by_port = {}
    for component in gauges:
        if component['product']:
            gauge_by_port.update(component['gauges'])
    output = []
    for profile in profiles:
        check()
        ports = profile['core_ports']
        if not ports or not profile['product'] or profile['genus'] != 0:
            continue
        if profile['boundary_components'] != 1:
            continue
        relevant = [word for word in words if word[0]['port'] in ports]
        if len(relevant) != 1 or {r['port'] for r in relevant[0]} != set(ports):
            raise ArithmeticError('a disc product has more than one marked boundary')
        sides = []
        for record in relevant[0]:
            sides.append(dict(kind='core_port', port=record['port'],
                              entry_endpoint=record['entry_endpoint'],
                              fibre_flip=gauge_by_port[record['port']]))
            if record['original_edges_after']:
                sides.append(dict(kind='original_boundary',
                                  source_edge_count=record['original_edges_after']))
        # At least three boundary vertices are needed for a simplicial disc.
        # Splitting a labelled side preserves its original parameter chart.
        pieces = max(1, 4 - len(sides))
        first, rest = sides[0], sides[1:]
        sides = [dict(first, parameter=[i, i + 1, pieces]) for i in range(pieces)]
        sides.extend(dict(side, parameter=[0, 1, 1]) for side in rest)
        boundary = len(sides)
        triangles = [[boundary, i, (i + 1) % boundary] for i in range(boundary)]
        vertices = boundary + 1
        tetrahedra = []
        for triangle in triangles:
            a, b, c = sorted(triangle)
            tetrahedra.extend([[a, b, c, c + vertices],
                               [a, b, b + vertices, c + vertices],
                               [a, a + vertices, b + vertices, c + vertices]])
        pattern_edges = [[i + sheet * vertices,
                          (i + 1) % boundary + sheet * vertices]
                         for i, side in enumerate(sides)
                         if side['kind'] == 'original_boundary' for sheet in (0, 1)]
        output.append(dict(core_ports=ports, boundary_sides=sides,
                           base_triangles=triangles, product_tetrahedra=tetrahedra,
                           first_cut_pattern_edges=pattern_edges))
    return output


def normal_parallelity_port_words(triangulation, coordinates, *, max_cycles=None,
                                 record_certificate=False, check=lambda: None):
    """Recover marked boundary circles and small attached disc-product models.

    The cycle cap is shared by all six source and attachment queries.  On
    exhaustion no partial geometry, template or certificate is returned.
    The first-cut pattern consists only of the original-boundary top/bottom
    seams, as appropriate when the input boundary pattern was empty.
    """
    check()
    source = normal_cut_parallelity(triangulation, coordinates, max_cycles=max_cycles,
                                   record_certificate=record_certificate, check=check)
    stats = dict(source=source['stats'])
    result = dict(status='INCONCLUSIVE', stats=stats,
                  trust='source-bound cyclic ports and disc-product templates; '
                        'no admissibility, hierarchy, or knot verdict')
    if source['status'] != 'COMPLETE':
        return result
    spent = sum(row['orbit_cycles'] for row in source['stats'].values())
    remaining = None if max_cycles is None else max_cycles - spent
    geometry = source['geometry']
    paths, endpoint_weights, cover, fibre_weights = _port_queries(geometry, check)
    boundary = weighted_orbit_histogram(
        geometry['corner_points'], paths, endpoint_weights, dimension=2,
        max_cycles=remaining, record_certificate=record_certificate, check=check)
    stats['port_paths'] = boundary['stats']
    if boundary['status'] != 'COMPLETE':
        return result
    if remaining is not None:
        remaining -= boundary['stats']['orbit_cycles']
    fibres = weighted_orbit_histogram(
        2 * geometry['polygon_points'], cover, fibre_weights, dimension=1,
        max_cycles=remaining, record_certificate=record_certificate, check=check)
    stats['port_fibres'] = fibres['stats']
    if fibres['status'] != 'COMPLETE':
        return result
    number = len(geometry['ports'])
    profiles = source['summary']['base_profiles']
    words = _boundary_words(boundary['histogram'], number, check)
    gauges = _fibre_gauges(fibres['histogram'], profiles, number, check)
    templates = _disc_templates(words, gauges, profiles, check)
    result.update(geometry=geometry, summary=source['summary'], boundary_words=words,
                  fibre_gauges=gauges, disc_templates=templates, status='COMPLETE')
    if record_certificate:
        result['certificate'] = dict(schema='parallelity-port-words-v1',
                                     source=source['certificate'],
                                     port_paths=boundary['certificate'],
                                     port_fibres=fibres['certificate'],
                                     boundary_words=words, fibre_gauges=gauges,
                                     disc_templates=templates)
    check()
    return result
