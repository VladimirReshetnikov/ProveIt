"""Independent source reconstruction and replay for native moment interfaces.

This module imports neither native_moments nor a discovery scheduler.  It uses
the maintained raw-cut reference geometry and an independently implemented
permutation traversal after its own moment decoding.
"""

from math import isqrt

from fastunknot.integer_codec import encoded_integer, certificate_equal
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.normal_parallelity_reference import _reference_parallelity
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _fingerprint
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate


class _BadProof(ValueError):
    pass


def _integer(value):
    try:
        return encoded_integer(value)
    except ValueError as error:
        raise _BadProof('invalid exact integer') from error


def _reference_query(geometry, check, codec):
    n = geometry['corner_points']
    terminals = 4 * len(geometry['ports'])
    if codec == 'four':
        width = sum(i * i for i in range(1, terminals + 1)).bit_length()
        base = 2 ** width
        mass = base ** 3
    else:
        base = 2 ** (2 * terminals).bit_length()
        mass = 2 ** (2 * (terminals + base * terminals ** 2)).bit_length()
    packing = dict(codec=codec, base=base, mass=mass)
    pairings, weights = [], []

    def add_maps(maps, start, stop):
        images = [sorted(slope * x + offset for x in (start, stop - 1))
                  for slope, offset in maps]
        pairings.append(IntervalPairing(*images[0], *images[1], maps[0][0] != maps[1][0]))

    for link in geometry['gluings']:
        check()
        for corner in range(2):
            maps = []
            for side in ('left', 'right'):
                polygon = geometry['polygons'][link[side]]
                k = corner if side == 'left' else corner ^ int(link['ends_reverse'])
                index = (link[side + '_edge'] + k) % len(polygon['vertices'])
                slope, offset = link[side + '_map']
                maps.append((slope, offset + polygon['corner_starts'][index] - polygon['start']))
            for sheet in range(2):
                sheets = (sheet, 1 - sheet if link['fibre_flip'] else sheet)
                lifted = [(slope, offset + n * h) for (slope, offset), h in zip(maps, sheets)]
                add_maps(lifted, link['rank_start'], link['rank_stop'])
    for free in geometry['free_edges']:
        check()
        if not free['original_boundary']:
            continue
        polygon = geometry['polygons'][free['polygon']]
        first, stop = free['rank_start'], free['rank_stop']
        local = [polygon['corner_starts'][(free['edge'] + e) % len(polygon['vertices'])] - 1
                 for e in range(2)]
        for sheet in range(2):
            offsets = [point + sheet * n for point in local]
            add_maps([(1, offset) for offset in offsets], first, stop)
            weights.append((offsets[0] + first, offsets[0] + stop, [mass]))
    for port in geometry['ports']:
        check()
        polygon = geometry['polygons'][port['polygon']]
        for corner in range(2):
            offset = polygon['corner_starts'][(port['edge'] + corner) % len(polygon['vertices'])]
            point = offset + port['rank'] - 1
            for sheet in range(2):
                label = 4 * port['id'] + 2 * corner + sheet + 1
                scalar = (sum(coefficient * base ** degree
                              for degree, coefficient in enumerate((1, label, label * label)))
                          if codec == 'four' else label + base * label ** 2)
                weights.append((point + sheet * n, point + sheet * n + 1, [scalar]))
    return pairings, weights, packing


def _reference_output(geometry, proof, packing, check):
    labels = 4 * len(geometry['ports'])
    pairs, length_by_label = {}, {}
    for row in proof['histogram'] if proof is not None else []:
        check()
        value, copies = _integer(row['weight'][0]), _integer(row['orbits'])
        if value < 0 or copies < 1:
            raise _BadProof('invalid moment scalar')
        base = packing['base']
        if packing['codec'] == 'four':
            quotient, count = divmod(value, base)
            quotient, total = divmod(quotient, base)
            length, squares = divmod(quotient, base)
            if count == 0:
                if total != 0 or squares != 0:
                    raise _BadProof('empty terminal class has nonzero moments')
                continue
        else:
            length, tail = divmod(value, packing['mass'])
            if tail == 0:
                continue
            squares, total = divmod(tail, base)
            count = 2  # Certified degree two, not an observed occupancy field.
        if count != 2 or copies != 1 or (total * total - squares) % 2:
            raise _BadProof('invalid endpoint occupancy or product')
        product = (total * total - squares) // 2
        discriminant = total * total - 4 * product
        if discriminant <= 0:
            raise _BadProof('repeated endpoint or negative discriminant')
        difference = isqrt(discriminant)
        if difference ** 2 != discriminant or (total + difference) % 2:
            raise _BadProof('nonintegral endpoint roots')
        ends = [(total - difference) // 2, (total + difference) // 2]
        if not 1 <= ends[0] < ends[1] <= labels:
            raise _BadProof('endpoint root out of range')
        if ends[0] * ends[1] != product:
            raise _BadProof('endpoint roots fail polynomial')
        ends = [value - 1 for value in ends]
        if any(endpoint in pairs for endpoint in ends):
            raise _BadProof('reused endpoint')
        pairs[ends[0]], pairs[ends[1]] = ends[1], ends[0]
        for endpoint in ends:
            length_by_label[endpoint] = length
    if len(pairs) != labels:
        raise _BadProof('missing endpoint')
    matching, gap_indices, gaps = {}, {}, []
    for endpoint in range(labels // 2):
        check()
        lifted = (2 * endpoint, 2 * endpoint + 1)
        images = [pairs[label] for label in lifted]
        if (images[0] // 2 != images[1] // 2 or images[0] % 2 == images[1] % 2
                or length_by_label[lifted[0]] != length_by_label[lifted[1]]):
            raise _BadProof('incompatible interval lifts')
        other = images[0] // 2
        if other == endpoint:
            raise _BadProof('a gap has only one endpoint occurrence')
        matching[endpoint] = other
        if endpoint < other:
            index = len(gaps)
            gap_indices[endpoint] = gap_indices[other] = index
            length = length_by_label[lifted[0]]
            gaps.append(dict(id=index, ends=[endpoint, other],
                             old_boundary_present=bool(length),
                             fibre_flip=bool(images[0] % 2), unmarked_edges=length))
    # Independently traverse the permutation cross-port then cross-gap.
    successor = {endpoint: matching[endpoint ^ 1] for endpoint in range(labels // 2)}
    unused, loops, attachments = set(range(labels // 4)), [], []
    least_unused = 0
    while unused:
        check()
        while least_unused not in unused:
            least_unused += 1
        start = 2 * least_unused
        sequence, seen, current = [], set(), start
        while current not in seen:
            check()
            seen.add(current)
            sequence.append(current)
            current = successor[current]
        if current != start:
            raise _BadProof('a cyclic boundary is not closed at its start')
        port_set = {endpoint // 2 for endpoint in sequence}
        if len(port_set) != len(sequence) or not port_set <= unused:
            raise _BadProof('a cyclic boundary repeats a port')
        unused.difference_update(port_set)
        word = [(-1 if endpoint % 2 else 1) * (endpoint // 2 + 1) for endpoint in sequence]
        links = [gap_indices[endpoint ^ 1] for endpoint in sequence]
        if sum(gaps[index]['fibre_flip'] for index in links) % 2:
            raise _BadProof('boundary-circle fibre orientation is inconsistent')
        index = len(loops)
        entire = not any(gaps[gap]['old_boundary_present'] for gap in links)
        loops.append(dict(id=index, word=word, gaps=links, all_core=entire, fibre_flip=False))
        if entire:
            attachments.append(dict(kind='circle', boundary_loop=index, word=word.copy(),
                                    endpoint_tokens=[], fibre_flip=False,
                                    base_anchor_port=min(port_set)))
            continue
        for first in range(len(word)):
            if not gaps[links[first - 1]]['old_boundary_present']:
                continue
            positions, parity, last = [first], False, first
            while not gaps[links[last]]['old_boundary_present']:
                check()
                parity ^= gaps[links[last]]['fibre_flip']
                last = (last + 1) % len(word)
                positions.append(last)
            run = [word[position] for position in positions]
            attachments.append(dict(kind='interval', boundary_loop=index, word=run,
                                    endpoint_tokens=[sequence[first], sequence[last] ^ 1],
                                    fibre_flip=parity,
                                    base_anchor_port=min(abs(value) for value in run) - 1))
    return dict(ports=[dict(port) for port in geometry['ports']], gaps=gaps,
                boundary_loops=loops, attachment_components=attachments,
                interval_attachments=sum(item['kind'] == 'interval' for item in attachments),
                circle_attachments=sum(item['kind'] == 'circle' for item in attachments))


def _trace_size(proof):
    if (type(proof) is not dict or type(proof.get('orbit_proof')) is not dict
            or type(proof['orbit_proof'].get('operations')) is not list):
        return None
    return len(proof['orbit_proof']['operations'])


def verify_native_moment_words(triangulation, coordinates, certificate, *,
                               max_operations=None, check=lambda: None):
    """Replay one weighted trace; never call source or orbit producers.

    Malformed proofs return False.  Source validation errors and cooperative
    callback exceptions propagate, consistently with the native checkers.
    """
    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('max_operations must be nonnegative or None')
    keys = {'schema', 'codec', 'input_sha256', 'skeleton', 'census'}
    if (type(certificate) is not dict or set(certificate) != keys
            or certificate['schema'] != 'native-moment-boundary-v2'
            or certificate['codec'] not in ('pair', 'four')):
        return False
    census = certificate['census']
    if census is not None:
        operations = _trace_size(census)
        if operations is None or (max_operations is not None and operations > max_operations):
            return False
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    if certificate['input_sha256'] != _fingerprint(triangulation, analysed, check):
        return False
    geometry = _reference_parallelity(prepared, analysed, check)
    if not geometry['ports']:
        if census is not None:
            return False
        expected = _reference_output(geometry, None, None, check)
        return certificate_equal(certificate['skeleton'], expected)
    if census is None:
        return False
    pairings, weights, packing = _reference_query(geometry, check, certificate['codec'])
    if not verify_weighted_orbit_certificate(2 * geometry['corner_points'], pairings, weights,
                                             census, dimension=1, check=check):
        return False
    try:
        expected = _reference_output(geometry, census, packing, check)
    except _BadProof:
        return False
    return certificate_equal(certificate['skeleton'], expected)


def verify_native_moment_packet(triangulation, coordinates, certificate, *,
                                max_operations=None, check=lambda: None):
    """Authenticate the upstream packet, boundary output and base ownership.

    max_operations bounds the sum of all four inherited traces and the new
    census trace.  Source proof verification is not treated as free work.
    """
    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('max_operations must be nonnegative or None')
    keys = {'schema', 'parallelity', 'boundary', 'base_interfaces'}
    if (type(certificate) is not dict or set(certificate) != keys
            or certificate['schema'] != 'native-moment-parallelity-interface-v1'):
        return False
    source = certificate['parallelity']
    if type(source) is not dict:
        return False
    total = 0
    for key in ('vertex_selector', 'boundary_selector', 'polygon_weights', 'fibre_cover'):
        proof = source.get(key)
        if key.endswith('selector'):
            if type(proof) is not dict:
                return False
            proof = proof.get('weighted_certificate')
        amount = _trace_size(proof)
        if amount is None:
            return False
        total += amount
    if max_operations is not None and total > max_operations:
        return False
    if not verify_normal_cut_parallelity(triangulation, coordinates, source, check=check):
        return False
    remaining = None if max_operations is None else max_operations - total
    boundary = certificate['boundary']
    if not verify_native_moment_words(triangulation, coordinates, boundary,
                                      max_operations=remaining, check=check):
        return False
    profiles = source['summary']['base_profiles']
    ownership, loops_by_profile = {}, [[] for _ in profiles]
    for index, profile in enumerate(profiles):
        for port in profile['core_ports']:
            ownership[_integer(port)] = index
    for loop in boundary['skeleton']['boundary_loops']:
        port_ids = [abs(_integer(value)) - 1 for value in loop['word']]
        if len({ownership[port] for port in port_ids}) != 1:
            return False
        loops_by_profile[ownership[port_ids[0]]].append(_integer(loop['id']))
    expected = []
    for index, profile in enumerate(profiles):
        ports = [_integer(port) for port in profile['core_ports']]
        multiplicity = _integer(profile['multiplicity'])
        passive = _integer(profile['boundary_components']) - len(loops_by_profile[index])
        if passive < 0 or (ports and multiplicity != 1):
            return False
        expected.append(dict(profile=index, multiplicity=multiplicity, core_ports=ports,
                             active_boundary_loops=loops_by_profile[index],
                             passive_boundary_components_per_copy=passive))
    return certificate_equal(certificate['base_interfaces'], expected)
