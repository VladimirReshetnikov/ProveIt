"""Native source-bound moment first returns with exact free-edge lengths.

Adapted from report 93; the independent checker and source tests are retained.
Put Topology/UnknotRecognition/fast on PYTHONPATH.  No expanded normal
coordinate, boundary-edge or corner list is constructed.

The geometric query is compiled from the maintained parallelity free-edge
packet.  Local fibre charts are retained; coherent orientations of different
boundary circles of the same base are not part of this interface.
"""

from copy import deepcopy
from math import isqrt

from .integer_codec import encoded_integer
from .interval_orbits import IntervalPairing
from .normal_parallelity_geometry import _parallelity_geometry
from .normal_parallelity_verify import verify_normal_cut_parallelity
from .normal_surface_geometry import _prepare, _coordinates, _fingerprint
from .weighted_orbits import weighted_orbit_histogram


def _isometry(left, right, first, stop):
    a = sorted(left[0] * r + left[1] for r in (first, stop - 1))
    b = sorted(right[0] * r + right[1] for r in (first, stop - 1))
    return IntervalPairing(*a, *b, left[0] != right[0])


def _moment_query(g, check, codec='pair'):
    """One double-cover query; own each old edge at its start occurrence.

    Every free-edge record occurs once in the authenticated packet.  Its
    rank interval maps injectively to the chosen start-corner interval.
    Distinct free edges may have equivalent owners, and their masses add.
    """
    n = g['corner_points']
    r = 4 * len(g['ports'])
    if codec == 'four':
        shift = (r * (r + 1) * (2 * r + 1) // 6).bit_length()
        edge_bits = 3 * shift
    elif codec == 'pair':
        shift = (2 * r).bit_length()
        edge_bits = (2 * (r + (r * r << shift))).bit_length()
    else:
        raise ValueError('codec must be pair or four')
    packing = dict(codec=codec, sum_bits=shift, edge_bits=edge_bits)
    edge_unit = 1 << edge_bits
    pairs, weights, owners = [], [], []
    for gluing in g['gluings']:
        check()
        p, q = (g['polygons'][gluing[key]] for key in ('left', 'right'))
        for end in (0, 1):
            i = (gluing['left_edge'] + end) % len(p['vertices'])
            j = (gluing['right_edge'] + (end ^ gluing['ends_reverse'])) % len(q['vertices'])
            a = gluing['left_map']
            b = gluing['right_map']
            left = (a[0], a[1] - p['start'] + p['corner_starts'][i])
            right = (b[0], b[1] - q['start'] + q['corner_starts'][j])
            for sheet in (0, 1):
                target = sheet ^ gluing['fibre_flip']
                pairs.append(_isometry((left[0], left[1] + sheet * n),
                                       (right[0], right[1] + target * n),
                                       gluing['rank_start'], gluing['rank_stop']))
    for free_id, edge in enumerate(g['free_edges']):
        check()
        if not edge['original_boundary']:
            continue
        p = g['polygons'][edge['polygon']]
        first, stop = edge['rank_start'], edge['rank_stop']
        starts = [p['corner_starts'][(edge['edge'] + k) % len(p['vertices'])] - 1
                  for k in (0, 1)]
        for sheet in (0, 1):
            a, b = (start + sheet * n for start in starts)
            pairs.append(_isometry((1, a), (1, b), first, stop))
            weights.append((a + first, a + stop, [edge_unit]))
            owners.append(dict(free_edge=free_id, sheet=sheet,
                               start=a + first, stop=a + stop))
    for port in g['ports']:
        check()
        p = g['polygons'][port['polygon']]
        for end in (0, 1):
            token = 2 * port['id'] + end
            slot = (port['edge'] + end) % len(p['vertices'])
            point = p['corner_starts'][slot] + port['rank'] - 1
            for sheet in (0, 1):
                label = 2 * token + sheet + 1
                value = (1 + (label << shift) + (label * label << (2 * shift))
                         if codec == 'four' else label + (label * label << shift))
                x = point + sheet * n
                weights.append((x, x + 1, [value]))
    return pairs, weights, packing, owners


def _decode(histogram, number, packing, check):
    """Decode distinct lifted endpoint occurrences with global inventory checks.

    In pair mode, a singleton would decode roots 0,i and is rejected.  A
    complete partition has number/2 accepted rows, each consuming at least
    two actual labels; hence global inventory forces exactly two per row.
    Geometry is separately needed to identify such rows with boundary paths.
    """
    shift = packing['sum_bits']
    mask = (1 << shift) - 1
    matching, lengths = {}, {}
    for row in histogram:
        check()
        weight, copies = encoded_integer(row['weight'][0]), encoded_integer(row['orbits'])
        if weight < 0 or copies < 1:
            raise ArithmeticError('negative moment or invalid multiplicity')
        if packing['codec'] == 'four':
            count = weight & mask
            total = (weight >> shift) & mask
            square = (weight >> (2 * shift)) & mask
            length = weight >> (3 * shift)
            if not count:
                if total or square:
                    raise ArithmeticError('terminal-free class has nonzero moments')
                continue
        else:
            edge_bits = packing['edge_bits']
            length = weight >> edge_bits
            tail = weight & ((1 << edge_bits) - 1)
            if tail == 0:
                continue
            total, square, count = tail & mask, tail >> shift, 2
        discriminant = 2 * square - total * total
        if count != 2 or copies != 1 or discriminant <= 0:
            raise ArithmeticError('residual class does not have two distinct labels')
        difference = isqrt(discriminant)
        if difference * difference != discriminant or (total - difference) % 2:
            raise ArithmeticError('moment pair is not integral')
        left, right = (total - difference) // 2, (total + difference) // 2
        if not 1 <= left < right <= number:
            raise ArithmeticError('decoded endpoint label out of range')
        if left * left + right * right != square or left + right != total:
            raise ArithmeticError('decoded endpoint moments disagree')
        left, right = left - 1, right - 1
        if left in matching or right in matching:
            raise ArithmeticError('a lifted endpoint occurs twice')
        matching[left], matching[right] = right, left
        lengths[left] = lengths[right] = length
    if set(matching) != set(range(number)):
        raise ArithmeticError('missing lifted endpoint')
    return matching, lengths


def _assemble(g, histogram, packing, check):
    number = 4 * len(g['ports'])
    lifted, lengths = _decode(histogram, number, packing, check) if number else ({}, {})
    mate, flip, base_lengths = {}, {}, {}
    for endpoint in range(number // 2):
        check()
        image = lifted[2 * endpoint]
        other, twist = divmod(image, 2)
        if (other == endpoint or lifted[2 * endpoint + 1] != 2 * other + (twist ^ 1)
                or lengths[2 * endpoint] != lengths[2 * endpoint + 1]):
            raise ArithmeticError('a residual gap does not have two equal-length lifts')
        mate[endpoint], flip[endpoint] = other, bool(twist)
        base_lengths[endpoint] = lengths[2 * endpoint]
    gaps, gap_id = [], {}
    for endpoint in range(number // 2):
        other = mate[endpoint]
        if endpoint < other:
            index = len(gaps)
            gap_id[endpoint] = gap_id[other] = index
            gaps.append(dict(id=index, ends=[endpoint, other],
                             old_boundary_present=base_lengths[endpoint] > 0,
                             fibre_flip=flip[endpoint], unmarked_edges=base_lengths[endpoint]))
    # Direct matching traversal, adapted from the maintained native cyclic
    # compiler.  No O(p)-bit endpoint masks are materialized after decoding.
    loops, used = [], set()
    for initial in range(number // 4):
        if initial in used:
            continue
        endpoint, word, links, twisting = 2 * initial, [], [], False
        while True:
            check()
            port, direction = endpoint // 2, 1 if endpoint % 2 == 0 else -1
            if port in used:
                raise ArithmeticError('a boundary word visits a port twice')
            used.add(port)
            word.append(direction * (port + 1))
            exit_endpoint = endpoint ^ 1
            index = gap_id[exit_endpoint]
            links.append(index)
            twisting ^= gaps[index]['fibre_flip']
            endpoint = mate[exit_endpoint]
            if endpoint == 2 * initial:
                break
        if twisting:
            raise ArithmeticError('boundary-circle fibre orientation is inconsistent')
        loops.append(dict(id=len(loops), word=word, gaps=links,
                          all_core=all(not gaps[index]['old_boundary_present'] for index in links),
                          fibre_flip=False))
    attachments = []
    for loop in loops:
        check()
        word, links = loop['word'], loop['gaps']
        starts = [i for i in range(len(word)) if gaps[links[i - 1]]['old_boundary_present']]
        if not starts:
            attachments.append(dict(kind='circle', boundary_loop=loop['id'], word=word.copy(),
                                    endpoint_tokens=[], fibre_flip=False,
                                    base_anchor_port=min(abs(x) for x in word) - 1))
            continue
        for first in starts:
            run, position, twisting = [], first, False
            while True:
                check()
                run.append(word[position])
                if gaps[links[position]]['old_boundary_present']:
                    break
                twisting ^= gaps[links[position]]['fibre_flip']
                position = (position + 1) % len(word)
            first_token = 2 * (abs(run[0]) - 1) + int(run[0] < 0)
            last_token = 2 * (abs(run[-1]) - 1) + int(run[-1] > 0)
            attachments.append(dict(kind='interval', boundary_loop=loop['id'], word=run,
                                    endpoint_tokens=[first_token, last_token], fibre_flip=twisting,
                                    base_anchor_port=min(abs(x) for x in run) - 1))
    return dict(ports=[dict(port) for port in g['ports']], gaps=gaps, boundary_loops=loops,
                attachment_components=attachments,
                interval_attachments=sum(item['kind'] == 'interval' for item in attachments),
                circle_attachments=sum(item['kind'] == 'circle' for item in attachments))


def _compile(g, fingerprint, max_cycles, record_certificate, check, codec):
    result = dict(status='INCONCLUSIVE', stats={},
                  trust='source-bound cyclic core ports, exact old-edge lengths and local fibre transport')
    if not g['ports']:
        skeleton = _assemble(g, [], 0, check)
        result.update(status='COMPLETE', skeleton=skeleton)
        if record_certificate:
            result['certificate'] = dict(schema='native-moment-boundary-v2', codec=codec,
                                        input_sha256=fingerprint, skeleton=skeleton, census=None)
        return result
    pairs, weights, packing, owners = _moment_query(g, check, codec)
    answer = weighted_orbit_histogram(2 * g['corner_points'], pairs, weights,
                                     dimension=1, periodic_rule='aht',
                                     max_cycles=max_cycles, record_certificate=record_certificate,
                                     check=check)
    result['stats']['census'] = answer['stats']
    result['stats']['compilation'] = dict(weight_dimension=1, weighted_calls=1,
                                       codec=codec,
                                       terminal_labels=4 * len(g['ports']),
                                       sum_field_bits=packing['sum_bits'],
                                       edge_field_bits=packing['edge_bits'],
                                       maximum_additive_weight_bits=max(v[0].bit_length() for _, _, v in weights),
                                       owner_intervals=len(owners),
                                       pairing_records=len(pairs), weight_records=len(weights))
    if answer['status'] != 'COMPLETE':
        return result
    skeleton = _assemble(g, answer['histogram'], packing, check)
    result.update(status='COMPLETE', skeleton=skeleton)
    if record_certificate:
        result['certificate'] = dict(schema='native-moment-boundary-v2', codec=codec,
                                    input_sha256=fingerprint, skeleton=skeleton,
                                    census=answer['certificate'])
    check()
    return result


def normal_parallelity_moment_words(triangulation, coordinates, *, codec='pair', max_cycles=None,
                                    record_certificate=False, check=lambda: None):
    """Source -> complete first-return/cyclic interface with one scalar census.

    This entry point has the same geometry contract as the maintained native
    boundary compiler.  It adds ``unmarked_edges`` to each gap.  Its independent
    checker reconstructs source geometry and authenticates the weighted proof.
    Unported boundary circles and component ownership need a base-profile
    certificate: use ``moments_from_parallelity_packet`` for those data.
    ``codec='pair'`` uses the smaller path-local scalar; ``codec='four'``
    retains the incoming count/sum/squares/length scalar for comparison.
    """
    check()
    if codec not in ('pair', 'four'):
        raise ValueError('codec must be pair or four')
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be nonnegative or None')
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    g = _parallelity_geometry(prepared, analysed, check)
    return _compile(g, _fingerprint(triangulation, analysed, check),
                    max_cycles, record_certificate, check, codec)


def _transport_decode(value):
    if isinstance(value, dict):
        return {key: _transport_decode(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_transport_decode(item) for item in value]
    if isinstance(value, str) and value.lstrip('+-').lower().startswith('0x'):
        return encoded_integer(value)
    return value


def _base_interfaces(profiles, skeleton):
    owner = {port: index for index, row in enumerate(profiles) for port in row['core_ports']}
    active = [[] for _ in profiles]
    for loop in skeleton['boundary_loops']:
        ports = [abs(value) - 1 for value in loop['word']]
        index = owner[ports[0]]
        if any(owner[port] != index for port in ports):
            raise ArithmeticError('a cyclic boundary crosses base owners')
        active[index].append(loop['id'])
    output = []
    for index, profile in enumerate(profiles):
        if profile['core_ports'] and profile['multiplicity'] != 1:
            raise ArithmeticError('a port-bearing base profile must be unique')
        passive = profile['boundary_components'] - len(active[index])
        if passive < 0:
            raise ArithmeticError('active cycles exceed certified base boundary count')
        output.append(dict(profile=index, multiplicity=profile['multiplicity'],
                           core_ports=profile['core_ports'].copy(),
                           active_boundary_loops=active[index],
                           passive_boundary_components_per_copy=passive))
    return output


def moments_from_parallelity_packet(triangulation, coordinates, parallelity_certificate, *,
                                    codec='pair', max_cycles=None, record_certificate=False,
                                    check=lambda: None):
    """Authenticate a complete native packet, then run one new scalar census.

    Source authentication replays the four existing packet proofs.  It is
    additional work and is not included in the claim of one *new* census.
    The output also binds each active loop to its base profile and retains
    passive boundary counts, including multiplicities of port-free bases.
    """
    check()
    if codec not in ('pair', 'four'):
        raise ValueError('codec must be pair or four')
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be nonnegative or None')
    packet = deepcopy(parallelity_certificate)
    if not verify_normal_cut_parallelity(triangulation, coordinates, packet, check=check):
        raise ValueError('parallelity source packet failed independent verification')
    g = _transport_decode(packet['geometry'])
    profiles = _transport_decode(packet['summary']['base_profiles'])
    result = _compile(g, packet['input_sha256'], max_cycles, record_certificate, check, codec)
    if result['status'] != 'COMPLETE':
        return result
    interfaces = _base_interfaces(profiles, result['skeleton'])
    result['base_interfaces'] = interfaces
    if record_certificate:
        result['certificate'] = dict(schema='native-moment-parallelity-interface-v1',
                                    parallelity=packet, boundary=result['certificate'],
                                    base_interfaces=interfaces)
    return result


def native_projection(skeleton):
    """The exact pre-existing output contract, for differential verification."""
    answer = deepcopy(skeleton)
    for gap in answer['gaps']:
        gap.pop('unmarked_edges', None)
    return answer
