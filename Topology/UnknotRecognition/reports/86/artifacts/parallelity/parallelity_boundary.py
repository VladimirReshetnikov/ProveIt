"""Ordered core interfaces of an authenticated source parallelity packet.

This research prototype consumes the geometry from ``normal_cut_parallelity``.
It does not authenticate that source geometry or perform a topological surgery.
The upstream ``verify_normal_cut_parallelity`` supplies source authentication;
the checker in ``parallelity_boundary_verify`` replays the extra orbit proofs.

No polygon copy or old-boundary path is expanded.  A successful result records
the cyclic order of ports, adjacent port endpoints, and interval-fibre transport.
``disc_replacement_plan`` then specifies the locally justified relative handles.
It does not construct an admissible patterned hierarchy.
"""

from hashlib import sha256
import json

from fastunknot.integer_codec import encoded_integer, json_safe
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.weighted_orbits import weighted_orbit_histogram


def geometry_digest(geometry):
    encoded = json.dumps(json_safe(geometry), sort_keys=True,
                         separators=(',', ':')).encode('utf-8')
    return sha256(encoded).hexdigest()


def _pair(left, right, lo, hi):
    a, b = left
    c, d = right
    domain = sorted((a*lo+b, a*(hi-1)+b))
    image = sorted((c*lo+d, c*(hi-1)+d))
    return IntervalPairing(*domain, *image, a != c)


def _queries(geometry, check):
    polygons = geometry['polygons']
    size = geometry['corner_points']
    vertex_pairs, gap_pairs, lift_pairs = [], [], []
    endpoints = [None] * (2*len(geometry['ports']))
    for link in geometry['gluings']:
        check()
        left, right = polygons[link['left']], polygons[link['right']]
        a, b = link['left_map']
        c, d = link['right_map']
        lo, hi = link['rank_start'], link['rank_stop']
        for end in (0, 1):
            i = (link['left_edge']+end) % len(left['vertices'])
            j = (link['right_edge']+(end ^ link['ends_reverse']))
            j %= len(right['vertices'])
            first = (a, b+left['corner_starts'][i]-left['start'])
            last = (c, d+right['corner_starts'][j]-right['start'])
            vertex_pairs.append(_pair(first, last, lo, hi))
            for sheet in (0, 1):
                flip = sheet ^ link['fibre_flip']
                lift_pairs.append(_pair((first[0], first[1]+sheet*size),
                                        (last[0], last[1]+flip*size), lo, hi))
    gap_pairs.extend(vertex_pairs)
    for edge in geometry['free_edges']:
        check()
        polygon = polygons[edge['polygon']]
        lo, hi = edge['rank_start'], edge['rank_stop']
        first = polygon['corner_starts'][edge['edge']]-1
        last = polygon['corner_starts'][(edge['edge']+1)
                                       % len(polygon['vertices'])]-1
        if edge['original_boundary']:
            gap_pairs.append(_pair((1, first), (1, last), lo, hi))
            for sheet in (0, 1):
                lift_pairs.append(_pair((1, first+sheet*size),
                                        (1, last+sheet*size), lo, hi))
        else:
            port = edge['port']
            if hi != lo+1 or not 0 <= port < len(geometry['ports']):
                raise ValueError('a source port must be one labelled side')
            if endpoints[2*port] is not None:
                raise ValueError('source port occurs more than once')
            endpoints[2*port:2*port+2] = [first+lo, last+lo]
    if any(point is None for point in endpoints):
        raise ValueError('source port endpoint is absent')
    weights = [(point, point+1, [1 << label])
               for label, point in enumerate(endpoints)]
    lifted = [(point+sheet*size, point+sheet*size+1,
               [1 << (2*label+sheet)])
              for label, point in enumerate(endpoints) for sheet in (0, 1)]
    return size, vertex_pairs, gap_pairs, lift_pairs, weights, lifted


def _groups(histogram, labels, pair_only=False):
    groups, seen = [], 0
    for row in histogram:
        mask = encoded_integer(row['weight'][0])
        copies = encoded_integer(row['orbits'])
        if mask == 0:
            continue
        if mask < 0 or mask.bit_length() > labels or copies != 1:
            raise ArithmeticError('invalid marked-orbit weight')
        if seen & mask:
            raise ArithmeticError('a marked endpoint is repeated')
        seen |= mask
        group = []
        while mask:
            bit = mask & -mask
            group.append(bit.bit_length()-1)
            mask -= bit
        permitted = (2,) if pair_only else (1, 2)
        if len(group) not in permitted:
            raise ArithmeticError('marked component is not a boundary gap or vertex')
        groups.append(group)
    if seen != (1 << labels)-1:
        raise ArithmeticError('marked endpoint partition is incomplete')
    return sorted(groups)


def _assemble(port_count, vertices, matched, signed, check):
    size = 2*port_count
    vertex_class = {}
    for index, group in enumerate(vertices):
        for endpoint in group:
            vertex_class[endpoint] = index
    mate = {}
    for a, b in matched:
        mate[a], mate[b] = b, a
    flips = {}
    if signed is not None:
        lifted_mate = {}
        for a, b in signed:
            lifted_mate[a], lifted_mate[b] = b, a
        for endpoint in range(size):
            target = lifted_mate[2*endpoint]
            if target//2 != mate[endpoint]:
                raise ArithmeticError('lifted gap has the wrong endpoint')
            flip = target % 2
            if lifted_mate[2*endpoint+1] != 2*mate[endpoint]+(flip ^ 1):
                raise ArithmeticError('lifted gap violates the deck involution')
            flips[endpoint] = bool(flip)
    gaps = []
    for a, b in matched:
        zero = vertex_class[a] == vertex_class[b]
        gaps.append(dict(ends=[a, b], zero_length=zero,
                         fibre_flip=flips.get(a)))
    cycles, used = [], set()
    for port in range(port_count):
        check()
        if port in used:
            continue
        start = current = 2*port
        word, nonempty, holonomy = [], 0, False
        while True:
            check()
            label, entry = divmod(current, 2)
            if label in used:
                raise ArithmeticError('cyclic interface revisits a port')
            used.add(label)
            exit_end = current ^ 1
            next_end = mate[exit_end]
            zero = vertex_class[exit_end] == vertex_class[next_end]
            nonempty += int(not zero)
            if signed is not None:
                holonomy ^= flips[exit_end]
            word.append(dict(port=label, entry_end=entry,
                             next_port=next_end//2, next_entry_end=next_end % 2,
                             gap_zero_length=zero,
                             gap_fibre_flip=flips.get(exit_end)))
            current = next_end
            if current == start:
                break
        if signed is not None and holonomy:
            raise ArithmeticError('orientable source bundle has twisted boundary fibre')
        cycles.append(dict(ports=word, full_core_circle=nonempty == 0,
                           core_interval_components=nonempty,
                           fibre_holonomy=False if signed is not None else None))
    attachment_chi = len(vertices)-port_count
    if attachment_chi != sum(c['core_interval_components'] for c in cycles):
        raise ArithmeticError('attachment Euler characteristic disagrees')
    return dict(port_count=port_count, endpoint_vertices=vertices, gaps=gaps,
                boundary_cycles=cycles, marked_boundary_components=len(cycles),
                core_attachment_vertices=len(vertices),
                attachment_euler_characteristic=attachment_chi,
                fibre_transport_checked=signed is not None)


def parallelity_boundary_interface(geometry, *, max_cycles=None,
                                   record_certificate=False, check=lambda: None):
    """Extract ordered interfaces from already authenticated source geometry.

    Three weighted queries share ``max_cycles``.  A cap never creates a
    partial interface.  Callback exceptions propagate.  Numerical ranks and
    multiplicities are binary; the input packet itself must use Python ints.
    """
    check()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be nonnegative or None')
    port_count = len(geometry['ports'])
    size, vp, gp, lp, weights, lifted = _queries(geometry, check)
    result = dict(status='INCONCLUSIVE',
                  trust='authenticated source geometry required; no hierarchy or knot verdict')
    remaining, statistics, proofs, histograms = max_cycles, {}, {}, {}
    if port_count:
        queries = [('vertices', size, vp, weights),
                   ('gaps', size, gp, weights),
                   ('fibre_gaps', 2*size, lp, lifted)]
        for name, universe, pairs, markers in queries:
            query = weighted_orbit_histogram(
                universe, pairs, markers, dimension=1, max_cycles=remaining,
                record_certificate=record_certificate, check=check)
            statistics[name] = query['stats']
            result['stats'] = statistics
            if remaining is not None:
                remaining -= query['stats']['orbit_cycles']
            if query['status'] != 'COMPLETE':
                return result
            histograms[name] = query['histogram']
            if record_certificate:
                proofs[name] = query['certificate']
        vertices = _groups(histograms['vertices'], 2*port_count)
        matched = _groups(histograms['gaps'], 2*port_count, pair_only=True)
        signed = _groups(histograms['fibre_gaps'], 4*port_count, pair_only=True)
    else:
        vertices, matched, signed = [], [], []
    interface = _assemble(port_count, vertices, matched, signed, check)
    result.update(status='COMPLETE', interface=interface, stats=statistics)
    if record_certificate:
        result['certificate'] = dict(schema='source-parallelity-boundary-v1',
                                     geometry_sha256=geometry_digest(geometry),
                                     interface=interface, orbit_proofs=proofs)
    check()
    return result


def disc_replacement_plan(interface, base_profiles, *, check=lambda: None):
    """Record justified local relative handles; perform no geometric surgery.

    Profiles must be those authenticated for the same source geometry.  Whole
    attaching circles add 2-handles; r nonempty proper attaching intervals
    add r-1 relative 1-handles after collar transport.  No admissibility or
    boundary-pattern essentiality is inferred.
    """
    check()
    port_count = interface['port_count']
    owner = {}
    for index, profile in enumerate(base_profiles):
        for port in profile['core_ports']:
            if port in owner:
                raise ValueError('a core port belongs to several profiles')
            owner[port] = index
    if set(owner) != set(range(port_count)):
        raise ValueError('profiles do not partition the interface ports')
    cycles_by_profile = {index: [] for index in range(len(base_profiles))}
    for number, cycle in enumerate(interface['boundary_cycles']):
        owners = {owner[entry['port']] for entry in cycle['ports']}
        if len(owners) != 1:
            raise ValueError('one boundary cycle crosses base components')
        cycles_by_profile[owners.pop()].append(number)
    records, ones, twos, balls = [], 0, 0, 0
    for index, profile in enumerate(base_profiles):
        check()
        ports = profile['core_ports']
        marked = cycles_by_profile[index]
        boundary = profile['boundary_components']
        if len(marked) > boundary or ports and profile['multiplicity'] != 1:
            raise ValueError('inconsistent attached base profile')
        record = dict(profile=index, core_ports=list(ports), boundary_cycles=marked,
                      unmarked_boundary_components=boundary-len(marked),
                      multiplicity=profile['multiplicity'])
        disc = (profile['orientable'] and profile['euler_characteristic'] == 1
                and boundary == 1 and profile['product'])
        if not disc:
            record.update(action='retain_source_bundle', relative_handles=None)
        elif not ports:
            balls += profile['multiplicity']
            record.update(action='count_isolated_balls', relative_handles=None)
        else:
            if len(marked) != 1:
                raise ValueError('an attached disc has one marked boundary circle')
            cycle = interface['boundary_cycles'][marked[0]]
            if cycle['full_core_circle']:
                twos += 1
                record.update(action='relative_two_handle',
                              relative_handles=dict(index=2, count=1),
                              relative_euler_characteristic=1)
            else:
                components = cycle['core_interval_components']
                if components < 1:
                    raise ValueError('proper disc attachment has no interval')
                ones += components-1
                record.update(action='relative_one_handles_after_collar_transport',
                              attaching_intervals=components,
                              relative_handles=dict(index=1, count=components-1),
                              relative_euler_characteristic=1-components)
        records.append(record)
    if ones+twos > port_count:
        raise ArithmeticError('disc replacement exceeds the port bound')
    return dict(records=records, relative_one_handles=ones,
                relative_two_handles=twos, isolated_balls=balls,
                status='LOCAL_RELATIVE_HANDLE_PLAN',
                performed_surgery=False, admissible_hierarchy=False)
