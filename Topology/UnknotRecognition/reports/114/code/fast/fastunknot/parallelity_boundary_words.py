"""Cyclic, fibre-labelled core interfaces without expanding normal stacks.

The source parallelity bases already have O(T) exceptional core-facing arcs.
This operator contracts only the complementary arcs of their boundary circles.
It retains their order, endpoint charts, and fibre transport, and distinguishes
proper attaching intervals from whole attaching circles. No arbitrary boundary
pattern hidden inside a complementary arc is preserved by this contract.
"""

from .interval_orbits import IntervalPairing
from .normal_surface_geometry import _prepare, _coordinates, _fingerprint
from .normal_parallelity_geometry import _parallelity_geometry
from .weighted_orbits import weighted_orbit_histogram


def _pair(left, right, lo, hi):
    a, b = left
    c, d = right
    domain = sorted((a * lo + b, a * (hi - 1) + b))
    image = sorted((c * lo + d, c * (hi - 1) + d))
    return IntervalPairing(*domain, *image, a != c)


def _queries(geometry, check):
    """Corner equivalence and the doubled boundary with core edges deleted."""
    n = geometry['corner_points']
    polygons = geometry['polygons']
    vertices, doubled = [], []
    for link in geometry['gluings']:
        check()
        p, q = polygons[link['left']], polygons[link['right']]
        a, b = link['left_map'], link['right_map']
        lo, hi = link['rank_start'], link['rank_stop']
        for end in (0, 1):
            i = (link['left_edge'] + end) % len(p['vertices'])
            j = (link['right_edge'] + (end ^ link['ends_reverse'])) % len(q['vertices'])
            left = (a[0], a[1] + p['corner_starts'][i] - p['start'])
            right = (b[0], b[1] + q['corner_starts'][j] - q['start'])
            vertices.append(_pair(left, right, lo, hi))
            for sheet in (0, 1):
                target = sheet ^ link['fibre_flip']
                doubled.append(_pair((left[0], left[1] + sheet * n),
                                     (right[0], right[1] + target * n), lo, hi))
    for edge in geometry['free_edges']:
        check()
        if not edge['original_boundary']:
            continue
        p = polygons[edge['polygon']]
        i, j = edge['edge'], (edge['edge'] + 1) % len(p['vertices'])
        for sheet in (0, 1):
            doubled.append(_pair((1, p['corner_starts'][i] - 1 + sheet * n),
                                 (1, p['corner_starts'][j] - 1 + sheet * n),
                                 edge['rank_start'], edge['rank_stop']))
    vertex_weights, cover_weights, endpoints = [], [], []
    for port in geometry['ports']:
        check()
        p = polygons[port['polygon']]
        for end in (0, 1):
            token = 2 * port['id'] + end
            slot = (port['edge'] + end) % len(p['vertices'])
            point = p['corner_starts'][slot] + port['rank'] - 1
            endpoints.append(point)
            vertex_weights.append((point, point + 1, [1 << token]))
            for sheet in (0, 1):
                lift = point + sheet * n
                cover_weights.append((lift, lift + 1, [1 << (2 * token + sheet)]))
    return vertices, vertex_weights, doubled, cover_weights, endpoints


def _marked_groups(histogram, tags, allowed_sizes, check):
    """Decode a partition of unique tags; zero-tag components are irrelevant."""
    groups, seen = [], 0
    for row in histogram:
        check()
        mask = row['weight'][0]
        if mask == 0:
            continue
        if mask < 0 or mask.bit_length() > tags or seen & mask or row['orbits'] != 1:
            raise ArithmeticError('endpoint tags do not form a partition')
        bits = []
        current = mask
        while current:
            bit = current & -current
            bits.append(bit.bit_length() - 1)
            current -= bit
        if len(bits) not in allowed_sizes:
            raise ArithmeticError('marked boundary component has the wrong degree')
        groups.append(bits)
        seen |= mask
    if seen != (1 << tags) - 1:
        raise ArithmeticError('an endpoint tag is missing')
    return groups


def _skeleton(geometry, vertices, cover, check):
    ports = geometry['ports']
    count = len(ports)
    vertex_groups = _marked_groups(vertices, 2 * count, {1, 2}, check)
    same_vertex = {tuple(pair) for pair in vertex_groups if len(pair) == 2}
    lifted = _marked_groups(cover, 4 * count, {2}, check)
    lift_mate = {}
    for a, b in lifted:
        lift_mate[a] = b
        lift_mate[b] = a
    mate, flip = {}, {}
    for endpoint in range(2 * count):
        check()
        target = lift_mate[2 * endpoint]
        other, twist = divmod(target, 2)
        if other == endpoint or lift_mate[2 * endpoint + 1] != 2 * other + (twist ^ 1):
            raise ArithmeticError('a marked gap is not a trivial interval bundle')
        mate[endpoint], flip[endpoint] = other, bool(twist)
    gaps, gap_id = [], {}
    for a in range(2 * count):
        b = mate[a]
        if a > b:
            continue
        index = len(gaps)
        gaps.append(dict(id=index, ends=[a, b],
                         old_boundary_present=(a, b) not in same_vertex,
                         fibre_flip=flip[a]))
        gap_id[a] = gap_id[b] = index
    if len(gaps) != count:
        raise ArithmeticError('the marked gaps are not a perfect matching')

    loops, used = [], set()
    for initial in range(count):
        if initial in used:
            continue
        check()
        endpoint, word, loop_gaps, twisting = 2 * initial, [], [], False
        while True:
            check()
            port, direction = endpoint // 2, 1 if endpoint % 2 == 0 else -1
            if port in used:
                raise ArithmeticError('a boundary word visits a port twice')
            used.add(port)
            word.append(direction * (port + 1))
            exit_endpoint = endpoint ^ 1
            index = gap_id[exit_endpoint]
            loop_gaps.append(index)
            twisting ^= gaps[index]['fibre_flip']
            endpoint = mate[exit_endpoint]
            if endpoint == 2 * initial:
                break
        if twisting:
            raise ArithmeticError('an orientable total bundle twists around a boundary circle')
        loops.append(dict(id=len(loops), word=word, gaps=loop_gaps,
                          all_core=all(not gaps[i]['old_boundary_present'] for i in loop_gaps),
                          fibre_flip=False))

    attachments = []
    for loop in loops:
        check()
        word, links = loop['word'], loop['gaps']
        starts = [i for i in range(len(word))
                  if gaps[links[i - 1]]['old_boundary_present']]
        if not starts:
            attachments.append(dict(kind='circle', boundary_loop=loop['id'],
                                    word=word.copy(), endpoint_tokens=[], fibre_flip=False,
                                    base_anchor_port=min(abs(x) for x in word) - 1))
            continue
        for first in starts:
            run, position, twist = [], first, False
            while True:
                check()
                run.append(word[position])
                if gaps[links[position]]['old_boundary_present']:
                    break
                twist ^= gaps[links[position]]['fibre_flip']
                position = (position + 1) % len(word)
            entry = 2 * (abs(run[0]) - 1) + int(run[0] < 0)
            exit_endpoint = 2 * (abs(run[-1]) - 1) + int(run[-1] > 0)
            attachments.append(dict(kind='interval', boundary_loop=loop['id'], word=run,
                                    endpoint_tokens=[entry, exit_endpoint], fibre_flip=twist,
                                    base_anchor_port=min(abs(x) for x in run) - 1))
    return dict(ports=[dict(p) for p in ports], gaps=gaps, boundary_loops=loops,
                attachment_components=attachments,
                interval_attachments=sum(a['kind'] == 'interval' for a in attachments),
                circle_attachments=sum(a['kind'] == 'circle' for a in attachments))


def normal_parallelity_boundary_words(triangulation, coordinates, *, max_cycles=None,
                                      record_certificate=False, check=lambda: None):
    """Construct the exact reduced boundary pair on every core-ported base.

    Positive words traverse local port edge 0 -> 1, using one-based port IDs.
    A following gap records whether original boundary is present and the fibre
    reversal between its endpoint charts. Unported boundary circles, genus,
    and additional original-boundary markings are outside this output contract.
    ``base_anchor_port`` joins a component to existing base-profile port masks.
    The two discovery queries share ``max_cycles``; exhausted work has no result.
    """
    check()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be nonnegative or None')
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    geometry = _parallelity_geometry(prepared, analysed, check)
    result = dict(status='INCONCLUSIVE', stats={},
                  trust='source-bound cyclic core ports and fibre transport; no hierarchy or knot verdict')
    if not geometry['ports']:
        skeleton = _skeleton(geometry, [], [], check)
        result.update(status='COMPLETE', skeleton=skeleton)
        if record_certificate:
            result['certificate'] = dict(schema='parallelity-boundary-words-v1',
                                        input_sha256=_fingerprint(triangulation, analysed, check),
                                        skeleton=skeleton, vertex_partition=None, gap_cover=None)
        return result
    vp, vw, dp, dw, _ = _queries(geometry, check)
    remaining = max_cycles
    vertex = weighted_orbit_histogram(geometry['corner_points'], vp, vw, dimension=1,
                                     periodic_rule='aht',
                                     max_cycles=remaining, record_certificate=record_certificate,
                                     check=check)
    result['stats']['vertices'] = vertex['stats']
    if vertex['status'] != 'COMPLETE':
        return result
    if remaining is not None:
        remaining -= vertex['stats']['orbit_cycles']
    cover = weighted_orbit_histogram(2 * geometry['corner_points'], dp, dw, dimension=1,
                                    periodic_rule='aht',
                                    max_cycles=remaining, record_certificate=record_certificate,
                                    check=check)
    result['stats']['gap_cover'] = cover['stats']
    if cover['status'] != 'COMPLETE':
        return result
    count = len(geometry['ports'])
    if vertex['stats']['maximum_weight_runs'] > 4 * count + 1:
        raise ArithmeticError('sparse vertex-tag partition bound failed')
    if cover['stats']['maximum_weight_runs'] > 8 * count + 1:
        raise ArithmeticError('sparse lifted-tag partition bound failed')
    skeleton = _skeleton(geometry, vertex['histogram'], cover['histogram'], check)
    result.update(status='COMPLETE', skeleton=skeleton)
    if record_certificate:
        result['certificate'] = dict(schema='parallelity-boundary-words-v1',
                                    input_sha256=_fingerprint(triangulation, analysed, check),
                                    skeleton=skeleton, vertex_partition=vertex['certificate'],
                                    gap_cover=cover['certificate'])
    check()
    return result
