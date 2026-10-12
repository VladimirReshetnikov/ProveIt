"""Source-independent reconstruction and replay of cyclic core-port proofs.

This checker uses the raw-cut-derived parallelity reference and the independent
weighted orbit checker. It imports neither the boundary-word producer nor its
query builder, decoder, traversal routine, or discovery scheduler.
"""

from .integer_codec import encoded_integer, certificate_equal
from .interval_orbits import IntervalPairing
from .normal_surface_geometry import _prepare, _coordinates, _fingerprint
from .normal_parallelity_reference import _reference_parallelity
from .weighted_orbit_verify import verify_weighted_orbit_certificate


class _BadProof(ValueError):
    pass


def _int(value):
    try:
        return encoded_integer(value)
    except ValueError as exc:
        raise _BadProof('expected an exact integer') from exc


def _isometry(a, b, first, stop):
    source = sorted(a[0] * x + a[1] for x in (first, stop - 1))
    target = sorted(b[0] * x + b[1] for x in (first, stop - 1))
    return IntervalPairing(source[0], source[1], target[0], target[1], a[0] != b[0])


def _reference_queries(g, check):
    size = g['corner_points']
    vertices, boundary_cover = [], []
    for gluing in g['gluings']:
        check()
        first, stop = gluing['rank_start'], gluing['rank_stop']
        corners = []
        for endpoint in (0, 1):
            pair = []
            for side in ('left', 'right'):
                polygon = g['polygons'][gluing[side]]
                end = endpoint
                if side == 'right' and gluing['ends_reverse']:
                    end = 1 - end
                slot = (gluing[side + '_edge'] + end) % len(polygon['vertices'])
                slope, shift = gluing[side + '_map']
                pair.append((slope, shift - polygon['start'] + polygon['corner_starts'][slot]))
            corners.append(pair)
        for a, b in corners:
            vertices.append(_isometry(a, b, first, stop))
            for sheet in (0, 1):
                target_sheet = 1 - sheet if gluing['fibre_flip'] else sheet
                boundary_cover.append(_isometry((a[0], a[1] + size * sheet),
                                                (b[0], b[1] + size * target_sheet),
                                                first, stop))
    for free in g['free_edges']:
        check()
        if free['original_boundary']:
            polygon = g['polygons'][free['polygon']]
            slots = (free['edge'], (free['edge'] + 1) % len(polygon['vertices']))
            ends = [polygon['corner_starts'][slot] - 1 for slot in slots]
            for sheet in (0, 1):
                boundary_cover.append(_isometry((1, ends[0] + size * sheet),
                                                (1, ends[1] + size * sheet),
                                                free['rank_start'], free['rank_stop']))
    vw, dw = [], []
    for port in g['ports']:
        check()
        polygon = g['polygons'][port['polygon']]
        for endpoint in (0, 1):
            slot = (port['edge'] + endpoint) % len(polygon['vertices'])
            point = polygon['corner_starts'][slot] + port['rank'] - 1
            label = 2 * port['id'] + endpoint
            vw.append((point, point + 1, [2 ** label]))
            for sheet in (0, 1):
                dw.append((point + sheet * size, point + sheet * size + 1,
                           [2 ** (2 * label + sheet)]))
    return vertices, vw, boundary_cover, dw


def _partition(proof, number, degrees, check):
    blocks, labels = [], set()
    for item in proof['histogram']:
        check()
        value = _int(item['weight'][0])
        if value == 0:
            continue
        if value < 0 or value.bit_length() > number or _int(item['orbits']) != 1:
            raise _BadProof('invalid labelled component')
        block = [i for i in range(number) if value & (1 << i)]
        if len(block) not in degrees or labels.intersection(block):
            raise _BadProof('invalid endpoint partition')
        blocks.append(block)
        labels.update(block)
    if labels != set(range(number)):
        raise _BadProof('missing endpoint labels')
    return blocks


def _reference_skeleton(g, vertex_proof, cover_proof, check):
    number = 2 * len(g['ports'])
    vertex_blocks = _partition(vertex_proof, number, {1, 2}, check)
    vertex_class = {label: i for i, block in enumerate(vertex_blocks) for label in block}
    cover_blocks = _partition(cover_proof, 2 * number, {2}, check)
    lifted_mate = {}
    for first, last in cover_blocks:
        lifted_mate[first] = last
        lifted_mate[last] = first
    matching = {}
    for endpoint in range(number):
        check()
        images = [lifted_mate[2 * endpoint + sheet] for sheet in (0, 1)]
        if images[0] // 2 != images[1] // 2 or images[0] % 2 == images[1] % 2:
            raise _BadProof('a gap does not have two interval lifts')
        target = images[0] // 2
        if target == endpoint:
            raise _BadProof('a gap has only one endpoint')
        matching[endpoint] = (target, bool(images[0] % 2))
    gaps, indices = [], {}
    for endpoint in range(number):
        target, twist = matching[endpoint]
        if endpoint < target:
            index = len(gaps)
            indices[endpoint] = indices[target] = index
            gaps.append(dict(id=index, ends=[endpoint, target],
                             old_boundary_present=vertex_class[endpoint] != vertex_class[target],
                             fibre_flip=twist))

    # The permutation "cross a port, cross its following gap" determines
    # each boundary orientation. The least port is read in its positive chart.
    successor = {i: matching[i ^ 1][0] for i in range(number)}
    unused, loops, attachments = set(range(number // 2)), [], []
    while unused:
        check()
        start = 2 * min(unused)
        endpoints, current = [], start
        while current not in endpoints:
            check()
            endpoints.append(current)
            current = successor[current]
        if current != start:
            raise _BadProof('a boundary word is not a circle')
        port_set = {endpoint // 2 for endpoint in endpoints}
        if len(port_set) != len(endpoints) or not port_set <= unused:
            raise _BadProof('a boundary word repeats a port')
        unused.difference_update(port_set)
        word = [(i // 2 + 1) * (-1 if i % 2 else 1) for i in endpoints]
        links = [indices[i ^ 1] for i in endpoints]
        parity = sum(gaps[i]['fibre_flip'] for i in links) % 2
        if parity:
            raise _BadProof('boundary-circle fibre orientation is inconsistent')
        loop_id = len(loops)
        all_core = not any(gaps[i]['old_boundary_present'] for i in links)
        loops.append(dict(id=loop_id, word=word, gaps=links, all_core=all_core,
                          fibre_flip=False))
        if all_core:
            attachments.append(dict(kind='circle', boundary_loop=loop_id, word=word.copy(),
                                    endpoint_tokens=[], fibre_flip=False,
                                    base_anchor_port=min(port_set)))
        else:
            for i in range(len(word)):
                if not gaps[links[i - 1]]['old_boundary_present']:
                    continue
                selected, parity, j = [i], False, i
                while not gaps[links[j]]['old_boundary_present']:
                    parity ^= gaps[links[j]]['fibre_flip']
                    j = (j + 1) % len(word)
                    selected.append(j)
                run = [word[k] for k in selected]
                attachments.append(dict(kind='interval', boundary_loop=loop_id, word=run,
                                        endpoint_tokens=[endpoints[i], endpoints[j] ^ 1],
                                        fibre_flip=parity,
                                        base_anchor_port=min(abs(k) for k in run) - 1))
    return dict(ports=[dict(p) for p in g['ports']], gaps=gaps, boundary_loops=loops,
                attachment_components=attachments,
                interval_attachments=sum(p['kind'] == 'interval' for p in attachments),
                circle_attachments=sum(p['kind'] == 'circle' for p in attachments))


def verify_parallelity_boundary_words(triangulation, coordinates, certificate, *,
                                       max_operations=None, check=lambda: None):
    """Verify source-bound signed boundary words and proper attachment intervals.

    The cap counts both supplied unweighted traces; malformed proofs return
    False. Invalid source geometry and cooperative callback exceptions propagate.
    """
    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('max_operations must be nonnegative or None')
    keys = {'schema', 'input_sha256', 'skeleton', 'vertex_partition', 'gap_cover'}
    if (type(certificate) is not dict or set(certificate) != keys
            or certificate['schema'] != 'parallelity-boundary-words-v1'):
        return False
    proofs = [certificate['vertex_partition'], certificate['gap_cover']]
    operations = 0
    for proof in proofs:
        if proof is None:
            continue
        if type(proof) is not dict or type(proof.get('orbit_proof')) is not dict:
            return False
        trace = proof['orbit_proof'].get('operations')
        if type(trace) is not list:
            return False
        operations += len(trace)
    if max_operations is not None and operations > max_operations:
        return False
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    if certificate['input_sha256'] != _fingerprint(triangulation, analysed, check):
        return False
    geometry = _reference_parallelity(prepared, analysed, check)
    if not geometry['ports']:
        if proofs != [None, None]:
            return False
        expected = _reference_skeleton(geometry, {'histogram': []}, {'histogram': []}, check)
        return certificate_equal(certificate['skeleton'], expected)
    if any(proof is None for proof in proofs):
        return False
    vp, vw, dp, dw = _reference_queries(geometry, check)
    if not verify_weighted_orbit_certificate(geometry['corner_points'], vp, vw, proofs[0],
                                             dimension=1, check=check):
        return False
    if not verify_weighted_orbit_certificate(2 * geometry['corner_points'], dp, dw, proofs[1],
                                             dimension=1, check=check):
        return False
    try:
        expected = _reference_skeleton(geometry, proofs[0], proofs[1], check)
    except _BadProof:
        return False
    return certificate_equal(certificate['skeleton'], expected)
