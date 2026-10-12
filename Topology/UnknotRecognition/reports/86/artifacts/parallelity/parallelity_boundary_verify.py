"""Independent query reconstruction and replay for ordered bundle interfaces.

Source geometry is an authenticated input, obtained using the maintained
``verify_normal_cut_parallelity``.  This checker never invokes the interface
producer, its query constructor, its mask decoder, or its cyclic traversal.
"""

from hashlib import sha256
import json

from fastunknot.integer_codec import certificate_equal, encoded_integer, json_safe
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate


def _reference_queries(geometry, check):
    size = geometry['corner_points']
    polygons = geometry['polygons']
    vertex, old, signed = [], [], []
    for link in geometry['gluings']:
        check()
        low, high = link['rank_start'], link['rank_stop']-1
        p, q = polygons[link['left']], polygons[link['right']]
        for endpoint in (0, 1):
            target_end = 1-endpoint if link['ends_reverse'] else endpoint
            i = (link['left_edge']+endpoint) % len(p['vertices'])
            j = (link['right_edge']+target_end) % len(q['vertices'])
            a, b = link['left_map']
            c, d = link['right_map']
            left = [a*r+b-p['start']+p['corner_starts'][i] for r in (low, high)]
            right = [c*r+d-q['start']+q['corner_starts'][j] for r in (low, high)]
            left.sort()
            right.sort()
            reverse = a != c
            vertex.append(IntervalPairing(*left, *right, reverse))
            for sheet in (0, 1):
                target = 1-sheet if link['fibre_flip'] else sheet
                signed.append(IntervalPairing(
                    *(x+sheet*size for x in left),
                    *(x+target*size for x in right), reverse))
    for edge in geometry['free_edges']:
        check()
        if not edge['original_boundary']:
            continue
        polygon = polygons[edge['polygon']]
        lo, hi = edge['rank_start']-1, edge['rank_stop']-2
        a = polygon['corner_starts'][edge['edge']]
        b = polygon['corner_starts'][(edge['edge']+1) % len(polygon['vertices'])]
        old.append(IntervalPairing(a+lo, a+hi, b+lo, b+hi))
        for sheet in (0, 1):
            signed.append(IntervalPairing(a+lo+sheet*size, a+hi+sheet*size,
                                          b+lo+sheet*size, b+hi+sheet*size))
    weights, lifted = [], []
    for port in geometry['ports']:
        check()
        p = polygons[port['polygon']]
        for end in (0, 1):
            label = 2*port['id']+end
            point = p['corner_starts'][(port['edge']+end)
                                      % len(p['vertices'])]+port['rank']-1
            weights.append((point, point+1, [2**label]))
            for sheet in (0, 1):
                address = point+sheet*size
                lifted.append((address, address+1, [2**(2*label+sheet)]))
    return [('vertices', size, vertex, weights),
            ('gaps', size, vertex+old, weights),
            ('fibre_gaps', 2*size, signed, lifted)]


def _partition(proof, total_labels, pairs):
    available = set(range(total_labels))
    answer = []
    for row in proof['histogram']:
        if len(row['weight']) != 1:
            raise ValueError('incorrect weight dimension')
        mask = encoded_integer(row['weight'][0])
        if mask == 0:
            continue
        if mask < 0 or mask.bit_length() > total_labels:
            raise ValueError('invalid endpoint mask')
        group = [label for label in range(total_labels) if mask & 2**label]
        if encoded_integer(row['orbits']) != 1:
            raise ValueError('endpoint mask repeats')
        if len(group) not in ((2,) if pairs else (1, 2)):
            raise ValueError('invalid number of boundary endpoints')
        if not set(group) <= available:
            raise ValueError('endpoint appears twice')
        available.difference_update(group)
        answer.append(group)
    if available:
        raise ValueError('missing endpoint')
    return sorted(answer)


def _reference_interface(count, vertices, pairs, lifts, check):
    vertex_number = {v: index for index, row in enumerate(vertices) for v in row}
    continuation = {a: b for x, y in pairs for a, b in ((x, y), (y, x))}
    lifted = {a: b for x, y in lifts for a, b in ((x, y), (y, x))}
    twists = {}
    for x in range(2*count):
        check()
        target = lifted[2*x]
        if target//2 != continuation[x]:
            return None
        twist = target % 2
        if lifted[2*x+1] != 2*continuation[x]+1-twist:
            return None
        twists[x] = bool(twist)
    gap_records = [dict(ends=[a, b], zero_length=vertex_number[a] == vertex_number[b],
                        fibre_flip=twists[a]) for a, b in pairs]
    unused = set(range(count))
    circles = []
    while unused:
        start = current = 2*min(unused)
        path, open_gaps, parity = [], 0, False
        while True:
            check()
            port, incoming = divmod(current, 2)
            if port not in unused:
                return None
            unused.remove(port)
            outgoing = 2*port+1-incoming
            following = continuation[outgoing]
            zero = vertex_number[outgoing] == vertex_number[following]
            open_gaps += not zero
            parity ^= twists[outgoing]
            path.append(dict(port=port, entry_end=incoming,
                             next_port=following//2, next_entry_end=following % 2,
                             gap_zero_length=zero, gap_fibre_flip=twists[outgoing]))
            current = following
            if current == start:
                break
        if parity:
            return None
        circles.append(dict(ports=path, full_core_circle=open_gaps == 0,
                            core_interval_components=open_gaps, fibre_holonomy=False))
    chi = len(vertices)-count
    if chi != sum(circle['core_interval_components'] for circle in circles):
        return None
    return dict(port_count=count, endpoint_vertices=vertices, gaps=gap_records,
                boundary_cycles=circles, marked_boundary_components=len(circles),
                core_attachment_vertices=len(vertices),
                attachment_euler_characteristic=chi, fibre_transport_checked=True)


def verify_parallelity_boundary_interface(geometry, certificate, *,
                                          max_operations=None, check=lambda: None):
    """Replay the interface certificate over authenticated source geometry.

    This operation authenticates new cyclic/gap/fibre data only.  The geometry
    must separately pass the maintained source-parallelity verifier.  The
    operation cap covers all three supplied orbit traces.  Callback exceptions
    propagate, and exhausted caps return False.
    """
    check()
    if max_operations is not None and (type(max_operations) is not int
                                       or max_operations < 0):
        raise ValueError('max_operations must be nonnegative or None')
    expected_keys = {'schema', 'geometry_sha256', 'interface', 'orbit_proofs'}
    if type(certificate) is not dict or set(certificate) != expected_keys:
        return False
    if certificate['schema'] != 'source-parallelity-boundary-v1':
        return False
    payload = json.dumps(json_safe(geometry), sort_keys=True,
                         separators=(',', ':')).encode('utf-8')
    if certificate['geometry_sha256'] != sha256(payload).hexdigest():
        return False
    count = len(geometry['ports'])
    proofs = certificate['orbit_proofs']
    fields = {'vertices', 'gaps', 'fibre_gaps'} if count else set()
    if type(proofs) is not dict or set(proofs) != fields:
        return False
    operations = 0
    for proof in proofs.values():
        if type(proof) is not dict or type(proof.get('orbit_proof')) is not dict:
            return False
        trace = proof['orbit_proof'].get('operations')
        if type(trace) is not list:
            return False
        operations += len(trace)
    if max_operations is not None and operations > max_operations:
        return False
    if count:
        for name, universe, pairings, weights in _reference_queries(geometry, check):
            if not verify_weighted_orbit_certificate(
                    universe, pairings, weights, proofs[name], dimension=1, check=check):
                return False
        try:
            vertices = _partition(proofs['vertices'], 2*count, False)
            pairs = _partition(proofs['gaps'], 2*count, True)
            lifts = _partition(proofs['fibre_gaps'], 4*count, True)
        except (KeyError, TypeError, ValueError, IndexError):
            return False
    else:
        vertices, pairs, lifts = [], [], []
    expected = _reference_interface(count, vertices, pairs, lifts, check)
    return expected is not None and certificate_equal(certificate['interface'], expected)
