"""Independent replay of marked-order certificates on degree-two boundaries.

This verifier does not import or call the marked-order producer.  It rebuilds
the marked cut by a separate endpoint partition, verifies the existing
weighted AHT certificate, and reconstructs the finite marked quotient.
Only source/trace bit lengths and the explicit number of marks govern work.
"""

from bisect import bisect_left
from math import isqrt

from .integer_codec import certificate_equal, encoded_integer
from .interval_orbits import IntervalPairing
from .weighted_orbit_verify import verify_weighted_orbit_certificate


class _InvalidBoundaryProof(ValueError):
    pass


def _integer(value):
    try:
        return encoded_integer(value)
    except ValueError as exc:
        raise _InvalidBoundaryProof('expected exact integer') from exc


def _inputs(size, pairings, marks, direction, poll):
    size = _integer(size)
    if size < 0 or not isinstance(marks, (list, tuple)):
        raise _InvalidBoundaryProof('invalid size or marks container')
    try:
        pairs = list(pairings)
    except TypeError as exc:
        raise _InvalidBoundaryProof('pairings must be iterable') from exc
    spans = []
    for pair in pairs:
        poll()
        if not isinstance(pair, IntervalPairing) or pair.d >= size:
            raise _InvalidBoundaryProof('invalid interval pairing')
        spans.extend(((pair.a, pair.b + 1), (pair.c, pair.d + 1)))
    # Different from the producer's difference-map integration: sweep signed
    # endpoint tokens, checking coverage before processing each endpoint group.
    tokens = sorted([(left, 1) for left, _ in spans]
                    + [(right, -1) for _, right in spans] + [(size, 0)])
    position, coverage, cursor = 0, 0, 0
    while cursor < len(tokens):
        poll()
        endpoint = tokens[cursor][0]
        if position < endpoint and coverage != 2:
            raise _InvalidBoundaryProof('source multigraph does not have degree two')
        while cursor < len(tokens) and tokens[cursor][0] == endpoint:
            coverage += tokens[cursor][1]
            cursor += 1
        position = endpoint
    if position != size or coverage:
        raise _InvalidBoundaryProof('source endpoint sweep did not close')
    marks = [_integer(value) for value in marks]
    if len(set(marks)) != len(marks) or any(not 0 <= value < size for value in marks):
        raise _InvalidBoundaryProof('invalid marked vertices')
    if direction is not None:
        if not isinstance(direction, (list, tuple)) or len(direction) != 3:
            raise _InvalidBoundaryProof('invalid selected half-edge')
        direction = [_integer(value) for value in direction]
        if min(direction) < 0 or direction[2] not in (0, 1):
            raise _InvalidBoundaryProof('invalid selected half-edge')
    return size, pairs, marks, direction


def _rebuild(size, pairs, marks, encoding, poll):
    """Partition by marks and their inverse images; retain unmarked cells."""
    ordered = sorted(marks)
    marked = set(marks)
    occurrences, survivors = [], []
    for index, pair in enumerate(pairs):
        poll()
        sign = -1 if pair.reverse else 1
        shift = pair.a + pair.d if pair.reverse else pair.c - pair.a
        breaks = {pair.a, pair.b + 1}
        for occurrence, point in enumerate(marks):
            poll()
            if pair.a <= point <= pair.b:
                occurrences.append((occurrence, index, point, 0))
                breaks.update((point, point + 1))
            inverse = sign * (point - shift)
            if pair.a <= inverse <= pair.b:
                occurrences.append((occurrence, index, inverse, 1))
                breaks.update((inverse, inverse + 1))
        endpoints = sorted(breaks)
        for left, right in zip(endpoints, endpoints[1:]):
            poll()
            image = sign * left + shift
            if left in marked or image in marked:
                if right - left != 1:
                    raise _InvalidBoundaryProof('a deleted cell was not a singleton')
                continue
            a = left - bisect_left(ordered, left)
            b = right - 1 - bisect_left(ordered, right - 1)
            low, high = sorted((image, sign * (right - 1) + shift))
            c = low - bisect_left(ordered, low)
            d = high - bisect_left(ordered, high)
            if b - a != d - c:
                raise _InvalidBoundaryProof('rank compression altered a pairing width')
            survivors.append(IntervalPairing(a, b, c, d, pair.reverse))
    occurrences.sort()
    if len(occurrences) != 2 * len(marks):
        raise _InvalidBoundaryProof('incorrect number of endpoint occurrences')
    ports = [dict(zip(('mark', 'pairing', 'source', 'side'), row)) for row in occurrences]
    edge_ends, weights = {}, []
    smaller = size - len(marks)
    dimension = 4 if encoding == 'moments' else len(ports) + 1
    if smaller:
        weights.append((0, smaller, [0] * (dimension - 1) + [1]))
    for port, (_, row, source, side) in enumerate(occurrences):
        poll()
        pair = pairs[row]
        target = pair.a + pair.d - source if pair.reverse else source + pair.c - pair.a
        neighbour = target if side == 0 else source
        if neighbour in marked:
            edge_ends.setdefault((row, source), []).append(port)
        else:
            point = neighbour - bisect_left(ordered, neighbour)
            if encoding == 'moments':
                number = port + 1
                vector = [1, number, number ** 2, 0]
            else:
                vector = [0] * dimension
                vector[port] = 1
            weights.append((point, point + 1, vector))
    direct = []
    for edge, ends in edge_ends.items():
        poll()
        if len(ends) != 2:
            raise _InvalidBoundaryProof('direct marked edge lost one endpoint occurrence')
        direct.append((tuple(sorted(ends)), 0))
    return ports, smaller, survivors, weights, direct


def _recover(marks, ports, direct, histogram, direction, encoding, poll):
    gaps, closed = dict(direct), {}
    for record in histogram:
        poll()
        value = [_integer(entry) for entry in record['weight']]
        count = _integer(record['orbits'])
        length = value.pop()
        if encoding == 'moments':
            endpoints, total, square_sum = value
            if endpoints == 0:
                if total or square_sum:
                    raise _InvalidBoundaryProof('unmarked component carries a port moment')
                active = ()
            elif endpoints == 2:
                squared_difference = 2 * square_sum - total ** 2
                if squared_difference < 0:
                    raise _InvalidBoundaryProof('negative endpoint squared difference')
                lower = (total - isqrt(squared_difference)) // 2
                upper = total - lower
                if (not 1 <= lower < upper <= len(ports)
                        or lower * lower + upper * upper != square_sum):
                    raise _InvalidBoundaryProof('moments do not determine two valid distinct ports')
                active = (lower - 1, upper - 1)
            else:
                raise _InvalidBoundaryProof('residual component has other than zero or two ports')
        else:
            active = tuple(index for index, weight in enumerate(value) if weight)
            if any(value[index] != 1 for index in active):
                raise _InvalidBoundaryProof('a basis port weight is not one')
        if length <= 0:
            raise _InvalidBoundaryProof('residual component has no vertices')
        if not active:
            if length in closed:
                raise _InvalidBoundaryProof('duplicate unmarked length class')
            closed[length] = count
        else:
            if len(active) != 2 or count != 1 or active in gaps:
                raise _InvalidBoundaryProof('residual component does not certify a unique path')
            gaps[active] = length
    connection, length_at = {}, {}
    for (left, right), length in gaps.items():
        if left == right or left in connection or right in connection:
            raise _InvalidBoundaryProof('marked gap incidence is not an involution')
        connection[left], connection[right] = right, left
        length_at[left] = length_at[right] = length
    if sorted(connection) != list(range(len(ports))):
        raise _InvalidBoundaryProof('missing marked half-edge')
    incidences = {}
    for index, port in enumerate(ports):
        incidences.setdefault(port['mark'], []).append(index)
    if sorted(incidences) != list(range(len(marks))):
        raise _InvalidBoundaryProof('missing marked occurrence')
    if any(len(value) != 2 for value in incidences.values()):
        raise _InvalidBoundaryProof('wrong marked vertex degree')

    def circuit(initial):
        departure, order, arc_lengths, visited = initial, [], [], set()
        outgoing = []
        while True:
            poll()
            occurrence = ports[departure]['mark']
            if occurrence in visited:
                raise _InvalidBoundaryProof('a circuit revisited a marked occurrence early')
            visited.add(occurrence)
            order.append(occurrence)
            outgoing.append(departure)
            arc_lengths.append(length_at[departure])
            arrival = connection[departure]
            alternatives = incidences[ports[arrival]['mark']]
            departure = alternatives[0] if alternatives[1] == arrival else alternatives[1]
            if departure == initial:
                break
        return dict(marks=order, departures=outgoing, gaps=arc_lengths,
                    vertices=len(order) + sum(arc_lengths))

    directed_port = None
    if direction is not None:
        for index, port in enumerate(ports):
            if direction == [port['pairing'], port['source'], port['side']]:
                directed_port = index
        if directed_port is None:
            raise _InvalidBoundaryProof('selected half-edge is not a marked incidence')
    remaining, cycles = set(range(len(marks))), []
    while remaining:
        poll()
        first = min(remaining)
        left, right = (circuit(port) for port in incidences[first])
        left_key, right_key = (left['marks'], left['departures']), (right['marks'], right['departures'])
        chosen = left if left_key <= right_key else right
        if directed_port is not None and ports[directed_port]['mark'] in chosen['marks']:
            chosen = circuit(directed_port)
        remaining.difference_update(chosen['marks'])
        cycles.append(chosen)
    cycles.sort(key=lambda row: min(row['marks']))
    connections = [dict(ports=list(ends), unmarked_vertices=length)
                   for ends, length in sorted(gaps.items())]
    unmarked = [dict(vertices=length, components=count) for length, count in sorted(closed.items())]
    return dict(ports=ports, connections=connections, cycles=cycles, unmarked_cycles=unmarked,
                component_count=len(cycles) + sum(closed.values()))


def verify_marked_boundary_certificate(size, pairings, marks, certificate, *,
                                       start_half_edge=None, weight_encoding='moments', check=None):
    """Replay a source-bound cyclic-order proof without calling its producer.

    Malformed proofs return False.  Cooperative callback exceptions propagate.
    Hexadecimal integer transport is accepted in every integer certificate field.
    The complete supplied AHT trace and all weight transports are checked before
    using the residual histogram to infer any path, circle, or cyclic order.
    """
    poll = check if check is not None else lambda: None
    try:
        poll()
        if weight_encoding not in ('moments', 'one_hot'):
            return False
        size, pairs, marks, direction = _inputs(size, pairings, marks, start_half_edge, poll)
        expected = {'schema', 'size', 'pairings', 'marks', 'start_half_edge',
                    'weight_encoding', 'weighted_proof', 'solution'}
        if not isinstance(certificate, dict) or set(certificate) != expected:
            return False
        if certificate['schema'] != 'marked-boundary-order-v1':
            return False
        source = dict(size=size, pairings=[
            [pair.a, pair.b, pair.c, pair.d, -1 if pair.reverse else 1] for pair in pairs],
            marks=marks, start_half_edge=direction, weight_encoding=weight_encoding)
        if not all(certificate_equal(certificate[key], value) for key, value in source.items()):
            return False
        ports, smaller, survivors, weights, direct = _rebuild(size, pairs, marks, weight_encoding, poll)
        proof = certificate['weighted_proof']
        if not verify_weighted_orbit_certificate(
                smaller, survivors, weights, proof,
                dimension=4 if weight_encoding == 'moments' else len(ports) + 1, check=poll):
            return False
        solution = _recover(marks, ports, direct, proof['histogram'], direction, weight_encoding, poll)
        poll()
        return certificate_equal(certificate['solution'], solution)
    except _InvalidBoundaryProof:
        return False


def verify_normal_marked_boundary_certificate(triangulation, coordinates, marks,
                                              certificate, **options):
    """Rebuild a validated native normal boundary before independent replay."""
    from .normal_surface_geometry import NormalOrbitError, normal_arc_pairings
    poll = options.get('check') or (lambda: None)
    callback_error = None

    def geometry_poll():
        nonlocal callback_error
        try:
            poll()
        except NormalOrbitError as exc:
            # This exception type also denotes malformed native geometry.
            # Preserve an external callback's exception by exact identity.
            callback_error = exc
            raise

    try:
        size, pairings = normal_arc_pairings(triangulation, coordinates,
                                            boundary=True, check=geometry_poll)
    except NormalOrbitError as exc:
        if exc is callback_error:
            raise
        return False
    return verify_marked_boundary_certificate(size, pairings, marks, certificate, **options)
