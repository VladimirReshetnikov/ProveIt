"""Certified cyclic order of finitely many marks on compressed normal curves.

An interval pairing is interpreted here as a *multigraph edge family*: for
each source point x there is one edge, with two distinct endpoint occurrences.
This retains loops and parallel edges that the underlying orbit relation
alone forgets.  The graph must have degree two everywhere.  No represented
point or normal arc is expanded.

Deleting the marked vertices and applying weighted AHT orbit counting to
the remainder identifies the paths between their incident half-edges.
This implements the established marked-circle ordering method, used for
normal boundary curves in Lackenby's efficient certification paper, §9.4.
It is an implementation advance, not a new orbit or topology theorem.

Marks are distinct points.  Their occurrence identifiers are their positions
in the supplied list, so arbitrary repeated application labels must be kept
separately by the caller.  Two different attachments at the same geometric
point require extra local ordering information; duplicate points are rejected.
"""

from bisect import bisect_left, bisect_right
from math import isqrt

from .integer_codec import encoded_integer
from .interval_orbits import IntervalPairing
from .weighted_orbits import weighted_orbit_histogram


def _integer(value, name, minimum=0):
    try:
        value = encoded_integer(value)
    except ValueError as exc:
        raise ValueError(f'{name} requires an integer or hexadecimal string') from exc
    if value < minimum:
        raise ValueError(f'{name} must be at least {minimum}')
    return value


def _source(size, pairings, marks, start_half_edge, poll):
    size = _integer(size, 'size')
    try:
        pairs = list(pairings)
    except TypeError as exc:
        raise ValueError('pairings must be an iterable of IntervalPairing values') from exc
    delta = {0: 0, size: 0}
    for pair in pairs:
        poll()
        if not isinstance(pair, IntervalPairing) or pair.d >= size:
            raise ValueError('pairings must be IntervalPairing values inside [0,size)')
        for lo, hi in ((pair.a, pair.b), (pair.c, pair.d)):
            delta[lo] = delta.get(lo, 0) + 1
            delta[hi + 1] = delta.get(hi + 1, 0) - 1
    degree, endpoints = 0, sorted(delta)
    for lo, hi in zip(endpoints, endpoints[1:]):
        poll()
        degree += delta[lo]
        if lo < hi and degree != 2:
            raise ValueError('the interval multigraph must have degree two everywhere')
    if not isinstance(marks, (list, tuple)):
        raise ValueError('marks must be an explicit list or tuple of distinct points')
    marks = [_integer(point, 'marked point') for point in marks]
    if len(set(marks)) != len(marks) or any(point >= size for point in marks):
        raise ValueError('marked points must be distinct and inside [0,size)')
    if start_half_edge is not None:
        if not isinstance(start_half_edge, (tuple, list)) or len(start_half_edge) != 3:
            raise ValueError('start_half_edge requires (pairing, source, side)')
        start_half_edge = [_integer(value, 'half-edge field') for value in start_half_edge]
        if start_half_edge[2] not in (0, 1):
            raise ValueError('half-edge side must be 0 or 1')
    return size, pairs, marks, start_half_edge, len(endpoints)


def _cut(size, pairs, marks, encoding, poll):
    """Delete incident edges at their source indices, then close marked gaps."""
    ordered = sorted(marks)
    mark_index = {point: index for index, point in enumerate(marks)}
    ports, forbidden = [], []
    for index, pair in enumerate(pairs):
        poll()
        removed = set()
        for point in ordered[bisect_left(ordered, pair.a):bisect_right(ordered, pair.b)]:
            ports.append(dict(mark=mark_index[point], pairing=index, source=point, side=0))
            removed.add(point)
        for point in ordered[bisect_left(ordered, pair.c):bisect_right(ordered, pair.d)]:
            source = (pair.a + pair.d - point if pair.reverse
                      else point - pair.c + pair.a)
            ports.append(dict(mark=mark_index[point], pairing=index, source=source, side=1))
            removed.add(source)
        forbidden.append(sorted(removed))
    ports.sort(key=lambda row: (row['mark'], row['pairing'], row['source'], row['side']))
    if len(ports) != 2 * len(marks):
        raise ArithmeticError('degree validation and marked incidences disagree')
    lookup = {(row['pairing'], row['source'], row['side']): i
              for i, row in enumerate(ports)}

    def compress(point):
        return point - bisect_left(ordered, point)

    residual = []
    for pair, removed in zip(pairs, forbidden):
        poll()
        left = pair.a
        for cut in removed + [pair.b + 1]:
            if left < cut:
                low, high = sorted((pair.image(left), pair.image(cut - 1)))
                residual.append(IntervalPairing(compress(left), compress(cut - 1),
                                                compress(low), compress(high), pair.reverse))
            left = cut + 1
    dimension = 4 if encoding == 'moments' else len(ports) + 1
    residual_size = size - len(marks)
    weights = []
    if residual_size:
        weights.append((0, residual_size, [0] * (dimension - 1) + [1]))
    direct = []
    for index, port in enumerate(ports):
        poll()
        pair, source = pairs[port['pairing']], port['source']
        neighbour = pair.image(source) if port['side'] == 0 else source
        if neighbour in mark_index:
            if port['side'] == 0:
                other = lookup[(port['pairing'], source, 1)]
                direct.append(dict(ports=sorted((index, other)), unmarked_vertices=0))
        else:
            if encoding == 'moments':
                label = index + 1
                value = [1, label, label * label, 0]
            else:
                value = [0] * dimension
                value[index] = 1
            point = compress(neighbour)
            weights.append((point, point + 1, value))
    return ports, residual_size, residual, weights, direct


def _solution(marks, ports, direct, histogram, start_half_edge, encoding, poll):
    connections, unmarked = list(direct), []
    for record in histogram:
        poll()
        vector, multiplicity = record['weight'], record['orbits']
        length = vector[-1]
        if encoding == 'moments':
            count, total, squares = vector[:3]
            if count == 0 and total == 0 and squares == 0:
                support = []
            elif count == 2:
                discriminant = 2 * squares - total * total
                root = isqrt(discriminant) if discriminant >= 0 else -1
                if root <= 0 or root * root != discriminant or (total - root) % 2:
                    raise ArithmeticError('endpoint moments do not encode two distinct labels')
                lower, upper = (total - root) // 2, (total + root) // 2
                if not 1 <= lower < upper <= len(ports):
                    raise ArithmeticError('decoded endpoint label is out of range')
                support = [lower - 1, upper - 1]
            else:
                raise ArithmeticError('residual endpoint count is not zero or two')
        else:
            endpoint_weights = vector[:-1]
            support = [index for index, value in enumerate(endpoint_weights) if value]
            if any(value != 1 for value in endpoint_weights if value):
                raise ArithmeticError('an endpoint basis label occurred more than once')
        if length < 1:
            raise ArithmeticError('a residual component must contain a vertex')
        if not support:
            unmarked.append(dict(vertices=length, components=multiplicity))
        elif len(support) == 2 and multiplicity == 1:
            connections.append(dict(ports=support, unmarked_vertices=length))
        else:
            raise ArithmeticError('a residual component is not an unmarked cycle or path')
    connections.sort(key=lambda row: tuple(row['ports']))
    unmarked.sort(key=lambda row: row['vertices'])
    across, lengths = {}, {}
    for row in connections:
        a, b = row['ports']
        if a == b or a in across or b in across:
            raise ArithmeticError('each marked half-edge must belong to exactly one gap')
        across[a], across[b] = b, a
        lengths[a] = lengths[b] = row['unmarked_vertices']
    if len(across) != len(ports):
        raise ArithmeticError('a marked half-edge was lost')
    at_mark = [[] for _ in marks]
    for index, port in enumerate(ports):
        at_mark[port['mark']].append(index)
    if any(len(pair) != 2 for pair in at_mark):
        raise ArithmeticError('each mark must have two distinct half-edges')
    twin = {a: b for pair in at_mark for a, b in (pair, pair[::-1])}

    def walk(start):
        order, outgoing, gaps = [], [], []
        current = start
        while True:
            poll()
            order.append(ports[current]['mark'])
            outgoing.append(current)
            gaps.append(lengths[current])
            current = twin[across[current]]
            if current == start:
                break
            if len(order) > len(marks):
                raise ArithmeticError('marked quotient traversal did not close')
        return dict(marks=order, departures=outgoing, gaps=gaps,
                    vertices=len(order) + sum(gaps))

    selected = None
    if start_half_edge is not None:
        candidates = [index for index, port in enumerate(ports)
                      if [port['pairing'], port['source'], port['side']] == start_half_edge]
        if len(candidates) != 1:
            raise ValueError('start_half_edge must be incident to a marked point')
        selected = candidates[0]
    cycles, seen = [], set()
    for mark in range(len(marks)):
        poll()
        if mark in seen:
            continue
        choices = [walk(port) for port in at_mark[mark]]
        cycle = min(choices, key=lambda row: (row['marks'], row['departures']))
        if selected is not None and ports[selected]['mark'] in cycle['marks']:
            cycle = walk(selected)
        seen.update(cycle['marks'])
        cycles.append(cycle)
    cycles.sort(key=lambda row: min(row['marks']))
    return dict(ports=ports, connections=connections, cycles=cycles,
                unmarked_cycles=unmarked,
                component_count=len(cycles) + sum(row['components'] for row in unmarked))


def marked_boundary_order(size, pairings, marks, *, start_half_edge=None,
                          weight_encoding='moments',
                          max_cycles=None, periodic_rule='fine_wilf', check=None,
                          record_certificate=False):
    """Find exact marked cyclic orders and intervening arc lengths in binary size.

    ``marks[i]`` is occurrence i; points must be distinct.  A half-edge is
    ``(pairing_index, original_domain_point, endpoint_side)``.  Side 0 is its
    source endpoint and side 1 its range endpoint, including for a self-loop.
    Output port indices are the order of these descriptors sorted first by
    mark occurrence.  Their identity is bound to the *ordered* pairing input.

    By default each cycle starts at its smallest occurrence index and chooses
    the lexicographically smaller of its two directions.  Ties (one or two
    marks) are resolved by its outgoing port word.  ``start_half_edge`` fixes
    start and direction on its own cycle.  Other cycles remain canonical.

    ``gaps[i]`` counts unmarked vertices following occurrence i; the number
    of original graph edges in that gap is one more.  Unmarked cycles are
    retained by exact length and multiplicity.  INCONCLUSIVE has no order
    or certificate.  Cooperative cancellation exceptions propagate.

    Default ``weight_encoding='moments'`` uses four coordinates: endpoint
    count, sum of labels, sum of squared labels, and vertex count.  The raw
    degree-two guard proves that a residual component has zero or two ports,
    making the two labels recoverable by exact quadratic roots.  This is a
    lossless signature only under that guard.  ``'one_hot'`` retains the
    reference encoding with 2*len(marks)+1 coordinates for controlled audits.
    """
    poll = check if check is not None else lambda: None
    poll()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if weight_encoding not in ('moments', 'one_hot'):
        raise ValueError("weight_encoding must be 'moments' or 'one_hot'")
    size, pairs, marks, start, endpoints = _source(size, pairings, marks, start_half_edge, poll)
    ports, residual_size, residual, weights, direct = _cut(size, pairs, marks, weight_encoding, poll)
    if start is not None and not any(
            [row['pairing'], row['source'], row['side']] == start for row in ports):
        raise ValueError('start_half_edge must be incident to a marked point')
    dimension = 4 if weight_encoding == 'moments' else len(ports) + 1
    counted = weighted_orbit_histogram(
        residual_size, residual, weights, dimension=dimension, max_cycles=max_cycles,
        periodic_rule=periodic_rule, check=poll, record_certificate=record_certificate)
    stats = dict(source_pairings=len(pairs), source_point_bits=size.bit_length(),
                 degree_endpoints=endpoints, marked_vertices=len(marks), ports=len(ports),
                 residual_pairings=len(residual), weight_intervals=len(weights),
                 weight_dimension=dimension, weight_encoding=weight_encoding,
                 weighted_stats=counted['stats'])
    if counted['status'] != 'COMPLETE':
        return dict(status='INCONCLUSIVE', stats=stats)
    solution = _solution(marks, ports, direct, counted['histogram'], start, weight_encoding, poll)
    answer = dict(status='COMPLETE', **solution, stats=stats)
    if record_certificate:
        answer['certificate'] = dict(
            schema='marked-boundary-order-v1', size=size,
            pairings=[[p.a, p.b, p.c, p.d, -1 if p.reverse else 1] for p in pairs],
            marks=marks, start_half_edge=start, weight_encoding=weight_encoding,
            weighted_proof=counted['certificate'],
            solution=solution)
    poll()
    return answer


def normal_marked_boundary_order(triangulation, coordinates, marks, **options):
    """Reconstruct native normal boundary arcs, then order the supplied marks.

    Point indices are exactly those returned by
    ``normal_surface_geometry.normal_arc_pairings(..., boundary=True)``.
    Its full supported manifold/coordinate validation is retained.
    """
    from .normal_surface_geometry import normal_arc_pairings
    poll = options.get('check') or (lambda: None)
    size, pairings = normal_arc_pairings(triangulation, coordinates, boundary=True, check=poll)
    return marked_boundary_order(size, pairings, marks, **options)
