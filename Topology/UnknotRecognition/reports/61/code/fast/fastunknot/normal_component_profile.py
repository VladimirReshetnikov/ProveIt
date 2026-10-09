"""Compressed component weights and disk detection for supplied normal surfaces.

Five additive integer coordinates recover Euler characteristic, normal disk
count, boundary vertex count and intersections with two mod-two boundary
cycles.  The weighted AHT kernel never expands an edge point or a component.
The supported triangulations are the same compact orientable manifolds with
one torus boundary as normal_surface_geometry.  No PD/exterior provenance is
asserted here; this is a supplied-normal-surface query, not an unknot solver.
"""

from collections import deque

from .normal_surface_geometry import (
    _prepare, _coordinates, _arc_system, _edge, _quad, _EDGES, _fingerprint,
)


WEIGHT_DIMENSION = 5
WEIGHT_FIELDS = ('euler_characteristic', 'normal_disks', 'boundary_vertices',
                 'cycle_0_intersections', 'cycle_1_intersections')


def boundary_cycle_basis(prepared, *, check=lambda: None):
    """Choose two graph cycles forming H_1(boundary; F_2).

Triangle boundary vectors are inserted first into a binary linear basis.
Fundamental cycles of a spanning tree then extend that basis by exactly two
vectors.  Loops, multiple edges and repeated face edges are retained.
The output cycles are original graph cycles, not just reduced vectors.
"""
    edges = sorted(prepared['boundary_incidence'])
    position = {edge: i for i, edge in enumerate(edges)}
    span = {}

    def insert(vector):
        while vector:
            check()
            pivot = vector.bit_length() - 1
            if pivot in span:
                vector ^= span[pivot]
            else:
                span[pivot] = vector
                return True
        return False

    for t, f in prepared['boundary_faces']:
        check()
        vertices = [v for v in range(4) if v != f]
        vector = 0
        for a, b in _EDGES:
            if a in vertices and b in vertices:
                edge = prepared['edge_roots'][_edge(t, a, b)]
                vector ^= 1 << position[edge]
        insert(vector)

    graph = {}
    for i, edge in enumerate(edges):
        check()
        u, v = prepared['endpoints'][edge]
        graph.setdefault(u, []).append((v, i))
        graph.setdefault(v, []).append((u, i))
    paths, tree = {}, set()
    for start in sorted(graph):
        if start in paths:
            continue
        paths[start] = 0
        todo = deque([start])
        while todo:
            check()
            u = todo.popleft()
            for v, i in graph[u]:
                if v not in paths:
                    paths[v] = paths[u] ^ (1 << i)
                    tree.add(i)
                    todo.append(v)
    cycles = []
    for i, edge in enumerate(edges):
        check()
        if i in tree:
            continue
        u, v = prepared['endpoints'][edge]
        vector = paths[u] ^ paths[v] ^ (1 << i)
        if insert(vector):
            cycles.append(vector)
    if len(cycles) != 2:
        raise ArithmeticError('validated torus boundary did not have mod-two rank two')
    return tuple(edges), tuple(cycles)


def component_weight_system(prepared, analysed, *, check=lambda: None):
    """Return a five-coordinate, O(tetrahedra)-run weight field.

Euler weights count each normal vertex, geometric arc and polygon exactly
once.  Arc weights are attached to the original geometric pairing list,
before identity deletion or any scheduler normalization.
"""
    size, pairs = _arc_system(prepared, analysed, check=check)
    edges, cycles = boundary_cycle_basis(prepared, check=check)
    boundary_position = {edge: i for i, edge in enumerate(edges)}
    offsets, cursor = {}, 0
    for edge in sorted(analysed['weights']):
        check()
        offsets[edge] = cursor
        cursor += analysed['weights'][edge]
    if cursor != size:
        raise ArithmeticError('normal edge universe disagrees with arc geometry')
    events = {}

    def add(start, stop, vector):
        check()
        if not 0 <= start <= stop <= size:
            raise ArithmeticError('component weight interval is outside its universe')
        if start == stop:
            return
        left = events.setdefault(start, [0] * WEIGHT_DIMENSION)
        right = events.setdefault(stop, [0] * WEIGHT_DIMENSION)
        for j, value in enumerate(vector):
            left[j] += value
            right[j] -= value

    add(0, size, (1, 0, 0, 0, 0))
    for pair in pairs:
        # Every original pairing encodes one distinct family of geometric arcs.
        add(pair.a, pair.b + 1, (-1, 0, 0, 0, 0))
    for edge in edges:
        check()
        bit = 1 << boundary_position[edge]
        start = offsets[edge]
        stop = start + analysed['weights'][edge]
        add(start, stop, (0, 0, 1, int(bool(cycles[0] & bit)),
                         int(bool(cycles[1] & bit))))

    def local_interval(t, a, b, start, count):
        """Locate a run measured from local vertex a towards b."""
        local = _edge(t, a, b)
        edge = prepared['edge_roots'][local]
        width = analysed['weights'][edge]
        backwards = prepared['edge_orientations'][local] ^ int(a > b)
        first = width - start - count if backwards else start
        return offsets[edge] + first, offsets[edge] + first + count

    for t, row in enumerate(analysed['rows']):
        check()
        for v in range(4):
            if row[v]:
                u = next(u for u in range(4) if u != v)
                start, stop = local_interval(t, v, u, 0, row[v])
                add(start, stop, (1, 1, 0, 0, 0))
        for q in range(3):
            count = row[4 + q]
            if count:
                a, b = next((a, b) for a, b in _EDGES if _quad(a, b) != q)
                start, stop = local_interval(t, a, b, row[a], count)
                add(start, stop, (1, 1, 0, 0, 0))

    runs, vector, last = [], [0] * WEIGHT_DIMENSION, 0
    for point in sorted(events):
        check()
        if point > last:
            value = tuple(vector)
            if runs and runs[-1][2] == value:
                runs[-1] = (runs[-1][0], point, value)
            else:
                runs.append((last, point, value))
        for j, change in enumerate(events[point]):
            vector[j] += change
        last = point
    if last != size or any(vector):
        if size:
            raise ArithmeticError('component weights do not cover the universe')
    # Global cellular totals provide a cheap invariant of the construction.
    totals = tuple(sum((stop - start) * value[j] for start, stop, value in runs)
                   for j in range(WEIGHT_DIMENSION))
    if totals[:2] != (analysed['euler_characteristic'], analysed['normal_disks']):
        raise ArithmeticError('component weights violate global cellular totals')
    cycle_edges = [[edge for i, edge in enumerate(edges) if cycle & (1 << i)]
                   for cycle in cycles]
    return size, pairs, tuple(runs), cycle_edges


def _profile_summary(profiles):
    groups = []
    components = disks = compressing = 0
    for multiplicity, vector in profiles:
        chi, pieces, boundary, x, y = vector
        if min(pieces, boundary, x, y) < 0 or pieces == 0:
            raise ArithmeticError('invalid component cellular counts')
        is_disk = chi == 1 and boundary > 0
        essential = is_disk and bool((x | y) & 1)
        group = dict(zip(WEIGHT_FIELDS, vector))
        group.update(multiplicity=multiplicity, is_disk=is_disk,
                     is_compressing_disk=essential,
                     boundary_class_mod2=[x & 1, y & 1])
        groups.append(group)
        components += multiplicity
        disks += multiplicity * is_disk
        compressing += multiplicity * essential
    return dict(components=components, disk_components=disks,
                compressing_disk_components=compressing,
                has_compressing_disk_component=bool(compressing), groups=groups)


def normal_component_profile(triangulation, coordinates, *, max_cycles=None,
                             periodic_rule='fine_wilf', check=lambda: None,
                             record_certificate=False):
    """Classify disk components of the supplied, possibly disconnected surface.

    Positive/negative answers refer only to components of this normal vector.
    A negative answer does not prove the boundary incompressible.  There is no
    claim that the supplied triangulation is the exterior of a particular PD.
    ``max_cycles`` limits the orbit producer; replay and geometry cooperate
    with ``check``.  No unfinished profile or disk verdict is returned.
    """
    from .weighted_orbits import weighted_orbit_profile
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    size, pairs, runs, cycles = component_weight_system(prepared, analysed, check=check)
    weighted = weighted_orbit_profile(
        size, pairs, runs, max_cycles=max_cycles, periodic_rule=periodic_rule,
        check=check, record_certificate=record_certificate, dimension=WEIGHT_DIMENSION)
    result = dict(status='COMPLETE' if weighted.complete else 'INCONCLUSIVE',
                  points=size, pairings=len(pairs), initial_weight_runs=len(runs),
                  weight_dimension=WEIGHT_DIMENSION, cycles=weighted.cycles,
                  stats=weighted.stats, boundary_cycle_edges=cycles)
    if not weighted.complete:
        result['reason'] = 'orbit-cycle allowance exhausted'
        return result
    result.update(_profile_summary(weighted.profiles))
    if result['components'] != weighted.orbits:
        raise ArithmeticError('component profile multiplicities disagree with orbit count')
    if record_certificate:
        result['certificate'] = dict(
            algorithm='normal-component-profile-v1',
            input_fingerprint=_fingerprint(triangulation, analysed, check),
            orbit_certificate=weighted.certificate,
            profiles=[[count, list(vector)] for count, vector in weighted.profiles])
    return result


def _verify_normal_component_profile(triangulation, coordinates, certificate, check):
    """Reconstruct source geometry and replay a supplied weighted orbit proof.

    The scheduler is not invoked.  The unweighted trace is checked by the
    existing independent local-relation verifier before weighted replay.
    Malformed source data/certificates return False; caller cancellation
    exceptions propagate.  The five-coordinate construction is shared with
    the producer and is separately tested against Regina component oracles.
    """
    from .weighted_orbits import replay_weighted_orbit_profile, WeightedOrbitError
    from .normal_surface_geometry import NormalOrbitError
    from .integer_codec import encoded_integer
    check()
    if not isinstance(certificate, dict):
        return False
    if certificate.get('algorithm') != 'normal-component-profile-v1':
        return False
    try:
        prepared = _prepare(triangulation, check)
        analysed = _coordinates(prepared, coordinates, check)
    except NormalOrbitError:
        return False
    if certificate.get('input_fingerprint') != _fingerprint(triangulation, analysed, check):
        return False
    size, pairs, runs, _ = component_weight_system(prepared, analysed, check=check)
    raw_profiles = certificate.get('profiles')
    if not isinstance(raw_profiles, list):
        return False
    decoded = []
    for row in raw_profiles:
        if (not isinstance(row, list) or len(row) != 2
                or not isinstance(row[1], list) or len(row[1]) != WEIGHT_DIMENSION):
            return False
        try:
            count = encoded_integer(row[0])
            vector = [encoded_integer(x) for x in row[1]]
        except ValueError:
            return False
        if count <= 0:
            return False
        decoded.append([count, vector])
    try:
        replayed = replay_weighted_orbit_profile(
            size, pairs, runs, certificate.get('orbit_certificate'),
            check=check, dimension=WEIGHT_DIMENSION)
    except WeightedOrbitError:
        return False
    return decoded == [[count, list(vector)] for count, vector in replayed.profiles]


class _CallbackRaised(BaseException):
    def __init__(self, original):
        self.original = original


def verify_normal_component_profile(triangulation, coordinates, certificate, *,
                                    check=lambda: None):
    """Source-bound replay; invalid data returns False, cancellation propagates.

    A tagged callback preserves even exceptions whose classes coincide with
    normal-input or weighted-certificate validation errors.  The producer's
    search scheduler is never run by this checker.
    """
    def checkpoint():
        try:
            check()
        except BaseException as exc:
            raise _CallbackRaised(exc) from exc
    try:
        return _verify_normal_component_profile(
            triangulation, coordinates, certificate, checkpoint)
    except _CallbackRaised as exc:
        raise exc.original
