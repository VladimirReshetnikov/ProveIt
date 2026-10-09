"""Native topology and optional proofs for supplied binary normal surfaces.

Geometry is reconstructed by normal_surface_geometry. Independent replay is
available in normal_surface_verify. No correspondence to a PD is asserted.
"""

from collections import deque
from .interval_orbits import count_orbits
from .normal_surface_geometry import (
    NormalOrbitError, _prepare, _coordinates, _arc_system, normal_arc_pairings,
    _boundary_graph, _fingerprint, _TOPOLOGY_FIELDS,
    _primitive_coordinates,
    _boundary_intervals, _coned_pairings, _BOUNDARY_FIELDS,
)


def _nonzero_boundary_class(prepared, analysed, check):
    """Nonzero mod-two homology of the boundary cycle in the boundary torus."""
    graph = {}
    for edge in prepared['boundary_incidence']:
        check()
        a, b = prepared['endpoints'][edge]
        parity = analysed['weights'][edge] & 1
        graph.setdefault(a, []).append((b, parity))
        graph.setdefault(b, []).append((a, parity))
    potentials = {}
    for start in graph:
        if start in potentials:
            continue
        potentials[start] = 0
        queue = deque([start])
        while queue:
            check()
            a = queue.popleft()
            for b, parity in graph[a]:
                value = potentials[a] ^ parity
                if b in potentials:
                    if potentials[b] != value:
                        return True
                else:
                    potentials[b] = value
                    queue.append(b)
    return False


def _classify_boundary(prepared, analysed, queries, systems, query, check, *,
                       shortcuts=True, even_multiple=False):
    """Counts of boundary-touching components in Q and 2Q, or incomplete.

    The internal no-shortcut mode is a research ablation. Replay derives
    omitted counts independently and accepts redundant valid cone proofs.
    """
    total = queries['surface']['orbits']
    double = queries['double']['orbits']
    boundary = queries['boundary']['orbits']
    check()
    if boundary == 0:
        return 0, 0
    if shortcuts and total == 1:
        return 1, double
    marks = _boundary_intervals(prepared, analysed, check=check)
    if shortcuts and marks == ((0, systems['surface'][0]),):
        return total, double
    if shortcuts and boundary == 1:
        touched = 1
    elif shortcuts and even_multiple and double not in (total, 2 * total):
        # For even g, gQ is g/2 copies of the orientable surface 2Q.
        # Only its touched count is needed; do not claim the unknown count in Q.
        touched = None
    else:
        size, pairings = systems['surface']
        coned = query('surface_boundary_cone', size, _coned_pairings(pairings, marks, check))
        if coned is None:
            return None
        touched = total - coned + 1
    if shortcuts and double == 2 * total:
        lifted_touched = 2 * touched
    elif shortcuts and double == total:
        lifted_touched = touched
    else:
        size, pairings = systems['double']
        lifted_marks = _boundary_intervals(prepared, analysed, scale=2, check=check)
        coned = query('double_boundary_cone', size,
                      _coned_pairings(pairings, lifted_marks, check))
        if coned is None:
            return None
        lifted_touched = double - coned + 1
    return touched, lifted_touched


def normal_surface_topology(triangulation, coordinates, *, max_cycles=None,
                            periodic_rule='fine_wilf', check=lambda: None,
                            record_certificate=False, reduce_multiplicity=True,
                            classify_boundary=False, coorientation=True,
                            sweep_direction='forward'):
    """Count components, orientations, boundary curves and total Euler value.

    The normal surface with doubled coordinates is the horizontal boundary of its
    normal interval bundle. In an orientable ambient manifold this is the
    orientation double cover. If the original has C components and the
    double has C2, precisely C2-C are orientable and 2*C-C2 are not.

    max_cycles is shared by the three base and all optional cone queries. Inconclusive counts
    never produce a topological or disc certificate. Global cancellation
    callbacks propagate. The returned data concerns only the supplied
    triangulation, with no asserted correspondence to a PD knot diagram.
    Optional certificates bind the validated input, three orbit proofs and
    a finite boundary-cohomology witness. Use integer_codec.json_safe to
    serialize arbitrary binary sizes. Incomplete calls emit no certificate.
    Common coordinate multiplicity is removed before orbit search by default.
    Query statistics then describe the quotient vector, and coordinate_divisor
    records its exact scale. Topology fields always describe the original input.
    Disable reduce_multiplicity to retain direct queries and version-one proofs.
    classify_boundary adds open/closed component counts by orientability, using
    at most two further orbit queries under the same allowance. Existing counts
    can make those queries unnecessary. Its optional proofs use version three;
    the existing topology fields are unchanged.
    coorientation first tries a finite sufficient parity certificate for a
    trivial orientation double. Success derives its orbit count from the
    surface query and emits version four when recording proofs; failure uses
    the original double query. Disable it for the original query schedule.
    sweep_direction is passed to each actual orbit query, including optional
    boundary cones. 'wide' chooses the wider terminal carrier; it is a
    scheduling heuristic, not a surface-topology assertion.
    'race' tries both directions with geometrically increasing checkpoint
    allowances. All begun cycles, including abandoned attempts, share the
    caller's max_cycles allowance. Only completed winning proofs are emitted.
    """
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if type(reduce_multiplicity) is not bool:
        raise ValueError('reduce_multiplicity must be bool')
    if type(classify_boundary) is not bool:
        raise ValueError('classify_boundary must be bool')
    if type(coorientation) is not bool:
        raise ValueError('coorientation must be bool')
    if sweep_direction not in ('forward', 'reverse', 'wide', 'race'):
        raise ValueError("sweep_direction must be 'forward', 'reverse', 'wide' or 'race'")
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    divisor, orbit_data = (_primitive_coordinates(analysed, check)
                           if reduce_multiplicity else (1, analysed))
    reduction = {'coordinate_divisor': divisor} if divisor > 1 else {}
    queries, proofs, used = {}, {}, 0
    trivialization = None
    systems = {} if classify_boundary else None
    for label, boundary, scale in [('surface', False, 1),
                                    ('double', False, 2), ('boundary', True, 1)]:
        check()
        size, pairings = _arc_system(prepared, orbit_data, boundary=boundary,
                                     scale=scale, check=check)
        if classify_boundary and not boundary:
            systems[label] = size, pairings
        if label == 'double' and trivialization is not None:
            count = 2*queries['surface']['orbits']
            queries[label] = dict(complete=True, orbits=count, points=size,
                                  pairings=len(pairings), cycles=0,
                                  stats=dict(derived_coorientation=True))
            if record_certificate:
                proofs[label] = dict(schema='normal-double-coorientation-v1',
                                     coorientation=trivialization,
                                     orbit_count=count, operations=[])
            continue
        remaining = None if max_cycles is None else max_cycles - used
        result = count_orbits(size, pairings, max_cycles=remaining,
                              periodic_rule=periodic_rule, check=check,
                              record_certificate=record_certificate,
                              sweep_direction=sweep_direction)
        used += result.cycles
        queries[label] = dict(complete=result.complete, orbits=result.orbits,
                              points=size, pairings=len(pairings), cycles=result.cycles,
                              stats=dict(result.stats))
        if not result.complete:
            return dict(status='INCONCLUSIVE', reason='shared orbit-cycle allowance exhausted',
                        cycles=used, queries=queries, **reduction)
        if record_certificate:
            proofs[label] = result.certificate
        if label == 'surface' and coorientation:
            from .normal_coorientation import _coorientation_graph
            from .normal_surface_parity import _parity_certificate
            candidate = _parity_certificate(_coorientation_graph(orbit_data, pairings, check), check)
            if not candidate['nonzero']:
                trivialization = candidate
    components = queries['surface']['orbits']
    double_components = queries['double']['orbits']
    boundary_components = queries['boundary']['orbits']
    orientable = double_components - components
    nonorientable = 2 * components - double_components
    if min(orientable, nonorientable) < 0:
        raise ArithmeticError('normal doubling violates the orientation-cover identity')
    boundary_counts = None
    if classify_boundary:
        def query(label, size, pairings):
            nonlocal used
            remaining = None if max_cycles is None else max_cycles - used
            answer = count_orbits(size, pairings, max_cycles=remaining,
                                  periodic_rule=periodic_rule, check=check,
                                  record_certificate=record_certificate,
                                  sweep_direction=sweep_direction)
            used += answer.cycles
            queries[label] = dict(complete=answer.complete, orbits=answer.orbits,
                                  points=size, pairings=len(pairings), cycles=answer.cycles,
                                  stats=dict(answer.stats))
            if not answer.complete:
                return None
            if record_certificate:
                proofs[label] = answer.certificate
            return answer.orbits
        boundary_counts = _classify_boundary(prepared, orbit_data, queries, systems, query, check,
                                             even_multiple=divisor % 2 == 0)
        if boundary_counts is None:
            return dict(status='INCONCLUSIVE', reason='shared orbit-cycle allowance exhausted',
                        cycles=used, queries=queries, **reduction)
        touched, lifted_touched = boundary_counts
        if touched is None:
            if divisor % 2 or not 1 <= lifted_touched <= min(double_components, 2*boundary_components):
                raise ArithmeticError('invalid boundary orientation-cover count')
        else:
            boundary_orientable = lifted_touched - touched
            boundary_nonorientable = 2 * touched - lifted_touched
            if not (0 <= boundary_orientable <= orientable
                    and 0 <= boundary_nonorientable <= nonorientable
                    and (touched == 0 if boundary_components == 0 else
                         1 <= touched <= min(components, boundary_components))):
                raise ArithmeticError('boundary component counts violate cover identities')
    if divisor > 1:
        orientable, nonorientable = (divisor * orientable + (divisor // 2) * nonorientable,
                                     (divisor & 1) * nonorientable)
        components = orientable + nonorientable
        boundary_components *= divisor
    result = dict(status='COMPLETE', tetrahedra=len(prepared['tetrahedra']),
                  components=components, orientable_components=orientable,
                  nonorientable_components=nonorientable,
                  boundary_components=boundary_components,
                  euler_characteristic=analysed['euler_characteristic'],
                  normal_disks=analysed['normal_disks'],
                  maximum_coordinate_bits=analysed['maximum_coordinate_bits'],
                  boundary_normal_arcs=analysed['boundary_arcs'],
                  cycles=used, queries=queries, **reduction,
                  trust='native topology of the supplied finite triangulation; '
                        'no correspondence with an input knot is asserted')
    if classify_boundary:
        if boundary_counts[0] is None:
            boundary_orientable, boundary_nonorientable = (divisor // 2) * lifted_touched, 0
        else:
            boundary_orientable, boundary_nonorientable = (
                divisor * boundary_orientable + (divisor // 2) * boundary_nonorientable,
                (divisor & 1) * boundary_nonorientable)
        touched = boundary_orientable + boundary_nonorientable
        result.update(components_with_boundary=touched, closed_components=components-touched,
                      orientable_components_with_boundary=boundary_orientable,
                      nonorientable_components_with_boundary=boundary_nonorientable,
                      closed_orientable_components=orientable-boundary_orientable,
                      closed_nonorientable_components=nonorientable-boundary_nonorientable)
    if components == 1:
        defect = 2 - boundary_components - analysed['euler_characteristic']
        if orientable:
            if defect < 0 or defect & 1:
                raise ArithmeticError('invalid connected orientable surface characteristic')
            result['genus'] = defect // 2
        else:
            if defect < 1:
                raise ArithmeticError('invalid connected nonorientable surface characteristic')
            result['crosscaps'] = defect
    result['compressing_disk'] = (components == 1
                                  and analysed['euler_characteristic'] == 1
                                  and boundary_components == 1
                                  and _nonzero_boundary_class(prepared, analysed, check))
    if record_certificate:
        from .normal_surface_parity import _parity_certificate
        parity = _parity_certificate(_boundary_graph(prepared, analysed, check), check)
        result['certificate'] = dict(
            schema='normal-surface-topology-v1',
            input_sha256=_fingerprint(triangulation, analysed, check),
            queries=proofs, boundary_homology=parity,
            topology={key: result[key] for key in
                      _TOPOLOGY_FIELDS + (_BOUNDARY_FIELDS if classify_boundary else ())
                      if key in result})
        if divisor > 1:
            result['certificate'].update(schema='normal-surface-topology-v2',
                                         coordinate_divisor=divisor)
        if classify_boundary:
            result['certificate'].update(schema='normal-surface-topology-v3',
                                         coordinate_divisor=divisor)
        if trivialization is not None:
            result['certificate'].update(schema='normal-surface-topology-v4',
                                         coordinate_divisor=divisor,
                                         classify_boundary=classify_boundary)
    check()
    return result


