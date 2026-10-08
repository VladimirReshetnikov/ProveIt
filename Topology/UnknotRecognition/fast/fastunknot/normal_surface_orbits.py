"""Native topology and optional proofs for supplied binary normal surfaces.

Geometry is reconstructed by normal_surface_geometry. Independent replay is
available in normal_surface_verify. No correspondence to a PD is asserted.
"""

from collections import deque
from .interval_orbits import count_orbits
from .normal_surface_geometry import (
    NormalOrbitError, _prepare, _coordinates, _arc_system, normal_arc_pairings,
    _boundary_graph, _fingerprint, _TOPOLOGY_FIELDS,
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


def normal_surface_topology(triangulation, coordinates, *, max_cycles=None,
                            periodic_rule='fine_wilf', check=lambda: None,
                            record_certificate=False):
    """Count components, orientations, boundary curves and total Euler value.

    The normal surface with doubled coordinates is the horizontal boundary of its
    normal interval bundle. In an orientable ambient manifold this is the
    orientation double cover. If the original has C components and the
    double has C2, precisely C2-C are orientable and 2*C-C2 are not.

    max_cycles is shared by all three orbit queries. Inconclusive counts
    never produce a topological or disc certificate. Global cancellation
    callbacks propagate. The returned data concerns only the supplied
    triangulation, with no asserted correspondence to a PD knot diagram.
    Optional certificates bind the validated input, three orbit proofs and
    a finite boundary-cohomology witness. Use integer_codec.json_safe to
    serialize arbitrary binary sizes. Incomplete calls emit no certificate.
    """
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    queries, proofs, used = {}, {}, 0
    for label, boundary, scale in [('surface', False, 1),
                                    ('double', False, 2), ('boundary', True, 1)]:
        check()
        size, pairings = _arc_system(prepared, analysed, boundary=boundary,
                                     scale=scale, check=check)
        remaining = None if max_cycles is None else max_cycles - used
        result = count_orbits(size, pairings, max_cycles=remaining,
                              periodic_rule=periodic_rule, check=check,
                              record_certificate=record_certificate)
        used += result.cycles
        queries[label] = dict(complete=result.complete, orbits=result.orbits,
                              points=size, pairings=len(pairings), cycles=result.cycles,
                              stats=dict(result.stats))
        if not result.complete:
            return dict(status='INCONCLUSIVE', reason='shared orbit-cycle allowance exhausted',
                        cycles=used, queries=queries)
        if record_certificate:
            proofs[label] = result.certificate
    components = queries['surface']['orbits']
    double_components = queries['double']['orbits']
    boundary_components = queries['boundary']['orbits']
    orientable = double_components - components
    nonorientable = 2 * components - double_components
    if min(orientable, nonorientable) < 0:
        raise ArithmeticError('normal doubling violates the orientation-cover identity')
    result = dict(status='COMPLETE', tetrahedra=len(prepared['tetrahedra']),
                  components=components, orientable_components=orientable,
                  nonorientable_components=nonorientable,
                  boundary_components=boundary_components,
                  euler_characteristic=analysed['euler_characteristic'],
                  normal_disks=analysed['normal_disks'],
                  maximum_coordinate_bits=analysed['maximum_coordinate_bits'],
                  boundary_normal_arcs=analysed['boundary_arcs'],
                  cycles=used, queries=queries,
                  trust='native topology of the supplied finite triangulation; '
                        'no correspondence with an input knot is asserted')
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
            topology={key: result[key] for key in _TOPOLOGY_FIELDS if key in result})
    check()
    return result


