"""Exact connected-component vectors of a supplied binary normal surface.

One local-edge anchor per normal disc type turns weighted interval orbits
into normal coordinates of actual connected components. Equal vectors are
coalesced with binary multiplicities. This implements the construction in
Agol--Hass--Thurston, Section 6, using the maintained native geometry.

The supplied finite compact orientable manifold has one torus boundary.
There is no implicit correspondence to a knot diagram and no vector search.
"""

from .integer_codec import encoded_integer
from .normal_surface_geometry import (
    _prepare, _coordinates, _arc_system, _edge, _quad, _EDGES,
    _boundary_graph, _fingerprint,
)
from .normal_surface_parity import _parity_certificate, _verify_parity
from .weighted_orbits import (
    WeightInterval, weighted_orbit_counts, verify_weighted_orbit_certificate,
)


def normal_disc_weights(prepared, analysed, check=lambda: None):
    """Build additive half-open basis-weight intervals in global edge order.

    Each disc receives exactly one anchor, even when multiple local edges
    identify globally. Global edge orientations come from the parity union-find.
    """
    dimension = 7 * len(analysed['rows'])
    offsets, total = {}, 0
    for root in sorted(analysed['weights']):
        check()
        offsets[root] = total
        total += analysed['weights'][root]
    result = []
    for t, row in enumerate(analysed['rows']):
        check()
        for kind, count in enumerate(row):
            check()
            if not count:
                continue
            if kind < 4:
                other = 1 if kind == 0 else 0
                a, b = sorted((kind, other))
            else:
                a, b = next(edge for edge in _EDGES if _quad(*edge) != kind - 4)
            local = _edge(t, a, b)
            root = prepared['edge_roots'][local]
            weight = analysed['weights'][root]
            if kind == a:
                lo, hi = 0, count
            elif kind == b:
                lo, hi = weight - count, weight
            else:
                lo, hi = row[a], row[a] + count
            if prepared['edge_orientations'][local]:
                lo, hi = weight - hi, weight - lo
            if not 0 <= lo < hi <= weight:
                raise ArithmeticError('disc anchor is outside its edge block')
            basis = tuple(int(index == 7 * t + kind) for index in range(dimension))
            result.append(WeightInterval(offsets[root] + lo, offsets[root] + hi, basis))
    return total, result


def _component_data(prepared, value, multiplicity, check):
    rows = [list(value[i:i + 7]) for i in range(0, len(value), 7)]
    analysed = _coordinates(prepared, rows, check)
    if analysed['normal_disks'] == 0 or multiplicity < 1:
        raise ArithmeticError('a component inventory contains an empty component')
    chi, boundary = analysed['euler_characteristic'], analysed['boundary_arcs']
    # Weighted extraction proves connectedness. A connected compact surface
    # with chi=1 and nonempty boundary is a disc by surface classification.
    disk = chi == 1 and boundary > 0
    return dict(coordinates=rows, multiplicity=multiplicity,
                euler_characteristic=chi, normal_disks=analysed['normal_disks'],
                boundary_normal_arcs=boundary, disk=disk), analysed


def normal_component_inventory(triangulation, coordinates, *, max_cycles=None,
                               max_operations=None, max_weight_blocks=None,
                               max_output_records=None, record_certificate=False,
                               check=lambda: None):
    """Extract all distinct component vectors and detect compressing discs.

    COMPLETE certifies the inventory of this supplied vector only. A false
    has_compressing_disk says nothing about other normal surfaces or the knot.
    One weighted orbit query suffices; classification of disc components uses
    linear Euler data and finite boundary parity, with no extra orbit searches.
    """
    check()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be boolean')
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    size, pairings = _arc_system(prepared, analysed, check=check)
    anchored_size, weights = normal_disc_weights(prepared, analysed, check)
    if size != anchored_size:
        raise ArithmeticError('anchor and normal-arc universes differ')
    dimension = 7 * len(analysed['rows'])
    answer = weighted_orbit_counts(
        size, pairings, weights, dimension=dimension, max_cycles=max_cycles,
        max_operations=max_operations, max_weight_blocks=max_weight_blocks,
        max_output_records=max_output_records, record_certificate=record_certificate,
        check=check)
    stats = dict(answer.stats, anchor_intervals=len(weights), dimension=dimension,
                 orbit_queries=1, orbit_cycles=answer.cycles)
    if not answer.complete:
        return dict(status='INCONCLUSIVE', reason=answer.reason, stats=stats)
    flat = tuple(value for row in analysed['rows'] for value in row)
    if answer.aggregate != flat:
        raise ArithmeticError('component coordinates do not conserve the source vector')
    profiles, parity_proofs = [], []
    for item in answer.classes:
        check()
        profile, component = _component_data(prepared, item.value, item.multiplicity, check)
        parity = (_parity_certificate(_boundary_graph(prepared, component, check), check)
                  if profile['disk'] else None)
        profile['compressing_disk'] = bool(parity and parity['nonzero'])
        profiles.append(profile)
        parity_proofs.append(parity)
    disks = sum(p['multiplicity'] for p in profiles if p['compressing_disk'])
    result = dict(
        status='COMPLETE', components=answer.orbits, distinct_vectors=len(profiles),
        profiles=profiles, normal_disks=analysed['normal_disks'],
        euler_characteristic=analysed['euler_characteristic'],
        compressing_disk_components=disks, has_compressing_disk=disks > 0,
        stats=stats,
        trust='native components of the supplied finite triangulation and vector; '
              'no correspondence with an input knot is asserted')
    if disks:
        result['compressing_disk_witness'] = next(
            p['coordinates'] for p in profiles if p['compressing_disk'])
    if record_certificate:
        result['certificate'] = dict(
            schema='normal-component-inventory-v1',
            input_sha256=_fingerprint(triangulation, analysed, check),
            weighted=answer.certificate, profiles=profiles,
            boundary_homology=parity_proofs)
    check()
    return result


class _MalformedInventory(ValueError):
    pass


def _integer(value):
    try:
        return encoded_integer(value)
    except ValueError as exc:
        raise _MalformedInventory('invalid certificate integer') from exc


def verify_normal_component_certificate(triangulation, coordinates, certificate, *,
                                         max_operations=None, max_weight_blocks=None,
                                         max_output_records=None, check=lambda: None):
    """Verify source-bound component coordinates without orbit discovery.

    Geometry reconstruction is shared with the producer. Weighted transport is
    replayed over the independently checked unweighted trace; it is not a second
    separately implemented weighted algorithm. Boundary parity is independently
    checked by the existing finite cohomology verifier. Callback errors propagate.
    """
    check()
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    fields = {'schema', 'input_sha256', 'weighted', 'profiles', 'boundary_homology'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] != 'normal-component-inventory-v1'
            or certificate['input_sha256'] != _fingerprint(triangulation, analysed, check)):
        return False
    size, pairings = _arc_system(prepared, analysed, check=check)
    _, weights = normal_disc_weights(prepared, analysed, check)
    dimension = 7 * len(analysed['rows'])
    if not verify_weighted_orbit_certificate(
            size, pairings, weights, certificate['weighted'], dimension=dimension,
            max_operations=max_operations, max_weight_blocks=max_weight_blocks,
            max_output_records=max_output_records, check=check):
        return False
    profiles, parities = certificate['profiles'], certificate['boundary_homology']
    if type(profiles) is not list or type(parities) is not list:
        return False
    classes = certificate['weighted']['classes']
    if len(profiles) != len(classes) or len(parities) != len(classes):
        return False
    aggregate = [0] * dimension
    try:
        for item, claimed, parity in zip(classes, profiles, parities):
            check()
            value = tuple(_integer(x) for x in item[0])
            multiplicity = _integer(item[1])
            expected, component = _component_data(prepared, value, multiplicity, check)
            if expected['disk']:
                if not _verify_parity(_boundary_graph(prepared, component, check), parity, check):
                    return False
                expected['compressing_disk'] = parity['nonzero']
            else:
                if parity is not None:
                    return False
                expected['compressing_disk'] = False
            if type(claimed) is not dict or set(claimed) != set(expected):
                return False
            if (type(claimed['coordinates']) is not list
                    or len(claimed['coordinates']) != len(analysed['rows'])):
                return False
            rows = []
            for row in claimed['coordinates']:
                if type(row) is not list or len(row) != 7:
                    return False
                rows.append([_integer(x) for x in row])
            decoded = {'coordinates': rows}
            for key in ('multiplicity', 'euler_characteristic', 'normal_disks',
                        'boundary_normal_arcs'):
                decoded[key] = _integer(claimed[key])
            for key in ('disk', 'compressing_disk'):
                if type(claimed[key]) is not bool:
                    return False
                decoded[key] = claimed[key]
            if decoded != expected:
                return False
            aggregate = [a + multiplicity * b for a, b in zip(aggregate, value)]
    except _MalformedInventory:
        return False
    return tuple(aggregate) == tuple(x for row in analysed['rows'] for x in row)
