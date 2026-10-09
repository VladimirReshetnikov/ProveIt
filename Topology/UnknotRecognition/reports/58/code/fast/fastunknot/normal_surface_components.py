"""Compressed component census and disc detection for a supplied normal vector.

This adds a missing query to the repository: a disconnected normal surface
may contain compressing discs.  A negative query says only that this supplied
surface has no such component.  It is not a knottedness decision or a search
over normal vectors.  An ambient knot-diagram provenance certificate remains
a separate obligation.
"""

from .normal_surface_geometry import _prepare, _coordinates, _fingerprint
from .normal_component_geometry import component_weight_system, full_vector_signature
from .weighted_orbits import (
    weighted_orbit_histogram, weighted_histogram_from_orbit_certificate,
)


_SUMMARY_FIELDS = ('components', 'compressing_disk_components',
                   'contains_compressing_disk', 'component_histogram')


def _component_summary(prepared, histogram, mode, basis, check=lambda: None):
    """Interpret already-certified orbit weights using surface classification."""
    grouped, total, compressing = {}, 0, 0
    for record in histogram:
        check()
        weight, multiplicity = record['weight'], record['orbits']
        if mode == 'coordinates':
            signature, coordinates = full_vector_signature(prepared, weight, basis, check)
        else:
            signature, coordinates = weight, None
        chi, first, second = signature[:3]
        parity = (first & 1, second & 1)
        is_compressing = chi == 1 and any(parity)
        total += multiplicity
        compressing += multiplicity if is_compressing else 0
        key = (chi, *parity)
        if mode != 'disk':
            disks, boundary = signature[3:5]
            if disks < 1 or boundary < 0:
                raise ArithmeticError('a component must contain disks and nonnegative boundary')
            key += (disks, boundary)
        if mode == 'coordinates':
            key += tuple(weight)
        if key not in grouped:
            row = dict(euler_characteristic=chi, boundary_homology_mod2=list(parity),
                       compressing_disk=bool(is_compressing), multiplicity=0)
            if mode != 'disk':
                row.update(normal_disks=disks, boundary_points=boundary)
            if coordinates is not None:
                row['coordinates'] = coordinates
            grouped[key] = row
        grouped[key]['multiplicity'] += multiplicity
    return dict(components=total, compressing_disk_components=compressing,
                contains_compressing_disk=bool(compressing),
                component_histogram=[grouped[key] for key in sorted(grouped)])


def normal_component_census(triangulation, coordinates, *, mode='disk',
                            max_cycles=None, periodic_rule='fine_wilf',
                            check=lambda: None, record_certificate=False,
                            orbit_certificate=None):
    """Count components and embedded compressing discs without expanding sheets.

    ``mode='disk'`` uses three integer weights per representative.  ``summary``
    adds disk and boundary point counts.  ``coordinates`` returns a histogram
    of full 7t-coordinate component vectors, useful when a disc must be cut out.
    Histogram multiplicities stay binary; no component list is expanded.

    A supplied ``orbit_certificate`` is checked and reused; ``max_cycles``
    must then be None, since no orbit search runs.  Cancellation applies to
    validation, discovery and replay.  Incomplete calls give no verdict.
    """
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if mode not in ('disk', 'summary', 'coordinates'):
        raise ValueError('mode must be disk, summary, or coordinates')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    if periodic_rule not in ('fine_wilf', 'aht'):
        raise ValueError('unknown periodic rule')
    if orbit_certificate is not None and max_cycles is not None:
        raise ValueError('max_cycles cannot constrain replay of a supplied trace')
    check()
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    system = component_weight_system(prepared, analysed, mode=mode, check=check)
    if orbit_certificate is None:
        result = weighted_orbit_histogram(system['size'], system['pairings'],
            system['weights'], dimension=system['dimension'], max_cycles=max_cycles,
            periodic_rule=periodic_rule, check=check, record_certificate=record_certificate)
    else:
        result = weighted_histogram_from_orbit_certificate(system['size'],
            system['pairings'], system['weights'], orbit_certificate,
            dimension=system['dimension'], check=check, record_certificate=record_certificate)
    if result['status'] != 'COMPLETE':
        return dict(status='INCONCLUSIVE', reason='orbit-cycle allowance exhausted',
                    mode=mode, stats=result['stats'])
    summary = _component_summary(prepared, result['histogram'], mode, system['basis'], check)
    if summary['components'] != result['orbit_count']:
        raise ArithmeticError('component multiplicities disagree with orbit count')
    if sum(row['euler_characteristic']*row['multiplicity']
           for row in summary['component_histogram']) != analysed['euler_characteristic']:
        raise ArithmeticError('component Euler characteristics do not sum to the input')
    answer = dict(status='COMPLETE', mode=mode, tetrahedra=len(analysed['rows']),
                  normal_points=system['size'], normal_disks=analysed['normal_disks'],
                  euler_characteristic=analysed['euler_characteristic'],
                  boundary_normal_arcs=analysed['boundary_arcs'],
                  maximum_coordinate_bits=analysed['maximum_coordinate_bits'],
                  weight_dimension=system['dimension'],
                  boundary_homology_basis=system['basis'], stats=result['stats'], **summary,
                  trust='components of the supplied normal surface in the validated '
                        'torus-boundary manifold; no knot-diagram correspondence asserted')
    if record_certificate:
        answer['certificate'] = dict(schema='normal-component-census-v1',
            input_sha256=_fingerprint(triangulation, analysed, check), mode=mode,
            boundary_homology_basis=system['basis'], weighted_orbits=result['certificate'],
            summary=summary)
    check()
    return answer
