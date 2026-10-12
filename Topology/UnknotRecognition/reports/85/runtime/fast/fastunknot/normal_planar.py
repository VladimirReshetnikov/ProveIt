"""Optional compressed discovery of planar boundary-capping witnesses."""
from .normal_surface_geometry import _prepare, _coordinates
from .normal_component_geometry import boundary_homology_basis
from .normal_boundary_geometry import boundary_weight_system
from .weighted_orbits import weighted_orbit_histogram


def planar_cap_candidate(certificate, *, max_cycles=None, check=lambda: None):
    """Return boundary evidence for a candidate, without asserting source truth.

    Every positive must pass inspect_planar_certificate independently. This
    producer only tests the boundary census and the total Euler identity.
    """
    prepared = _prepare(certificate['triangulation'], check)
    analysed = _coordinates(prepared, certificate['coordinates'], check)
    return _planar_cap_candidate(certificate, prepared, analysed, max_cycles=max_cycles, check=check)


def _planar_cap_candidate(certificate, prepared, analysed, *, basis=None, max_cycles=None, check=lambda: None):
    if basis is None:
        basis = boundary_homology_basis(prepared, check)
    size, pairs, weights = boundary_weight_system(prepared, analysed, basis, check)
    result = weighted_orbit_histogram(size, pairs, weights, dimension=2,
        max_cycles=max_cycles, check=check, record_certificate=True)
    if result['status'] != 'COMPLETE':
        return dict(status='INCONCLUSIVE', stats=result['stats'])
    boundary = result['orbit_count']
    essential = sum(row['orbits'] for row in result['histogram'] if any(x & 1 for x in row['weight']))
    answer = dict(status='COMPLETE', boundary_components=boundary,
                  essential_boundary_components=essential, stats=result['stats'])
    if analysed['euler_characteristic']+boundary == 2 and essential == 1:
        answer['certificate'] = dict(certificate, schema='diagram-cocycle-planar-v1',
            boundary_homology_basis=basis, boundary_orbits=result['certificate'])
    return answer
