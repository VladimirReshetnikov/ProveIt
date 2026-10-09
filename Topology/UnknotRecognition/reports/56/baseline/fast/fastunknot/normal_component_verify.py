"""Source-bound independent arithmetic replay for normal component censuses.

Geometry uses the shared, validated finite-triangulation representation.
The boundary basis is checked by binary homology rather than by repeating
tree-cotree construction.  Weight transport uses a separately implemented
prefix-sum checker and never invokes orbit discovery or producer transport.
"""

from .integer_codec import encoded_integer, certificate_equal
from .normal_surface_geometry import _prepare, _coordinates, _fingerprint, NormalOrbitError
from .normal_component_geometry import (
    component_weight_system, valid_boundary_basis, full_vector_signature,
)
from .weighted_orbit_verify import verify_weighted_orbit_certificate


def verify_normal_component_certificate(triangulation, coordinates, certificate, *,
                                         check=lambda: None):
    """Check every source-dependent claim; malformed evidence returns False.

    Exceptions from a cancellation callback propagate.  This is not a
    containment boundary for unbounded serialized input or arbitrary code.
    """
    check()
    if (type(certificate) is not dict
            or certificate.get('schema') != 'normal-component-census-v1'):
        return False
    mode = certificate.get('mode')
    if mode not in ('disk', 'summary', 'coordinates'):
        return False
    try:
        prepared = _prepare(triangulation, check)
        analysed = _coordinates(prepared, coordinates, check)
    except NormalOrbitError:
        return False
    if certificate.get('input_sha256') != _fingerprint(triangulation, analysed, check):
        return False
    basis = certificate.get('boundary_homology_basis')
    if not valid_boundary_basis(prepared, basis, check):
        return False
    system = component_weight_system(prepared, analysed, mode=mode, basis=basis, check=check)
    proof = certificate.get('weighted_orbits')
    if not verify_weighted_orbit_certificate(system['size'], system['pairings'],
            system['weights'], proof, dimension=system['dimension'], check=check):
        return False
    # Deliberately interpret the certified histogram here, without using the
    # producer's classification helper or trusting its claimed counts.
    grouped, total, compressing, euler = {}, 0, 0, 0
    for item in proof['histogram']:
        check()
        weight = [encoded_integer(value) for value in item['weight']]
        count = encoded_integer(item['orbits'])
        if mode == 'coordinates':
            try:
                values, rows = full_vector_signature(prepared, weight, basis, check)
            except (NormalOrbitError, ValueError):
                return False
        else:
            values, rows = weight, None
        chi, first, second = values[:3]
        parity = first % 2, second % 2
        good = chi == 1 and parity != (0, 0)
        key = (chi, *parity)
        row = dict(euler_characteristic=chi, boundary_homology_mod2=list(parity),
                   compressing_disk=good, multiplicity=0)
        if mode != 'disk':
            disks, boundary = values[3:5]
            if disks < 1 or boundary < 0:
                return False
            key += (disks, boundary)
            row.update(normal_disks=disks, boundary_points=boundary)
        if mode == 'coordinates':
            key += tuple(weight)
            row['coordinates'] = rows
        grouped.setdefault(key, row)['multiplicity'] += count
        total += count
        euler += count*chi
        if good:
            compressing += count
    if euler != analysed['euler_characteristic']:
        return False
    expected = dict(components=total, compressing_disk_components=compressing,
                    contains_compressing_disk=bool(compressing),
                    component_histogram=[grouped[key] for key in sorted(grouped)])
    return certificate_equal(certificate.get('summary'), expected)
