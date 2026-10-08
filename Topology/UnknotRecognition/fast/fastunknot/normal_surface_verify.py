"""Replay supplied-normal-surface topology without any orbit search.

The finite manifold validator and normal-arc construction are shared with the
producer. Orbit scheduling and boundary cohomology search are not rerun.
The certified object is the caller's triangulation and normal vector, never
an implicitly associated knot diagram. Invalid source geometry raises the
same NormalOrbitError as the producer; malformed certificates return False.
"""

from .integer_codec import encoded_integer
from .interval_orbit_verify import verify_orbit_certificate
from .normal_surface_geometry import (
    _prepare, _coordinates, _arc_system, _boundary_graph, _fingerprint,
)
from .normal_surface_parity import _verify_parity


def verify_normal_surface_certificate(triangulation, coordinates, certificate, *,
                                      max_operations=None, check=lambda: None):
    """Verify exact source binding, all three orbit proofs and every claim.

    max_operations bounds the combined number of recorded orbit events before
    replay. Exceeding it returns False (unverified), never a topological result.
    Callbacks propagate, including ValueError; deadlines and serialized-size
    limits can be imposed by the caller. Running time is polynomial in the
    encoded triangulation, coordinates, and supplied trace lengths.
    """
    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('max_operations must be a nonnegative integer or None')
    if (type(certificate) is not dict or set(certificate) != {
            'schema', 'input_sha256', 'queries', 'boundary_homology', 'topology'}
            or certificate['schema'] != 'normal-surface-topology-v1'):
        return False
    proofs = certificate['queries']
    if type(proofs) is not dict or set(proofs) != {'surface', 'double', 'boundary'}:
        return False
    operations = 0
    for proof in proofs.values():
        check()
        if type(proof) is not dict or type(proof.get('operations')) is not list:
            return False
        operations += len(proof['operations'])
    if max_operations is not None and operations > max_operations:
        return False
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    if certificate['input_sha256'] != _fingerprint(triangulation, analysed, check):
        return False
    counts = {}
    for label, boundary, scale in [('surface', False, 1),
                                    ('double', False, 2), ('boundary', True, 1)]:
        check()
        size, pairings = _arc_system(prepared, analysed, boundary=boundary,
                                     scale=scale, check=check)
        if not verify_orbit_certificate(size, pairings, proofs[label], check=check):
            return False
        counts[label] = encoded_integer(proofs[label]['orbit_count'])
    parity = certificate['boundary_homology']
    if not _verify_parity(_boundary_graph(prepared, analysed, check), parity, check):
        return False
    components, lifted, boundary = (counts[key] for key in ('surface', 'double', 'boundary'))
    orientable, nonorientable = lifted - components, 2 * components - lifted
    if min(orientable, nonorientable) < 0:
        return False
    chi = analysed['euler_characteristic']
    expected = dict(components=components, orientable_components=orientable,
                    nonorientable_components=nonorientable, boundary_components=boundary,
                    euler_characteristic=chi, normal_disks=analysed['normal_disks'],
                    compressing_disk=(components == 1 and chi == 1 and boundary == 1
                                      and parity['nonzero']))
    if components == 1:
        defect = 2 - boundary - chi
        if orientable:
            if defect < 0 or defect & 1:
                return False
            expected['genus'] = defect // 2
        else:
            if defect < 1:
                return False
            expected['crosscaps'] = defect
    supplied = certificate['topology']
    if type(supplied) is not dict or set(supplied) != set(expected):
        return False
    for key, value in expected.items():
        check()
        if type(value) is bool:
            if type(supplied[key]) is not bool or supplied[key] != value:
                return False
        else:
            try:
                actual = encoded_integer(supplied[key])
            except ValueError:
                return False
            if actual != value:
                return False
    check()
    return True
