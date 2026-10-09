"""Vertex-link and quadrilateral-content reduction for disc-component counts.

Essential disc counts, unlike total component counts, are homogeneous under
normal-coordinate scaling.  This count-only interface exploits that fact.
It makes no inference about a different surface or an unbound knot diagram.
"""

from math import gcd

from .integer_codec import encoded_integer, certificate_equal
from .normal_surface_geometry import _prepare, _coordinates, _fingerprint, NormalOrbitError
from .normal_surface_components import normal_component_census
from .normal_component_verify import verify_normal_component_certificate


def canonical_disk_core(prepared, analysed, check=lambda: None):
    """Remove all vertex links, then divide by quadrilateral gcd.

    Matching equations imply this gcd divides the peeled triangle entries.
    The assertion is checked exactly; no rounding is permitted.
    """
    minima = {}
    for tetrahedron, row in enumerate(analysed['rows']):
        check()
        for vertex in range(4):
            root = prepared['vertex_roots'][4*tetrahedron+vertex]
            minima[root] = min(minima.get(root, row[vertex]), row[vertex])
    divisor = 0
    for row in analysed['rows']:
        check()
        for value in row[4:]:
            divisor = gcd(divisor, value)
    core = []
    for tetrahedron, row in enumerate(analysed['rows']):
        check()
        residual = [row[vertex]-minima[prepared['vertex_roots'][4*tetrahedron+vertex]]
                    for vertex in range(4)] + row[4:]
        if divisor:
            if any(value % divisor for value in residual):
                raise ArithmeticError('quadrilateral gcd does not divide peeled triangles')
            core.append([value//divisor for value in residual])
        else:
            if any(residual):
                raise ArithmeticError('triangle-only surface did not reduce to vertex links')
            core.append(residual)
    return divisor, core, [dict(vertex=root, multiplicity=minima[root]) for root in sorted(minima)]


def normal_compressing_disk_count(triangulation, coordinates, *, max_cycles=None,
                                  periodic_rule='fine_wilf', check=lambda: None,
                                  record_certificate=False):
    """Count compressing-disc components after canonical coordinate reduction.

    The result deliberately contains no claimed total component count.  That
    quantity is not homogeneous for a surface with one-sided components.
    Use normal_component_census for a full unreduced component histogram.
    """
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    if periodic_rule not in ('fine_wilf', 'aht'):
        raise ValueError('unknown periodic rule')
    check()
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    divisor, core, links = canonical_disk_core(prepared, analysed, check)
    metadata = dict(coordinate_divisor=divisor, vertex_links=links,
                    input_coordinate_bits=analysed['maximum_coordinate_bits'],
                    core_coordinate_bits=max(value.bit_length() for row in core for value in row))
    if divisor:
        result = normal_component_census(triangulation, core, max_cycles=max_cycles,
            periodic_rule=periodic_rule, check=check, record_certificate=record_certificate)
        if result['status'] != 'COMPLETE':
            return dict(status='INCONCLUSIVE', reason=result['reason'],
                        stats=result['stats'], **metadata)
        count = divisor*result['compressing_disk_components']
        core_proof = result.get('certificate')
        stats = result['stats']
    else:
        count, core_proof = 0, None
        stats = dict(orbit_cycles=0, maximum_weight_runs=0, replay_events=0)
    answer = dict(status='COMPLETE', compressing_disk_components=count,
                  contains_compressing_disk=bool(count), stats=stats, **metadata,
                  trust='disc components of this supplied normal vector only; '
                        'no knot-diagram correspondence asserted')
    if record_certificate:
        answer['certificate'] = dict(schema='normal-disc-count-v1',
            input_sha256=_fingerprint(triangulation, analysed, check),
            coordinate_divisor=divisor, vertex_links=links,
            core_coordinates=core, core_certificate=core_proof,
            compressing_disk_components=count)
    check()
    return answer


def verify_normal_disk_count_certificate(triangulation, coordinates, certificate, *,
                                         check=lambda: None):
    """Reconstruct the reduction and check the core proof independently."""
    check()
    if (type(certificate) is not dict
            or certificate.get('schema') != 'normal-disc-count-v1'):
        return False
    try:
        prepared = _prepare(triangulation, check)
        analysed = _coordinates(prepared, coordinates, check)
    except NormalOrbitError:
        return False
    if certificate.get('input_sha256') != _fingerprint(triangulation, analysed, check):
        return False
    # Independent arithmetic reconstruction; do not invoke canonical_disk_core.
    groups = {}
    for tetrahedron, row in enumerate(analysed['rows']):
        check()
        for vertex in range(4):
            root = prepared['vertex_roots'][4*tetrahedron+vertex]
            groups.setdefault(root, []).append((tetrahedron, vertex))
    core = [row.copy() for row in analysed['rows']]
    links = []
    for root in sorted(groups):
        check()
        amount = min(core[t][v] for t, v in groups[root])
        links.append(dict(vertex=root, multiplicity=amount))
        for t, v in groups[root]:
            core[t][v] -= amount
    divisor = 0
    for row in core:
        check()
        for value in row[4:]:
            divisor = gcd(divisor, value)
    if divisor:
        if any(value % divisor for row in core for value in row):
            return False
        core = [[value//divisor for value in row] for row in core]
    elif any(value for row in core for value in row):
        return False
    if (not certificate_equal(certificate.get('coordinate_divisor'), divisor)
            or not certificate_equal(certificate.get('vertex_links'), links)
            or not certificate_equal(certificate.get('core_coordinates'), core)):
        return False
    core_proof = certificate.get('core_certificate')
    if divisor:
        if (not verify_normal_component_certificate(triangulation, core, core_proof, check=check)
                or core_proof.get('mode') != 'disk'):
            return False
        expected = divisor*encoded_integer(core_proof['summary']['compressing_disk_components'])
    else:
        if core_proof is not None:
            return False
        expected = 0
    return certificate_equal(certificate.get('compressing_disk_components'), expected)
