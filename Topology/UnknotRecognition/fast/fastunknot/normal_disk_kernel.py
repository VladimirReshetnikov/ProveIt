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
                                  record_certificate=False, unit_ray=True):
    """Count compressing-disc components after canonical coordinate reduction.

    The result deliberately contains no claimed total component count.  That
    quantity is not homogeneous for a surface with one-sided components.
    Use normal_component_census for a full unreduced component histogram.
    A checked unit-pivot support witness can certify that the primitive core
    is connected and decide its essential-disc count without orbit discovery.
    Disable unit_ray to reproduce the original query schedule and proof format.
    """
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if type(unit_ray) is not bool:
        raise ValueError('unit_ray must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    if periodic_rule not in ('fine_wilf', 'aht'):
        raise ValueError('unknown periodic rule')
    check()
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    return _count_prepared_discs(triangulation, prepared, analysed, max_cycles=max_cycles,
        periodic_rule=periodic_rule, check=check, record_certificate=record_certificate,
        unit_ray=unit_ray)


def _count_prepared_discs(triangulation, prepared, analysed, *, max_cycles=None,
                          periodic_rule='fine_wilf', check=lambda: None,
                          record_certificate=False, unit_ray=True):
    """Private observer on geometry already validated against this source.

    The caller owns the read-only source and freshly validated analysis.
    Public entry points still validate both; independent certificate replay
    always reconstructs its own source and geometry.
    """
    divisor, core, links = canonical_disk_core(prepared, analysed, check)
    metadata = dict(coordinate_divisor=divisor, vertex_links=links,
                    input_coordinate_bits=analysed['maximum_coordinate_bits'],
                    core_coordinate_bits=max(value.bit_length() for row in core for value in row))
    ray_proof = None
    if divisor and unit_ray:
        from .normal_support_peeling import peel_support_ray
        from .normal_support_peeling_verify import verify_support_ray
        from .normal_component_geometry import boundary_homology_basis
        core_data = analysed if core == analysed['rows'] else _coordinates(prepared, core, check)
        support_proof = peel_support_ray(prepared, core_data, check)
        if support_proof is not None:
            if not verify_support_ray(prepared, core_data, support_proof, check):
                raise ArithmeticError('unit-pivot ray proof failed independent replay')
            seed = support_proof['seed']
            if core[seed//7][seed % 7] != 1:
                raise ArithmeticError('unit seed in a canonical primitive core must be one')
            basis = boundary_homology_basis(prepared, check)
            parity = []
            for cycle in basis:
                check()
                parity.append(sum(core_data['weights'][edge] for edge in cycle) & 1)
            core_count = int(core_data['euler_characteristic'] == 1 and any(parity))
            ray_proof = dict(schema='normal-unit-ray-disc-v1', support_certificate=support_proof,
                boundary_homology_basis=basis, euler_characteristic=core_data['euler_characteristic'],
                boundary_homology_mod2=parity, compressing_disk_components=core_count)
    if ray_proof is not None:
        count, core_proof = divisor*ray_proof['compressing_disk_components'], ray_proof
        stats = dict(orbit_cycles=0, maximum_weight_runs=0, replay_events=0,
                     unit_ray=True, ray_steps=len(ray_proof['support_certificate']['steps']))
    elif divisor:
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
        answer['certificate'] = dict(schema='normal-disc-count-v2' if ray_proof is not None else 'normal-disc-count-v1',
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
            or certificate.get('schema') not in ('normal-disc-count-v1','normal-disc-count-v2')):
        return False
    ray = certificate['schema'] == 'normal-disc-count-v2'
    if ray and set(certificate) != {'schema','input_sha256','coordinate_divisor','vertex_links',
                                  'core_coordinates','core_certificate','compressing_disk_components'}:
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
    if ray:
        from .normal_support_peeling_verify import verify_support_ray
        from .normal_component_geometry import boundary_homology_basis
        if (not divisor or type(core_proof) is not dict
                or set(core_proof) != {'schema','support_certificate','boundary_homology_basis',
                    'euler_characteristic','boundary_homology_mod2','compressing_disk_components'}
                or core_proof['schema'] != 'normal-unit-ray-disc-v1'):
            return False
        core_data = _coordinates(prepared, core, check)
        support = core_proof['support_certificate']
        if not verify_support_ray(prepared, core_data, support, check):
            return False
        seed = encoded_integer(support['seed'])
        if core[seed//7][seed % 7] != 1:
            return False
        basis = boundary_homology_basis(prepared, check)
        parity = []
        for cycle in basis:
            check()
            parity.append(sum(core_data['weights'][edge] for edge in cycle) & 1)
        core_count = int(core_data['euler_characteristic'] == 1 and any(parity))
        if (not certificate_equal(core_proof['boundary_homology_basis'],basis)
                or not certificate_equal(core_proof['boundary_homology_mod2'],parity)
                or not certificate_equal(core_proof['euler_characteristic'],core_data['euler_characteristic'])
                or not certificate_equal(core_proof['compressing_disk_components'],core_count)):
            return False
        expected = divisor*core_count
    elif divisor:
        if (not verify_normal_component_certificate(triangulation, core, core_proof, check=check)
                or core_proof.get('mode') != 'disk'):
            return False
        expected = divisor*encoded_integer(core_proof['summary']['compressing_disk_components'])
    else:
        if core_proof is not None:
            return False
        expected = 0
    return certificate_equal(certificate.get('compressing_disk_components'), expected)
