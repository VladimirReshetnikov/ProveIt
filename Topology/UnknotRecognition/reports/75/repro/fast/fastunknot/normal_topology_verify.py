"""Independent source-bound replay of connected normal-topology spectra.

The checker reuses the established geometry contract. It never invokes orbit
discovery, forward transversal construction, weighted producer replay, spectrum
inversion, or the producer's coordinate core reduction.
"""

from math import gcd

from .integer_codec import encoded_integer, certificate_equal
from .normal_surface_geometry import (
    _prepare, _coordinates, _arc_system, _fingerprint, NormalOrbitError,
)
from .normal_topology_geometry import topology_weight_system, vertex_link_totals
from .orbit_transversal_verify import verify_orbit_transversal_certificate
from .weighted_orbit_verify import verify_weighted_orbit_certificate
from .topology_spectrum import verify_topology_spectrum, verify_scaled_spectrum


def _decoded_rows(rows):
    """Decode fields only after a mathematical spectrum checker accepts them."""
    return [{key: (value if key == 'orientable' else encoded_integer(value))
             for key, value in row.items()} for row in rows]


def verify_normal_topology_spectrum(triangulation, coordinates, certificate, *,
                                    check=lambda: None):
    """Check a complete certificate against the original triangulation/vector.

    Malformed or false evidence returns False. Cooperative cancellation
    exceptions propagate. A certificate is not a runtime-resource guarantee.
    """
    check()
    keys = {'schema', 'input_sha256', 'reduced_core', 'coordinate_divisor',
            'vertex_links', 'core_coordinates', 'query', 'summary'}
    if (type(certificate) is not dict or set(certificate) != keys
            or certificate['schema'] != 'normal-topology-spectrum-v1'
            or type(certificate['reduced_core']) is not bool):
        return False
    try:
        prepared = _prepare(triangulation, check)
        analysed = _coordinates(prepared, coordinates, check)
    except NormalOrbitError:
        return False
    if certificate['input_sha256'] != _fingerprint(triangulation, analysed, check):
        return False
    reduced = certificate['reduced_core']
    core = [row.copy() for row in analysed['rows']]
    divisor, links = 1, []
    if reduced:
        groups = {}
        for tetrahedron, row in enumerate(core):
            check()
            for vertex in range(4):
                root = prepared['vertex_roots'][4 * tetrahedron + vertex]
                groups.setdefault(root, []).append((tetrahedron, vertex))
        for vertex in sorted(groups):
            check()
            amount = min(core[t][v] for t, v in groups[vertex])
            links.append(dict(vertex=vertex, multiplicity=amount))
            for t, v in groups[vertex]:
                core[t][v] -= amount
        divisor = 0
        for row in core:
            check()
            for value in row[4:]:
                divisor = gcd(divisor, value)
        if divisor:
            for row in core:
                check()
                for j, value in enumerate(row):
                    quotient, remainder = divmod(value, divisor)
                    if remainder:
                        return False
                    row[j] = quotient
        elif any(value for row in core for value in row):
            return False
    if (not certificate_equal(certificate['coordinate_divisor'], divisor)
            or not certificate_equal(certificate['vertex_links'], links)
            or not certificate_equal(certificate['core_coordinates'], core)):
        return False
    query = _coordinates(prepared, core, check)
    link_disks, link_spheres = vertex_link_totals(prepared, links, check)
    proof = certificate['query']
    if reduced and not divisor:
        if proof is not None:
            return False
        core_rows = []
    else:
        if (type(proof) is not dict or set(proof) !=
                {'boundary_transversal', 'surface', 'double', 'topology_spectrum'}):
            return False
        size, pairings = _arc_system(prepared, query, boundary=True, check=check)
        boundary = proof['boundary_transversal']
        if not verify_orbit_transversal_certificate(size, pairings, boundary, check=check):
            return False
        marks = [[encoded_integer(value) for value in interval]
                 for interval in boundary['representative_intervals']]
        for scale, field in ((1, 'surface'), (2, 'double')):
            check()
            system = topology_weight_system(prepared, query, marks, scale=scale, check=check)
            if not verify_weighted_orbit_certificate(system['size'], system['pairings'],
                    system['weights'], proof[field], dimension=2, check=check):
                return False
        if not verify_topology_spectrum(proof['surface']['histogram'],
                proof['double']['histogram'], proof['topology_spectrum'], check=check):
            return False
        core_rows = _decoded_rows(proof['topology_spectrum'])
    summary = certificate['summary']
    summary_keys = {'components', 'orientable_components', 'nonorientable_components',
                    'boundary_components', 'euler_characteristic', 'topology_spectrum'}
    if type(summary) is not dict or set(summary) != summary_keys:
        return False
    if not verify_scaled_spectrum(core_rows, divisor, summary['topology_spectrum'],
            vertex_link_disks=link_disks, vertex_link_spheres=link_spheres, check=check):
        return False
    rows = _decoded_rows(summary['topology_spectrum'])
    # Independent total reconstruction; do not call spectrum_summary.
    totals = [0, 0, 0, 0, 0]
    for row in rows:
        check()
        amount = row['multiplicity']
        totals[0] += amount
        totals[1 if row['orientable'] else 2] += amount
        totals[3] += amount * row['boundary_components']
        totals[4] += amount * row['chi']
    if totals[4] != analysed['euler_characteristic']:
        return False
    expected = dict(zip(('components', 'orientable_components', 'nonorientable_components',
                         'boundary_components', 'euler_characteristic'), totals))
    expected['topology_spectrum'] = rows
    check()
    return certificate_equal(summary, expected)
