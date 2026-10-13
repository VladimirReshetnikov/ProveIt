"""Independent source-bound replay of a bounded Pachner cochain endpoint.

This module imports no move, transport, search, or disc-count producer.
An endpoint certificate authenticates a reachable cochain state.  An optional
disc certificate additionally proves an essential disc in the supplied source
manifold.  No correspondence to an unspecified knot diagram is inferred.
"""
from .cocycle_transport_verify import (
    _shield_callback, _read_heights, _check_signed_edges,
    verify_cocycle_transport,
)
from .integer_codec import encoded_integer, certificate_equal
from .normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from .normal_disk_kernel import verify_normal_disk_count_certificate


@_shield_callback
def inspect_pachner_endpoint(triangulation, heights, certificate, *,
                              check=lambda: None):
    """Return a replayed endpoint summary, or None on malformed evidence."""
    check()
    fields = {'schema', 'max_upward', 'active_initial_tetrahedra',
              'moves', 'coordinates', 'disc_certificate'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] != 'pachner-cochain-endpoint-v1'
            or type(certificate['max_upward']) is not int
            or certificate['max_upward'] < 0
            or type(certificate['moves']) is not list):
        return None
    try:
        prepared = _prepare(triangulation, check)
        n = len(prepared['tetrahedra'])
        active = certificate['active_initial_tetrahedra']
        if (type(active) is not list or active != sorted(set(active))
                or any(type(i) is not int or not 0 <= i < n for i in active)):
            return None
        allowed = set(active)
        ancestry = list(range(n))
        consumed_initial = set()
        h = _read_heights(heights, n, check)
        if h is None or not _check_signed_edges(prepared, h, check):
            return None
        raw, upward, downward = triangulation, 0, 0
        for step in certificate['moves']:
            check()
            if (type(step) is not dict
                    or set(step) != {'triangulation', 'transport'}):
                return None
            after, proof = step['triangulation'], step['transport']
            if not verify_cocycle_transport(raw, h, after, proof, check=check):
                return None
            if proof['move']['schema'] == 'pachner-23-v1':
                upward += 1
                move = proof['move']
                a, f = move['tetrahedron'], move['face']
                used = {a, raw['tetrahedra'][a][f]['tetrahedron']}
                new_count = 3
            else:
                downward += 1
                used = {item['tetrahedron'] for item in proof['move']['region']}
                new_count = 2
            original = {ancestry[i] for i in used if ancestry[i] is not None}
            if not original <= allowed:
                return None
            consumed_initial.update(original)
            ancestry = [name for i, name in enumerate(ancestry) if i not in used]
            ancestry.extend([None]*new_count)
            if upward > certificate['max_upward']:
                return None
            raw, h = after, proof['heights']
        prepared = _prepare(raw, check)
        analysed = _coordinates(prepared, certificate['coordinates'], check)
        # Reconstruct coherent coordinates independently of local_coordinates.
        expected = []
        for row in h:
            check()
            levels = sorted(set(row))
            coordinates = [0] * 7
            for lo, hi in zip(levels, levels[1:]):
                low = {v for v in range(4) if row[v] <= lo}
                if len(low) == 1:
                    coordinates[next(iter(low))] += hi-lo
                elif len(low) == 3:
                    coordinates[next(v for v in range(4) if v not in low)] += hi-lo
                elif len(low) == 2:
                    pair = frozenset(low)
                    pairs = (frozenset((0, 1)), frozenset((0, 2)), frozenset((0, 3)))
                    complement = frozenset(range(4))-pair
                    q = next(i for i, p in enumerate(pairs)
                             if p == pair or p == complement)
                    coordinates[4+q] += hi-lo
            expected.append(coordinates)
        if not certificate_equal(analysed['rows'], expected):
            return None
        disc = certificate['disc_certificate']
        has_disc = False
        if disc is not None:
            if not verify_normal_disk_count_certificate(
                    raw, expected, disc, check=check):
                return None
            has_disc = encoded_integer(disc['compressing_disk_components']) > 0
            if not has_disc:
                return None
        return dict(triangulation=raw, heights=h, coordinates=expected,
                    upward_moves=upward, downward_moves=downward,
                    consumed_initial_tetrahedra=sorted(consumed_initial),
                    euler_characteristic=analysed['euler_characteristic'],
                    contains_compressing_disk=has_disc)
    except (NormalOrbitError, ValueError, TypeError, KeyError, IndexError,
            StopIteration):
        return None


def verify_pachner_endpoint(triangulation, heights, certificate, *,
                             check=lambda: None):
    """Check reachability and any included essential-disc claim."""
    return inspect_pachner_endpoint(triangulation, heights, certificate,
                                    check=check) is not None
