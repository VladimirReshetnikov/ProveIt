"""Independent checks of covered endpoints and strict Pachner descents.

This module imports no region enumerator, search, move, or transport producer.
It independently counts the chosen cover's induced dual-graph components and
delegates geometric source replay to the maintained endpoint verifier.
"""
from .cocycle_transport_verify import _shield_callback
from .normal_surface_geometry import _prepare, NormalOrbitError
from .pachner_commitments_verify import inspect_pachner_endpoint


@_shield_callback
def inspect_pachner_cover(triangulation, heights, certificate, *,
                          max_region_size, max_components=1, max_upward=None,
                          check=lambda: None):
    """Return a source-replayed summary, or None for malformed or overscope evidence."""
    for value in (max_region_size, max_components):
        if type(value) is not int or value < 0:
            return None
    if max_upward is not None and (type(max_upward) is not int or max_upward < 0):
        return None
    replay = inspect_pachner_endpoint(triangulation, heights, certificate, check=check)
    if replay is None:
        return None
    if max_upward is not None and replay['upward_moves'] > max_upward:
        return None
    cover = certificate['active_initial_tetrahedra']
    if len(cover) > max_region_size:
        return None
    try:
        rows = _prepare(triangulation, check)['tetrahedra']
        remaining, components = set(cover), 0
        while remaining:
            check()
            components += 1
            pending = [remaining.pop()]
            while pending:
                check()
                cell = pending.pop()
                neighbours = {entry['tetrahedron'] for entry in rows[cell]
                              if entry is not None}
                reached = remaining & neighbours
                remaining.difference_update(reached)
                pending.extend(reached)
        if components > max_components:
            return None
        # Endpoint replay checks consumption containment independently.  Retain
        # the concrete cover, which may be larger than the actual consumption.
        return dict(replay, cover=list(cover), cover_components=components)
    except (NormalOrbitError, TypeError, ValueError, KeyError, IndexError):
        return None


def verify_pachner_cover(triangulation, heights, certificate, **options):
    return inspect_pachner_cover(triangulation, heights, certificate, **options) is not None


@_shield_callback
def inspect_pachner_descent(triangulation, heights, certificate, *,
                            max_upward, max_region_size=None, check=lambda: None):
    """Replay a connected-cover certificate and verify strict tetrahedron descent."""
    if type(max_upward) is not int or max_upward < 0:
        return None
    try:
        n = len(_prepare(triangulation, check)['tetrahedra'])
    except (NormalOrbitError, TypeError, ValueError, KeyError, IndexError):
        return None
    radius = min(n, 3*max_upward+3) if max_region_size is None else max_region_size
    replay = inspect_pachner_cover(triangulation, heights, certificate,
        max_region_size=radius, max_components=1, max_upward=max_upward, check=check)
    if replay is None:
        return None
    final = len(replay['triangulation']['tetrahedra'])
    if final >= n or replay['downward_moves'] <= replay['upward_moves']:
        return None
    if final != n+replay['upward_moves']-replay['downward_moves']:
        return None
    return dict(replay, initial_tetrahedra=n, final_tetrahedra=final)


def verify_pachner_descent(triangulation, heights, certificate, **options):
    return inspect_pachner_descent(triangulation, heights, certificate, **options) is not None
