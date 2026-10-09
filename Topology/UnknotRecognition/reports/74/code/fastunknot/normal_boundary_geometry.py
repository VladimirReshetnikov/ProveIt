"""Two additive intersection weights on compressed normal boundary curves."""
from .normal_surface_geometry import _arc_system


def boundary_weight_system(prepared, analysed, basis, check=lambda: None):
    """Use the boundary-only point ordering, never the surface edge offsets.

    The caller constructs or independently validates the two torus cycles.
    Each orbit is a simple boundary circle; its two weight parities detect
    essentiality on the torus. Zero-weight circles still count as orbits.
    """
    cycles = [set(cycle) for cycle in basis]
    size, pairings = _arc_system(prepared, analysed, boundary=True, check=check)
    offset, weights = 0, []
    for edge in sorted(prepared['boundary_incidence']):
        check()
        end = offset+analysed['weights'][edge]
        value = [int(edge in cycle) for cycle in cycles]
        if end > offset and any(value):
            weights.append((offset, end, value))
        offset = end
    if offset != size:
        raise ArithmeticError('boundary point order disagrees with arc system')
    return size, pairings, weights
