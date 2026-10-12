"""Consequences for a CERTIFIED orientable interval bundle over a base surface.

No extraction or 3-dimensional recognition is performed here. MIT-0.
"""
from .surfaces import Surface


def orientation_bundle_summary(base: Surface) -> dict:
    """The unique interval bundle with orientable total space, up to isomorphism.

    The base description must come from an actual certified bundle. In
    particular, a spherical total boundary alone never authenticates this input.
    """
    if base.orientable:
        horizontal = [(base.genus_or_crosscaps, base.boundary, 2)]
    else:
        horizontal = [(1-base.chi-base.boundary, 2*base.boundary, 1)]
    if base.boundary > 0:
        total_boundary = [(1-base.chi, 1)]
        handlebody_genus = 1-base.chi
    elif base.orientable:
        total_boundary = [(base.genus_or_crosscaps, 2)]
        handlebody_genus = None
    else:
        total_boundary = [(1-base.chi, 1)]
        handlebody_genus = None
    return {'horizontal_surfaces_genus_boundary_multiplicity': horizontal,
            'total_boundary_genus_multiplicity': total_boundary,
            'handlebody_genus': handlebody_genus,
            'is_ball_given_certified_bundle':
                base.orientable and base.boundary == 1 and base.chi == 1}
