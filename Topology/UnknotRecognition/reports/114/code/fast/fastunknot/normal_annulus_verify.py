"""A primitive connected annulus in a knot exterior certifies unknottedness.

The independent cocycle inspector proves source binding, orientability,
connectedness and primitivity. Euler zero then forces an annulus: a closed
torus has zero relative class in a knot exterior. Its primitive boundary
class rules out two essential parallel curves and two inessential curves.
Cap the unique inessential boundary circle on the boundary torus and round
inward to obtain an embedded compressing disc.

The certificate stores the annulus, not a normal vector for the capped disc.
"""
from .normal_cocycle_verify import inspect_cocycle_certificate


def inspect_annulus_certificate(diagram, certificate, *, check=lambda: None):
    """Return checked annulus data, or None; import no discovery routine."""
    check()
    if (type(certificate) is not dict
            or certificate.get('schema') != 'diagram-cocycle-annulus-v1'):
        return None
    surface = dict(certificate, schema='diagram-cocycle-disc-v1')
    summary = inspect_cocycle_certificate(diagram, surface, check=check)
    if summary is None or summary['euler_characteristic'] != 0:
        return None
    check()
    return dict(summary, unknot_witness='annulus-cap')
