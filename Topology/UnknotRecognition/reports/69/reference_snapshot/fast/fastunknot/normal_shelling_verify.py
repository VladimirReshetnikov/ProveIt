"""Source-bound replay of shellings followed by a connected surface witness.

Only independent checkers are imported. The private source predicate binds
both triangulations through a canonical diagram exterior and legal moves;
no caller-supplied geometry or source-verification result is accepted.
"""
from .diagram_exterior_verify import verify_diagram_exterior
from .boundary_shellings_verify import verify_boundary_shellings
from .normal_cocycle_verify import _inspect_cocycle_source
from .normal_planar_verify import _inspect_planar_surface


def _details(certificate):
    fields = {'schema', 'source_triangulation', 'shellings', 'surface_certificate'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] != 'diagram-shelling-witness-v1'):
        return None
    def source_check(source, final, *, check):
        before = certificate['source_triangulation']
        return (verify_diagram_exterior(source, before, check=check)
                and verify_boundary_shellings(before, final, certificate['shellings'], check=check))
    def inspect(diagram, surface, *, check):
        return _inspect_cocycle_source(diagram, surface, source_check, check=check)
    return certificate['surface_certificate'], inspect


def inspect_shelling_cocycle(diagram, certificate, *, check=lambda: None):
    """Inspect an inner disc-schema surface; its Euler value need not be one."""
    check()
    parts = _details(certificate)
    if parts is None:return None
    surface, inspect = parts
    result = inspect(diagram, surface, check=check)
    return None if result is None else result[0]


def inspect_shelling_planar(diagram, certificate, *, check=lambda: None):
    check()
    parts = _details(certificate)
    if parts is None:return None
    surface, inspect = parts
    return _inspect_planar_surface(diagram, surface, inspect, check=check)


def verify_shelling_certificate(diagram, certificate, *, check=lambda: None):
    check()
    parts = _details(certificate)
    if parts is None:return False
    surface, inspect = parts
    if type(surface) is not dict:return False
    kind = surface.get('schema')
    if kind == 'diagram-cocycle-planar-v1':
        return _inspect_planar_surface(diagram, surface, inspect, check=check) is not None
    if kind not in ('diagram-cocycle-disc-v1', 'diagram-cocycle-annulus-v1'):
        return False
    normalized = dict(surface, schema='diagram-cocycle-disc-v1')
    result = inspect(diagram, normalized, check=check)
    return result is not None and result[0]['euler_characteristic'] == (0 if kind == 'diagram-cocycle-annulus-v1' else 1)
