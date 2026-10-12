"""Produce compact, independently replayable complete sector-ray lists."""

from bisect import bisect_left
from fractions import Fraction

from .normal_sector import build_sector_kernel, _source_hash
from .sector_envelope import sector_envelope_plan, sector_envelope_rays


def _encode(value):
    value = Fraction(value)
    return [value.numerator, value.denominator]


def certify_sector_enumeration(triangulation, allowed_types, *,
                              max_rays=None, check=lambda: None):
    """Return every non-link standard ray and a coverage certificate.

    This API accepts only matching nullity at most two.  It certifies the
    supplied triangulation and allowed sector; it does not identify a knot.
    A ray cap yields INCONCLUSIVE with no partial completeness certificate.
    """
    if max_rays is not None and (type(max_rays) is not int or max_rays < 0):
        raise ValueError('max_rays must be a nonnegative integer or None')
    kernel = build_sector_kernel(triangulation, allowed_types, check=check)
    plan_stats = {}
    plan = sector_envelope_plan(kernel, check=check, stats=plan_stats)
    if max_rays is not None and len(plan['parameters']) > max_rays:
        return dict(status='INCONCLUSIVE', reason='ray allowance exhausted',
                    stats=dict(kernel.stats, **plan_stats))
    ray_stats = {}
    rays = list(sector_envelope_rays(kernel, check=check,
                max_bases=max_rays, stats=ray_stats))
    proof = dict(schema='normal-sector-envelope-v1',
        source_sha256=_source_hash(triangulation),
        allowed_types=[list(pair) for pair in kernel.support],
        matching_dimension=plan['matching_dimension'],
        section_dimension=plan['section_dimension'],
        q_origin=None, q_direction=None, lower=None, upper=None,
        envelopes=[], rays=rays)
    if plan['section_dimension'] >= 0:
        proof.update(q_origin=[_encode(x) for x in plan['q_origin']],
            q_direction=[_encode(x) for x in plan['q_direction']],
            lower=_encode(plan['lower']), upper=_encode(plan['upper']))
    if plan['section_dimension'] == 1:
        vertices = {}
        for corner, vertex in enumerate(kernel.prepared['vertex_roots']):
            vertices.setdefault(vertex, []).append(corner)
        active_groups = {entry['vertex']: list(entry['corners'])
                         for entry in plan['groups']}
        direction = plan['q_direction']

        def slope(corner):
            potential = kernel.potentials[kernel.corner_class[corner]]
            return sum(x*y for x, y in zip(potential, direction))

        for vertex, corners in sorted(vertices.items()):
            check()
            active = active_groups.get(vertex, [corners[0]])
            slopes = [-slope(corner) for corner in active]
            brackets = [bisect_left(slopes, -slope(corner)) for corner in corners]
            proof['envelopes'].append(dict(vertex=vertex, corners=active,
                                            brackets=brackets))
    return dict(status='COMPLETE', coordinates=rays, certificate=proof,
                stats=dict(kernel.stats, **ray_stats),
                trust='all non-link standard rays in this supplied sector only')
