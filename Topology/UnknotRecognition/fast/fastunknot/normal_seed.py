"""Bounded native search for a source-certified normal meridian candidate.

Try a primitive integral cocycle surface first. If it has no verified disc,
optionally minimize its span before a second Euler check. Source-bound
connectedness witnesses avoid orbit searches for these two restricted
families. Failure of either seed says nothing about knottedness.
"""
from .diagram import Diagram
from .diagram_exterior import diagram_exterior
from .normal_cocycle import rank_one_cocycle_seed, _Budget, CocycleLimit
from .cocycle_span import minimize_cocycle_span
from .normal_cocycle_verify import inspect_cocycle_certificate
from .normal_surface_geometry import NormalOrbitError


def normal_seed_decide(diagram, *, optimize=True, max_work=2000000,
                       max_cycles=None, check=lambda: None):
    """Return UNKNOT with a native source certificate, or INCONCLUSIVE.

    The shared work allowance covers construction, cocycle extraction, both
    connectedness/Euler checks and span optimization. It is a deterministic
    guard-count allowance, not a count of bit operations or a time limit.
    max_cycles is retained and validated for compatibility; these certificates
    require no interval-orbit cycles, so even a zero cycle allowance suffices.
    """
    if type(optimize) is not bool:
        raise ValueError('optimize must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    budget = _Budget(check, max_work)
    stats, stages = {}, []
    try:
        budget.tick()
        source = Diagram.from_pd(diagram.pd)
        raw = diagram_exterior(source, check=budget.tick)
        seed = rank_one_cocycle_seed(raw, check=budget.tick)
        stats['cocycle'] = seed['stats']
        coordinates = seed['coordinates']
        span = None
        for stage in ('raw', 'optimized') if optimize else ('raw',):
            budget.tick()
            if stage == 'optimized':
                optimized = minimize_cocycle_span(seed['vertices'], seed['heights'], check=budget.tick)
                stats['optimization'] = optimized['stats']
                coordinates = optimized['coordinates']
                span = optimized['certificate']
            certificate = dict(schema='diagram-cocycle-disc-v1', input_pd=[list(row) for row in source.pd],
                               triangulation=raw, heights=seed['heights'], coordinates=coordinates,
                               span_certificate=span)
            answer = inspect_cocycle_certificate(source, certificate, check=budget.tick)
            if answer is None:
                raise ArithmeticError('source-bound cocycle connectivity replay failed')
            stages.append(dict(stage=stage, status='COMPLETE', **answer))
            if answer['compressing_discs']:
                budget.tick()
                return dict(status='UNKNOT', method='native-normal-cocycle', certificate=certificate,
                            stats=stats, stages=stages, work=budget.work)
        reason = 'the tested cocycle seeds contain no certified compressing disc'
    except (CocycleLimit, NormalOrbitError) as exc:
        reason = str(exc)
    return dict(status='INCONCLUSIVE', method='native-normal-cocycle', reason=reason,
                stats=stats, stages=stages, work=budget.work)
