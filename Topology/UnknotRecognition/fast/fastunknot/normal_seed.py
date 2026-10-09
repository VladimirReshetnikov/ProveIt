"""Bounded native search for a source-certified normal meridian candidate.

Try a primitive integral cocycle surface first. If it has no verified disc,
optionally minimize its span before a second component query. Failure of
either restricted seed says nothing about knottedness.
"""
from .diagram import Diagram
from .diagram_exterior import diagram_exterior
from .normal_cocycle import rank_one_cocycle_seed, _Budget, CocycleLimit
from .cocycle_span import minimize_cocycle_span
from .normal_disk_kernel import normal_compressing_disk_count
from .normal_surface_geometry import NormalOrbitError


def normal_seed_decide(diagram, *, optimize=True, max_work=2000000,
                       max_cycles=None, check=lambda: None):
    """Return UNKNOT with a native source certificate, or INCONCLUSIVE.

    The shared work allowance covers construction, cocycle extraction, both
    optional component queries and span optimization. It is a deterministic
    guard-count allowance, not a count of bit operations or a time limit.
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
        for stage in ('raw', 'optimized') if optimize else ('raw',):
            budget.tick()
            if stage == 'optimized':
                optimized = minimize_cocycle_span(seed['vertices'], seed['heights'], check=budget.tick)
                stats['optimization'] = optimized['stats']
                coordinates = optimized['coordinates']
            answer = normal_compressing_disk_count(raw, coordinates, max_cycles=max_cycles,
                check=budget.tick, record_certificate=True)
            stages.append(dict(stage=stage, status=answer['status'],
                               compressing_discs=answer.get('compressing_disk_components'),
                               normal_pieces=sum(map(sum, coordinates))))
            if answer['status'] == 'COMPLETE' and answer['contains_compressing_disk']:
                certificate = dict(schema='diagram-normal-disc-v1', input_pd=[list(row) for row in source.pd],
                                   triangulation=raw, coordinates=coordinates,
                                   disc_certificate=answer['certificate'])
                from .normal_seed_verify import verify_normal_seed_certificate
                if not verify_normal_seed_certificate(source, certificate, check=budget.tick):
                    raise ArithmeticError('source-bound normal-disc replay failed')
                budget.tick()
                return dict(status='UNKNOT', method='native-normal-cocycle', certificate=certificate,
                            stats=stats, stages=stages, work=budget.work)
        reason = 'the tested cocycle seeds contain no certified compressing disc'
    except (CocycleLimit, NormalOrbitError) as exc:
        reason = str(exc)
    return dict(status='INCONCLUSIVE', method='native-normal-cocycle', reason=reason,
                stats=stats, stages=stages, work=budget.work)
