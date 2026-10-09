"""Bounded native search for a source-certified normal meridian candidate.

Try the primitive integral cocycle, then a bounded prelude of alternative
tree gauges, then optional span minimization and any requested later trees. Source-bound
connectedness witnesses avoid orbit searches for these two restricted
families. Failure of the tested seeds says nothing about knottedness.
"""
from .diagram import Diagram
from .diagram_exterior import diagram_exterior
from .normal_cocycle import rank_one_cocycle_seed, _Budget, CocycleLimit
from .cocycle_span import minimize_cocycle_span
from .cocycle_trees import cocycle_tree_candidates
from .normal_cocycle_verify import inspect_cocycle_certificate
from .normal_surface_geometry import NormalOrbitError


def normal_seed_decide(diagram, *, optimize=True, max_work=2000000,
                       max_cycles=None, tree_trials=4, check=lambda: None):
    """Return UNKNOT with a native source certificate, or INCONCLUSIVE.

    The shared work allowance covers construction, cocycle extraction, all
    tree trials, connectedness/Euler checks and span optimization. It is a deterministic
    guard-count allowance, not a count of bit operations or a time limit.
    max_cycles is retained and validated for compatibility; these certificates
    require no interval-orbit cycles, so even a zero cycle allowance suffices.
    """
    if type(optimize) is not bool:
        raise ValueError('optimize must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    if type(tree_trials) is not int or tree_trials < 0:
        raise ValueError('tree_trials must be a nonnegative integer')
    budget = _Budget(check, max_work)
    stats, stages = {}, []
    try:
        budget.tick()
        source = Diagram.from_pd(diagram.pd)
        raw = diagram_exterior(source, check=budget.tick)
        seed = rank_one_cocycle_seed(raw, check=budget.tick)
        stats['cocycle'] = seed['stats']
        def evaluate(stage, heights, coordinates, span=None, candidate=None):
            budget.tick()
            certificate = dict(schema='diagram-cocycle-disc-v1', input_pd=[list(row) for row in source.pd],
                               triangulation=raw, heights=heights, coordinates=coordinates,
                               span_certificate=span)
            if candidate is not None and candidate['euler_characteristic'] != 1:
                # A miss emits no positive proof. The original class was
                # independently checked at the raw stage; this construction
                # changes only its tree gauge and validates normal matching.
                answer = dict(components=1, orientable_components=1,
                              euler_characteristic=candidate['euler_characteristic'],
                              normal_pieces=candidate['normal_pieces'], compressing_discs=0,
                              connectivity='zero-tree')
            else:
                answer = inspect_cocycle_certificate(source, certificate, check=budget.tick)
                if answer is None:
                    raise ArithmeticError('source-bound cocycle connectivity replay failed')
            entry = dict(stage=stage, status='COMPLETE', **answer)
            if candidate is not None:
                entry.update({k: candidate[k] for k in ('trial', 'root', 'randomized')})
            stages.append(entry)
            if answer['compressing_discs']:
                budget.tick()
                return dict(status='UNKNOT', method='native-normal-cocycle', certificate=certificate,
                            stats=stats, stages=stages, work=budget.work)
            return None

        result = evaluate('raw', seed['heights'], seed['coordinates'])
        if result is not None:
            return result
        candidates = iter(cocycle_tree_candidates(raw, seed['heights'], trials=tree_trials, check=budget.tick))
        tree_stats = dict(attempts=0, duplicates=0, candidates=0)
        if tree_trials:
            stats['tree_search'] = tree_stats

        def tree_attempt():
            candidate = next(candidates)
            tree_stats['attempts'] += 1
            if candidate['duplicate']:
                tree_stats['duplicates'] += 1
                return None
            tree_stats['candidates'] += 1
            return evaluate('tree', candidate['heights'], candidate['coordinates'], candidate=candidate)

        # Bound the cheap prelude. Additional requested trees run only after
        # the exact span solver has had its chance, sharing the same budget.
        for _ in range(min(4, tree_trials)):
            result = tree_attempt()
            if result is not None:
                return result
        if optimize:
            optimized = minimize_cocycle_span(seed['vertices'], seed['heights'], check=budget.tick)
            stats['optimization'] = optimized['stats']
            result = evaluate('optimized', seed['heights'], optimized['coordinates'], optimized['certificate'])
            if result is not None:
                return result
        for _ in range(4, tree_trials):
            result = tree_attempt()
            if result is not None:
                return result
        reason = 'the tested cocycle seeds contain no certified compressing disc'
    except (CocycleLimit, NormalOrbitError) as exc:
        reason = str(exc)
    return dict(status='INCONCLUSIVE', method='native-normal-cocycle', reason=reason,
                stats=stats, stages=stages, work=budget.work)
