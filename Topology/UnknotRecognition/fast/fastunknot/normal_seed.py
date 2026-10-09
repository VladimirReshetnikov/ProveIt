"""Bounded native search for a source-certified cocycle unknot witness.

Try the primitive integral cocycle, then a bounded prelude of alternative
tree gauges, then optional span minimization and any requested later trees.
Finally try bounded extrema in the certified minimum-span face. Source-bound
connectedness witnesses avoid orbit searches for these restricted families.
Failure of the tested seeds says nothing about knottedness.
Primitive connected annuli can be capped on the exterior boundary; their
certificates distinguish them from normal discs.
"""
from .diagram import Diagram
from .diagram_exterior import diagram_exterior
from .normal_cocycle import rank_one_cocycle_seed, _Budget, CocycleLimit
from .cocycle_span import minimize_cocycle_span
from .cocycle_trees import cocycle_tree_candidates
from .cocycle_face import cocycle_face_candidates
from .normal_cocycle_verify import inspect_cocycle_certificate
from .normal_surface_geometry import NormalOrbitError, _prepare, _coordinates


def normal_seed_decide(diagram, *, optimize=True, annulus=True, max_work=2000000,
                       max_cycles=None, tree_trials=4, face_roots=0, check=lambda: None):
    """Return UNKNOT with a source-bound disc/annulus proof, or INCONCLUSIVE.

    The shared work allowance covers construction, cocycle extraction, all
    tree and optimal-face trials, connectedness/Euler checks and span
    optimization. It is a deterministic guard-count allowance, not a count
    of bit operations or a time limit.
    max_cycles is retained and validated for compatibility; these certificates
    require no interval-orbit cycles, so even a zero cycle allowance suffices.
    face_roots defaults to zero: optional face discovery adds coverage but
    was slower than the existing complete fallback on measured cases.
    """
    if type(optimize) is not bool:
        raise ValueError('optimize must be bool')
    if type(annulus) is not bool:
        raise ValueError('annulus must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    if type(tree_trials) is not int or tree_trials < 0:
        raise ValueError('tree_trials must be a nonnegative integer')
    if type(face_roots) is not int or face_roots < 0:
        raise ValueError('face_roots must be a nonnegative integer')
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
            positive_euler = (0, 1) if annulus else (1,)
            if candidate is not None and candidate['euler_characteristic'] not in positive_euler:
                # A miss emits no positive proof. The original class was
                # independently checked at the raw stage; this construction
                # changes only its gauge and validates normal matching. A
                # face candidate also replays the original span optimum.
                answer = dict(components=1, orientable_components=1,
                              euler_characteristic=candidate['euler_characteristic'],
                              normal_pieces=candidate['normal_pieces'], compressing_discs=0,
                              connectivity='minimum-span' if span is not None else 'zero-tree')
            else:
                answer = inspect_cocycle_certificate(source, certificate, check=budget.tick)
                if answer is None:
                    raise ArithmeticError('source-bound cocycle connectivity replay failed')
            entry = dict(stage=stage, status='COMPLETE', **answer)
            if candidate is not None:
                keys = ('root_trial', 'root', 'direction') if stage == 'face' else ('trial', 'root', 'randomized')
                entry.update({k: candidate[k] for k in keys})
            stages.append(entry)
            capped_annulus = annulus and answer['euler_characteristic'] == 0
            if capped_annulus:
                # The independent inspection above establishes every
                # annulus-cap hypothesis. Only the witness tag changes;
                # compressing_discs remains zero for the stored surface.
                certificate['schema'] = 'diagram-cocycle-annulus-v1'
                entry['unknot_witness'] = 'annulus-cap'
            if answer['compressing_discs'] or capped_annulus:
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
        if optimize and face_roots:
            prepared = _prepare(raw, budget.tick)
            face_stats = dict(candidates=0)
            stats['face_search'] = face_stats
            for candidate in cocycle_face_candidates(seed['vertices'], seed['heights'],
                    optimized['certificate'], roots=face_roots, check=budget.tick):
                face_stats['candidates'] += 1
                analysed = _coordinates(prepared, candidate['coordinates'], budget.tick)
                candidate.update(euler_characteristic=analysed['euler_characteristic'],
                                 normal_pieces=analysed['normal_disks'])
                result = evaluate('face', seed['heights'], candidate['coordinates'],
                                  candidate['certificate'], candidate)
                if result is not None:
                    return result
        reason = 'the tested cocycle seeds contain no certified compressing disc'
    except (CocycleLimit, NormalOrbitError) as exc:
        reason = str(exc)
    return dict(status='INCONCLUSIVE', method='native-normal-cocycle', reason=reason,
                stats=stats, stages=stages, work=budget.work)
