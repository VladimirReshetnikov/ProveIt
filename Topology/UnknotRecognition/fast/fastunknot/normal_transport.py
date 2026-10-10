"""Experimental source-bound cocycle descent for unknot certificates.

This is an optional positive-certificate search.  Its final transported
coherent surface is checked by the general compressed component kernel.
A failed search is INCONCLUSIVE; the maintained recognition defaults are
unchanged.  No upper bound on upward escape depth is assumed.
"""

from copy import deepcopy

from .diagram import Diagram
from .diagram_exterior import diagram_exterior
from .boundary_shellings import shell_boundary
from .normal_cocycle import rank_one_cocycle_seed, _Budget, CocycleLimit
from .cocycle_span import minimize_cocycle_span
from .cocycle_transport import descend_cocycle
from .normal_disk_kernel import normal_compressing_disk_count
from .normal_transport_verify import (
    verify_transport_disk_certificate, _callback_safe_call,
)
from .normal_surface_geometry import NormalOrbitError


def transport_seed_decide(diagram, *, strategy='score', shellings=False,
                          optimize=False, max_moves=None, max_work=2000000,
                          max_cycles=None, check=lambda: None):
    """Search a single deterministic downward epoch and verify its final disc.

    max_work is a shared cooperative guard allowance, not bit operations.
    max_cycles limits the one terminal component query.  optimize selects
    the existing minimum-span representative before descent; shellings runs
    the existing certified boundary preprocessor.  No cohomology is solved
    after a Pachner move.  All stages and positive replay share max_work.
    """
    return _callback_safe_call(_transport_seed_decide, check, diagram,
        strategy=strategy, shellings=shellings, optimize=optimize,
        max_moves=max_moves, max_work=max_work, max_cycles=max_cycles)


def _transport_seed_decide(diagram, *, strategy, shellings, optimize,
                           max_moves, max_work, max_cycles, check):
    if type(shellings) is not bool or type(optimize) is not bool:
        raise ValueError('shellings and optimize must be bool')
    if strategy not in ('score', 'first'):
        raise ValueError('strategy must be score or first')
    if max_moves is not None and (type(max_moves) is not int or max_moves < 0):
        raise ValueError('max_moves must be a nonnegative integer or None')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    budget = _Budget(check, max_work)
    stats = {}
    try:
        budget.tick()
        source = Diagram.from_pd(diagram.pd)
        original = diagram_exterior(source, check=budget.tick)
        raw, shelling = original, None
        if shellings:
            reduced = shell_boundary(raw, check=budget.tick)
            raw = reduced['triangulation']
            shelling = dict(triangulation=raw, moves=reduced['moves'])
            stats['shellings'] = reduced['stats']
        seed = rank_one_cocycle_seed(raw, check=budget.tick)
        heights = seed['heights']
        stats['seed'] = seed['stats']
        if optimize:
            optimum = minimize_cocycle_span(seed['vertices'], heights, check=budget.tick)
            potential = dict(zip(optimum['certificate']['vertex_ids'],
                                 optimum['certificate']['potential']))
            heights = [[h+potential[v] for h, v in zip(hs, vs)]
                       for hs, vs in zip(heights, seed['vertices'])]
            stats['optimization'] = optimum['stats']
        initial_heights = deepcopy(heights)
        descent = descend_cocycle(raw, heights, strategy=strategy, max_moves=max_moves,
                                  check=budget.tick)
        stats['descent'] = descent['stats']
        query = normal_compressing_disk_count(descent['triangulation'],
            descent['coordinates'], max_cycles=max_cycles, record_certificate=True,
            check=budget.tick)
        stats['components'] = query['stats']
        if query['status'] != 'COMPLETE':
            return dict(status='INCONCLUSIVE', method='native-cocycle-transport',
                        reason=query['reason'], stats=stats, work=budget.work)
        count = query['compressing_disk_components']
        if count:
            proof = dict(schema='diagram-transport-disc-v1',
                input_pd=[list(row) for row in source.pd], source_triangulation=original,
                shelling=shelling, source_heights=initial_heights,
                steps=descent['moves'], coordinates=descent['coordinates'],
                disc_certificate=query['certificate'])
            if not verify_transport_disk_certificate(source, proof, check=budget.tick):
                raise ArithmeticError('source-bound transported disc failed replay')
            return dict(status='UNKNOT', method='native-cocycle-transport',
                        certificate=proof, stats=stats, work=budget.work,
                        compressing_disk_components=count)
        reason = 'the final transported coherent surface has no compressing-disc component'
    except (CocycleLimit, NormalOrbitError) as exc:
        reason = str(exc)
    return dict(status='INCONCLUSIVE', method='native-cocycle-transport',
                reason=reason, stats=stats, work=budget.work)
