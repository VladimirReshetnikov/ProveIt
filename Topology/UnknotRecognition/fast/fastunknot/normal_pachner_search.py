"""Optional diagram-bound positive certificates from exhaustive local search.

The search can exhaust its declared finite Pachner/cochain family, but this
does not exclude discs outside that family.  Only a separately replayed
essential normal-disc component produces UNKNOT.  All other outcomes are
INCONCLUSIVE and can be passed to the maintained complete recognizer.
"""
from copy import deepcopy

from .diagram import Diagram
from .diagram_exterior import diagram_exterior
from .boundary_shellings import shell_boundary
from .normal_cocycle import rank_one_cocycle_seed, _Budget, CocycleLimit
from .cocycle_span import minimize_cocycle_span
from .normal_surface_geometry import NormalOrbitError
from .normal_transport_verify import (
    verify_transport_disk_certificate, _callback_safe_call,
)
from .pachner_commitments import search_pachner_endpoints
from .pachner_regions import search_pachner_regions
from .pachner_cover_search import search_pachner_cover


def pachner_seed_decide(diagram, *, max_upward=0, max_region_size=None,
                       max_components=1, method='sleep', shellings=False,
                       optimize=False, max_nodes=10000, max_work=2000000,
                       max_cycles=None, check=lambda: None):
    """Build the source exterior, search, and replay a transported disc.

    max_upward counts all 2--3 moves, not height above the starting size.
    max_region_size, when supplied, restricts the allowed initial footprint
    to a cover of that size with at most max_components components.
    The cooperative work allowance includes preparation and positive replay.
    """
    return _callback_safe_call(_pachner_seed_decide, check, diagram,
        max_upward=max_upward, max_region_size=max_region_size,
        max_components=max_components, method=method, shellings=shellings,
        optimize=optimize, max_nodes=max_nodes, max_work=max_work,
        max_cycles=max_cycles)


def _pachner_seed_decide(diagram, *, max_upward, max_region_size,
                        max_components, method, shellings, optimize,
                        max_nodes, max_work, max_cycles, check):
    if type(shellings) is not bool or type(optimize) is not bool:
        raise ValueError('shellings and optimize must be bool')
    for name, value in (('max_upward', max_upward),
                        ('max_components', max_components)):
        if type(value) is not int or value < 0:
            raise ValueError(name + ' must be a nonnegative integer')
    for name, value in (('max_region_size', max_region_size),
                        ('max_nodes', max_nodes), ('max_cycles', max_cycles)):
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError(name + ' must be a nonnegative integer or None')
    if method not in ('sleep', 'commitments', 'naive'):
        raise ValueError('unknown search method')
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
            optimum = minimize_cocycle_span(seed['vertices'], heights,
                                            check=budget.tick)
            potentials = dict(zip(optimum['certificate']['vertex_ids'],
                                  optimum['certificate']['potential']))
            heights = [[h+potentials[v] for h, v in zip(hs, vs)]
                       for hs, vs in zip(heights, seed['vertices'])]
            stats['optimization'] = optimum['stats']
        source_heights = deepcopy(heights)
        common = dict(max_upward=max_upward, method=method, max_nodes=max_nodes,
                      seek_disc=True, check=budget.tick)
        if max_region_size is None:
            search = search_pachner_endpoints(raw, heights,
                                              max_cycles=max_cycles, **common)
        else:
            # The source endpoint belongs to every cover. Probe it before
            # constructing a potentially large index, then share the node
            # allowance with the full region search after an ordinary miss.
            probe=search_pachner_endpoints(raw,heights,active_initial_tetrahedra=[],
                max_upward=0,method=method,max_nodes=None if max_nodes is None else min(1,max_nodes),
                max_cycles=max_cycles,seek_disc=True,check=budget.tick)
            stats['root_probe']=probe['stats']
            if probe['status']=='DISC_FOUND':search=probe
            else:
                remaining=None if max_nodes is None else max_nodes-probe['stats']['nodes']
                if remaining==0:
                    search=dict(status='INCONCLUSIVE',reason='Pachner node allowance exhausted',stats=dict(nodes=0))
                else:
                    common['max_nodes']=remaining
                    call=search_pachner_cover if method in ('sleep','naive')else search_pachner_regions
                    search=call(raw,heights,max_region_size=max_region_size,
                        max_components=max_components,max_cycles=max_cycles,**common)
        stats['search'] = search['stats']
        if search['status'] == 'DISC_FOUND':
            local = search['certificate']
            proof = dict(schema='diagram-transport-disc-v1',
                input_pd=[list(row) for row in source.pd],
                source_triangulation=original, shelling=shelling,
                source_heights=source_heights, steps=local['moves'],
                coordinates=local['coordinates'],
                disc_certificate=local['disc_certificate'])
            if not verify_transport_disk_certificate(source, proof,
                                                      check=budget.tick):
                raise ArithmeticError('diagram-bound Pachner disc failed replay')
            return dict(status='UNKNOT', method='native-pachner-search',
                        certificate=proof, bounded_search_status=search['status'],
                        stats=stats, work=budget.work)
        reason = search.get('reason',
            'the declared finite Pachner/cochain family has no certified disc')
        bounded_status = search['status']
    except (CocycleLimit, NormalOrbitError) as exc:
        reason, bounded_status = str(exc), 'INCONCLUSIVE'
    return dict(status='INCONCLUSIVE', method='native-pachner-search',
                reason=reason, bounded_search_status=bounded_status,
                stats=stats, work=budget.work)
