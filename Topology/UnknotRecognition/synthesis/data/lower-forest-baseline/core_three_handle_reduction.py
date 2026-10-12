"""Source-authenticated removal of core three-handles by a dual boundary forest.

The enclosing parallelity proof authenticates all source handles. A two-handle
may cancel a three-handle precisely when one of its two dual endpoints is that
remaining three-handle and its other endpoint is already on the boundary.
"""
from collections import deque
from heapq import heapify, heappop, heappush

from .core_handlebody import _forest
from .normal_surface_geometry import _prepare, _coordinates, _EDGES


def _raw_costs(core, check):
    """Exact uncapped passage counts outside the fixed lower spanning forest."""
    tree, _ = _forest(core, check)
    tree = set(tree)
    costs = {}
    for handle in core['handles2']:
        check()
        cost = 0
        for flag in handle['cycle']:
            check()
            cost += flag['dimension'] == 1 and flag['handle'] not in tree
        costs[handle['id']] = cost
    return costs


def _dual_moves(ends, vertices, costs, check):
    """Root-growing maximum tree when costs are supplied; legacy FIFO otherwise.

    Endpoints and vertices belong to an already authenticated dual graph.
    A heap holds the exposed cut edges: this is maximum-weight Prim, including
    parallel edges and stale records from loops. It optimizes additive cost,
    not whether later one/two cancellation will finish.
    """
    incident = {v: [] for v in vertices}
    degree, owner = {}, {}
    for e, pair in ends.items():
        check()
        degree[e], owner[e] = 0, 0
        for v in pair:
            if v is not None:
                incident[v].append(e)
                degree[e] += 1
                owner[e] ^= v
    if costs is None:
        queue = deque(e for e in ends if degree[e] == 1)
        push, pop = queue.append, queue.popleft
    else:
        queue = [(-costs[e], e) for e in ends if degree[e] == 1]
        heapify(queue)
        push = lambda e: heappush(queue, (-costs[e], e))
        pop = lambda: heappop(queue)[1]
    alive, remaining = set(incident), set(ends)
    moves = []
    while queue:
        check()
        e = pop()
        if e not in remaining or degree[e] != 1:
            continue
        v = owner[e]
        moves.append(dict(two_handle=e, three_handle=v))
        remaining.remove(e)
        alive.remove(v)
        for other in incident[v]:
            check()
            if other not in remaining:
                continue
            degree[other] -= 1
            owner[other] ^= v
            if degree[other] == 1:
                push(other)
    return None if alive else (moves, remaining)


def reduce_core_three_handles(geometry, *, strategy='queue', check=lambda: None):
    """Return (reduced_geometry, certificate), or None if the forest stalls.

    ``max_weight`` minimizes retained raw passage count outside the existing
    lower forest. ``queue`` preserves the original deterministic selector.
    Both emit the same independently checked geometric certificate format.
    The additive objective follows reports 99 and 100; no tree search occurs.
    """
    check()
    if type(strategy) is not str or strategy not in ('queue', 'max_weight'):
        raise ValueError('strategy must be queue or max_weight')
    core = geometry['core']
    source = _prepare(geometry['source'], check)
    normal = _coordinates(source, geometry['coordinates'], check)
    by_vertex = {h['vertex']: h['id'] for h in core['handles3']}
    ends, records = {}, []
    for h in core['handles2']:
        check()
        t, edge = divmod(h['edge'], 6)
        a, b = _EDGES[edge]
        endpoints = [by_vertex.get(source['vertex_roots'][4*t+v]) for v in (a,b)]
        weight = normal['weights'][h['edge']]
        if weight:
            if h['rank'] == 0:
                endpoints[1] = None
            elif h['rank'] == weight:
                endpoints[0] = None
            else:
                raise ArithmeticError('non-extreme core edge gap')
        elif h['rank'] != 0:
            raise ArithmeticError('invalid zero-weight edge gap')
        ends[h['id']] = endpoints
        records.append(dict(two_handle=h['id'], ends=endpoints))
    costs = _raw_costs(core, check) if strategy == 'max_weight' else None
    plan = _dual_moves(ends, by_vertex.values(), costs, check)
    if plan is None:
        return None
    moves, remaining = plan
    kept = [h['id'] for h in core['handles2'] if h['id'] in remaining]
    reduced = dict(geometry, core=dict(core, handles3=[], handles2=[
        dict(core['handles2'][old], id=new) for new, old in enumerate(kept)]))
    proof = dict(schema='core-three-handle-reduction-v1', dual_endpoints=records,
                 cancellations=moves, surviving_two_handles=kept)
    check()
    return reduced, proof
