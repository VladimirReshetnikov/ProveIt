"""Exact enumeration of small regions in the initial tetrahedron dual graph.

A region is permission to consume original tetrahedra, not a requirement to
consume them all.  New tetrahedra born inside the region remain eligible.
The reverse search has one parent for each connected vertex set; it never
enumerates all orders in which the vertices of a region could be added.
"""

from .cocycle_transport_verify import _shield_callback, _CallbackAbort


def _limit(name, value):
    if type(value) is not int or value < 0:
        raise ValueError(name + ' must be a nonnegative integer')


def _graph(adjacency, check):
    if type(adjacency) not in (list, tuple):
        raise ValueError('adjacency must be a list or tuple')
    n = len(adjacency)
    graph = []
    for i, row in enumerate(adjacency):
        check()
        if type(row) not in (list, tuple, set, frozenset):
            raise ValueError('each adjacency row must be a finite collection')
        if any(type(v) is not int or not 0 <= v < n for v in row):
            raise ValueError('adjacency contains an invalid vertex')
        graph.append(frozenset(v for v in row if v != i))
    for i, row in enumerate(graph):
        check()
        if any(i not in graph[j] for j in row):
            raise ValueError('adjacency must be symmetric')
    return tuple(graph)


def _connected(graph, vertices, check):
    if not vertices:
        return False
    reached = {min(vertices)}
    todo = list(reached)
    while todo:
        check()
        v = todo.pop()
        new = (graph[v] & vertices) - reached
        reached.update(new)
        todo.extend(new)
    return len(reached) == len(vertices)


def _parent(graph, vertices, check):
    """Delete the largest non-root vertex whose deletion keeps connectivity."""
    root = min(vertices)
    for v in sorted(vertices - {root}, reverse=True):
        check()
        candidate = vertices - {v}
        if _connected(graph, candidate, check):
            return candidate
    raise ArithmeticError('a connected non-singleton set has no parent')


def _connected_sets(graph, max_size, permitted, after_root, check):
    for root in sorted(v for v in permitted if v > after_root):
        check()
        eligible = frozenset(v for v in permitted if v >= root)
        stack = [frozenset((root,))]
        while stack:
            check()
            current = stack.pop()
            yield tuple(sorted(current))
            if len(current) >= max_size:
                continue
            frontier = set().union(*(graph[v] for v in current))
            frontier.intersection_update(eligible)
            frontier.difference_update(current)
            for v in sorted(frontier, reverse=True):
                check()
                child = current | {v}
                if _parent(graph, child, check) == current:
                    stack.append(child)


def connected_regions(adjacency, max_size, *, check=lambda: None):
    """Yield every nonempty connected vertex set of size at most max_size once.

    For an n-vertex graph of maximum degree four, the number of yielded sets
    is at most n * (16**max_size - 1) / 15.  The algorithm has polynomial
    overhead per yielded set and uses no isomorphism or probabilistic hashes.
    Loops and repeated adjacency entries do not affect the sets.
    """
    _limit('max_size', max_size)
    graph = _graph(adjacency, check)
    if max_size:
        yield from _connected_sets(graph, min(max_size, len(graph)),
                                   frozenset(range(len(graph))), -1, check)


def footprint_regions(adjacency, max_size, max_components=1, *,
                      include_empty=True, check=lambda: None):
    """Yield each vertex set with the specified size/component bounds once.

    Components are selected in increasing order of their least vertex.  A
    new component must avoid the closed neighbourhood of every earlier one.
    Consequently the selected connected pieces are the actual components of
    the permitted region.  The consumed subset may have more components.
    """
    _limit('max_size', max_size)
    _limit('max_components', max_components)
    if type(include_empty) is not bool:
        raise ValueError('include_empty must be bool')
    graph = _graph(adjacency, check)
    n = len(graph)
    max_size = min(max_size, n)
    max_components = min(max_components, max_size)
    if include_empty:
        check()
        yield ()
    if not max_size or not max_components:
        return
    universe = frozenset(range(n))
    first = _connected_sets(graph, max_size, universe, -1, check)
    # Frame: chosen union, closed neighbourhood, component count, iterator.
    stack = [(frozenset(), frozenset(), 0, first)]
    while stack:
        check()
        chosen, blocked, count, iterator = stack[-1]
        try:
            component = frozenset(next(iterator))
        except StopIteration:
            stack.pop()
            continue
        union = chosen | component
        yield tuple(sorted(union))
        if count + 1 >= max_components or len(union) >= max_size:
            continue
        next_blocked = blocked | component
        for v in component:
            next_blocked |= graph[v]
        remaining = universe - next_blocked
        child = _connected_sets(graph, max_size-len(union), remaining,
                                min(component), check)
        stack.append((union, next_blocked, count+1, child))


def triangulation_dual_graph(triangulation, *, check=lambda: None):
    """Validate the source and return its simple tetrahedron dual graph."""
    from .normal_surface_geometry import _prepare
    prepared = _prepare(triangulation, check)
    result = []
    for t, row in enumerate(prepared['tetrahedra']):
        check()
        result.append(tuple(sorted({entry['tetrahedron'] for entry in row
                                    if entry is not None
                                    and entry['tetrahedron'] != t})))
    return tuple(result)


@_shield_callback
def search_pachner_regions(triangulation, heights, *, max_region_size,
                          max_components=1, max_upward=0, method='sleep',
                          max_nodes=10000, max_work=None, max_cycles=None,
                          seek_disc=True,
                          collect_endpoints=False, endpoint=None,
                          check=lambda: None):
    """Search every permitted initial region under one aggregate node/work cap.

    COMPLETE_BOUNDED_REGIONS means exhaustion of this finite region family.
    It is never a nontrivial-knot certificate.  The region is an allowed cover
    of the initial consumption footprint, not necessarily its exact support.
    A DISC_FOUND certificate is replayed by the independent endpoint verifier.
    """
    from .normal_cocycle import _Budget, CocycleLimit
    from .pachner_commitments import search_pachner_endpoints

    _limit('max_region_size', max_region_size)
    _limit('max_components', max_components)
    _limit('max_upward', max_upward)
    if max_nodes is not None:
        _limit('max_nodes', max_nodes)
    budget = _Budget(check, max_work)
    stats = dict(regions_started=0, regions_completed=0, nodes=0)
    scope = dict(max_region_size=max_region_size, max_components=max_components,
                 max_upward=max_upward, method=method,
                 meaning='initial footprint is contained in a permitted region')
    endpoints = []

    def protected_endpoint(proof):
        try:
            return endpoint(proof)
        except BaseException as error:
            raise _CallbackAbort(error) from None

    def finish(status, **fields):
        return dict(status=status, stats=dict(stats, work=budget.work),
                    scope=scope, endpoints=endpoints, **fields)

    try:
        graph = triangulation_dual_graph(triangulation, check=budget.tick)
        regions = footprint_regions(graph, max_region_size, max_components,
                                    check=budget.tick)
        for region in regions:
            budget.tick()
            stats['regions_started'] += 1
            remaining = None if max_nodes is None else max_nodes-stats['nodes']
            answer = search_pachner_endpoints(
                triangulation, heights, max_upward=max_upward, method=method,
                active_initial_tetrahedra=list(region), max_nodes=remaining,
                max_cycles=max_cycles,
                seek_disc=seek_disc, collect_endpoints=collect_endpoints,
                endpoint=protected_endpoint if endpoint is not None else None,
                check=budget.tick)
            stats['nodes'] += answer['stats']['nodes']
            if collect_endpoints:
                endpoints.extend(answer.get('endpoints', []))
            if answer['status'] in ('DISC_FOUND', 'ENDPOINT_SELECTED'):
                return finish(answer['status'], region=list(region),
                              certificate=answer['certificate'], result=answer)
            if answer['status'] != 'COMPLETE_BOUNDED_FAMILY':
                return finish('INCONCLUSIVE', region=list(region),
                              reason=answer.get('reason', 'bounded search stopped'),
                              result=answer)
            stats['regions_completed'] += 1
    except CocycleLimit as exc:
        return finish('INCONCLUSIVE', reason=str(exc))
    return finish('COMPLETE_BOUNDED_REGIONS')
