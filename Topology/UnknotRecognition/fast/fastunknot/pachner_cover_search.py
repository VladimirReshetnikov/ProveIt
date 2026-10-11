"""One exact search for the union of all bounded initial-footprint regions.

The maintained region wrapper restarts the same Pachner search for every
permitted cover. This implementation shares every common event prefix.
The default backend asks exactly whether a permitted cover contains the
consumed original footprint, completing disconnected footprints on demand.
The indexed backend instead intersects the full cover incidence sets. Both
represent the same existential language; neither an approximate oracle nor
a selected witness cover constrains later continuations.

The sleep route preserves the original commuting-trace reduction.  The
cover constraint is hereditary and depends only on the consumed original
cells, so exchanging disjoint consecutive moves preserves admissibility.
The naive route is a finite differential oracle.  Commitments are deliberately
not offered here: assigning all initially possible cells before fixing a
cover would reintroduce an exponential dependence on the ambient size.

All successful disc or descent claims are independently replayed.  Search
and index caps return INCONCLUSIVE.  Exhausting a finite cochain family is
never a nontrivial-knot certificate.
"""
from copy import deepcopy
from dataclasses import dataclass

from .cocycle_transport import _integer_heights
from .cocycle_transport_verify import _shield_callback, _CallbackAbort
from .normal_cocycle import _Budget, CocycleLimit
from .normal_surface_geometry import _prepare
from .pachner_commitments import (
    _State, _Names, _events, _advance, _state_key, _certificate,
)
from .pachner_regions import footprint_regions


def _limit(name, value, optional=False):
    if optional and value is None:
        return
    if type(value) is not int or value < 0:
        suffix = ' or None' if optional else ''
        raise ValueError(name + ' must be a nonnegative integer' + suffix)


@dataclass(frozen=True)
class _CoverIndex:
    regions: tuple
    incidence: tuple

    def extend(self, compatible, consumed, stats, check):
        """Return exactly the old covers also containing the new source cells."""
        # None represents every cover at the initial frame.  Starting with
        # the smallest incidence list avoids scanning the ambient family.
        for cell in sorted(consumed, key=lambda c: len(self.incidence[c])):
            check()
            stats['cover_intersections'] += 1
            allowed = self.incidence[cell]
            compatible = allowed if compatible is None else compatible & allowed
            if not compatible:
                return frozenset()
        return compatible

    def witness(self, compatible):
        return () if compatible is None else self.regions[min(compatible)]


def _build_index(graph, maximum, components, max_regions, stats, check):
    regions = []
    incidence = [set() for _ in graph]
    for region in footprint_regions(graph, maximum, components, check=check):
        check()
        if max_regions is not None and len(regions) >= max_regions:
            raise CocycleLimit('region index allowance exhausted')
        number = len(regions)
        regions.append(region)
        stats['regions_indexed'] += 1
        for cell in region:
            check()
            incidence[cell].add(number)
            stats['region_incidence_entries'] += 1
    return _CoverIndex(tuple(regions), tuple(frozenset(row) for row in incidence))


@_shield_callback
def search_pachner_cover(triangulation, heights, *, max_region_size,
                         max_components=1, max_upward=0, method='sleep',
                         max_nodes=10000, max_regions=None, max_work=None,
                         cover_backend='auto', max_oracle_states=None,
                         max_cycles=None, seek_disc=False,
                         collect_endpoints=False, endpoint=None,
                         check=lambda: None):
    """Search all permitted covers in one shared event tree.

    The exact finite family is the union, over all initial dual-graph vertex
    sets of size at most max_region_size and at most max_components induced
    components, of all traces consuming only original cells in that set and
    containing at most max_upward total 2--3 moves.  New cells are eligible.
    Every prefix is an endpoint; duplicate marked endpoints are queried once.

    Certificates use the maintained pachner-cochain-endpoint-v1 schema.  The
    active_initial_tetrahedra field supplies a concrete admissible cover.
    COMPLETE_BOUNDED_COVER_FAMILY means exhaustion of precisely this family.
    cover_backend is auto, indexed, or oracle. Auto uses the exact on-demand
    oracle unless max_regions explicitly requests a complete-index cap.
    max_regions retains its indexed meaning; max_oracle_states limits total
    completion states, and incomplete completion is inconclusive.
    Queued branches store parent+event and materialize a native move only when
    visited, so positive early stopping does not transport unused alternatives.
    max_nodes counts popped frames; max_work counts cooperative checkpoints,
    including index construction and positive replay.  Disc-query cycle caps
    are per endpoint and prevent a complete final answer if any query is capped.
    """
    for name, value in (('max_region_size', max_region_size),
                        ('max_components', max_components), ('max_upward', max_upward)):
        _limit(name, value)
    for name, value in (('max_nodes', max_nodes), ('max_regions', max_regions),
                        ('max_work', max_work), ('max_cycles', max_cycles),
                        ('max_oracle_states',max_oracle_states)):
        _limit(name, value, optional=True)
    if cover_backend not in ('auto','indexed','oracle'):
        raise ValueError('cover_backend must be auto, indexed or oracle')
    if cover_backend=='oracle'and max_regions is not None:
        raise ValueError('max_regions limits the indexed backend')
    if method not in ('sleep', 'naive'):
        raise ValueError('shared-cover method must be sleep or naive')
    if type(seek_disc) is not bool or type(collect_endpoints) is not bool:
        raise ValueError('seek_disc and collect_endpoints must be bool')
    if endpoint is not None and not callable(endpoint):
        raise ValueError('endpoint must be callable or None')
    budget = _Budget(check, max_work)
    stats = dict(method=method, regions_indexed=0, region_incidence_entries=0,
                 cover_intersections=0, cover_rejections=0, nodes=0, moves=0,
                 unique_endpoints=0, duplicate_endpoint_frames=0,
                 sleep_pruned=0, terminal_frames=0, disc_queries=0,
                 incomplete_disc_queries=0, maximum_upward=0,
                 maximum_downward=0, maximum_live_cells=0,
                 maximum_consumed_initial=0, maximum_compatible_covers=0,
                 oracle_queries=0,oracle_cache_hits=0,oracle_states=0)
    scope = dict(max_region_size=max_region_size, max_components=max_components,
                 max_upward=max_upward, method=method,
                 meaning='consumed original cells are contained in a permitted cover')
    collected, seen = [], set()

    def finish(status, **fields):
        result = dict(status=status, scope=scope, stats=dict(stats, work=budget.work),
                      trust='bounded cochain family in the supplied manifold only', **fields)
        if collect_endpoints:
            result['endpoints'] = collected
        return result

    try:
        prepared = _prepare(triangulation, budget.tick)
        initial_heights = _integer_heights(prepared, heights, budget.tick)
        n = len(prepared['tetrahedra'])
        stats['initial_tetrahedra'] = n
        graph = tuple(tuple(sorted({entry['tetrahedron'] for entry in row
                                    if entry is not None and entry['tetrahedron'] != t}))
                      for t, row in enumerate(prepared['tetrahedra']))
        selected_backend=('indexed'if max_regions is not None else 'oracle')if cover_backend=='auto'else cover_backend
        stats['cover_backend']=selected_backend
        scope['cover_backend']=selected_backend
        if selected_backend=='indexed':
            index = _build_index(graph, max_region_size, max_components, max_regions,
                                 stats, budget.tick)
        else:
            from .pachner_cover_oracle import _CoverOracle
            index=_CoverOracle(graph,max_region_size,max_components,max_oracle_states)
        names = _Names(n)
        first = _State(deepcopy(triangulation), initial_heights, tuple(range(n)), 0, 0, ())
        # Parent/state, sleep, consumed originals, compatible covers, pending
        # move.  Deferring replacement avoids computing unvisited siblings.
        stack = [(first, frozenset(), frozenset(), None, None)]
        while stack:
            budget.tick()
            if max_nodes is not None and stats['nodes'] >= max_nodes:
                return finish('INCONCLUSIVE', reason='search node allowance exhausted')
            state, payload, consumed, compatible, pending = stack.pop()
            if pending is not None:
                state = _advance(state, pending, names, budget.tick)
                stats['moves'] += 1
            stats['nodes'] += 1
            stats['maximum_upward'] = max(stats['maximum_upward'], state.upward)
            stats['maximum_downward'] = max(stats['maximum_downward'], state.downward)
            stats['maximum_live_cells'] = max(stats['maximum_live_cells'], len(state.cells))
            stats['maximum_consumed_initial'] = max(stats['maximum_consumed_initial'],
                                                     len(consumed))
            if selected_backend=='indexed'and compatible is not None:
                stats['maximum_compatible_covers'] = max(
                    stats['maximum_compatible_covers'], len(compatible))
            if (len(consumed) > max_region_size or state.upward > max_upward
                    or state.downward > len(consumed)+state.upward
                    or len(state.cells) != n+state.upward-state.downward):
                raise ArithmeticError('shared-cover incarnation invariant failed')
            key = _state_key(state)
            if key in seen:
                stats['duplicate_endpoint_frames'] += 1
            else:
                seen.add(key)
                stats['unique_endpoints'] += 1
                cover = index.witness(compatible)
                proof = _certificate(state, max_upward, cover)
                if collect_endpoints:
                    collected.append(deepcopy(proof))
                if endpoint is not None:
                    try:
                        selected = bool(endpoint(deepcopy(proof)))
                    except BaseException as error:
                        raise _CallbackAbort(error) from None
                    if selected:
                        return finish('ENDPOINT_SELECTED', region=list(cover),
                                      certificate=deepcopy(proof))
                if seek_disc:
                    from .normal_disk_kernel import normal_compressing_disk_count
                    from .pachner_cover_verify import inspect_pachner_cover
                    stats['disc_queries'] += 1
                    answer = normal_compressing_disk_count(
                        state.raw, proof['coordinates'], max_cycles=max_cycles,
                        record_certificate=True, check=budget.tick)
                    if answer['status'] != 'COMPLETE':
                        stats['incomplete_disc_queries'] += 1
                    elif answer['contains_compressing_disk']:
                        proof['disc_certificate'] = answer['certificate']
                        replay = inspect_pachner_cover(triangulation, heights, proof,
                            max_region_size=max_region_size, max_components=max_components,
                            max_upward=max_upward, check=budget.tick)
                        if replay is None or not replay['contains_compressing_disk']:
                            raise ArithmeticError('covered disc failed independent source replay')
                        return finish('DISC_FOUND', region=list(cover), certificate=proof)
            sleep = set(payload)
            children = []
            for move in _events(state, state.upward < max_upward, budget.tick):
                budget.tick()
                if method == 'sleep' and move.key in sleep:
                    stats['sleep_pruned'] += 1
                    continue
                original = frozenset(cell for cell in move.cells if cell < n)
                allowed = index.extend(compatible, original, stats, budget.tick)
                if allowed is not None and not allowed:
                    stats['cover_rejections'] += 1
                    continue
                retained = frozenset(key for key in sleep
                    if move.cells.isdisjoint(cell for cell, port in key[1]))
                children.append((state, retained, consumed | original, allowed, move))
                if method == 'sleep':
                    sleep.add(move.key)
            if not children:
                stats['terminal_frames'] += 1
            stack.extend(reversed(children))
        stats['interned_incarnations'] = len(names.names)
        if stats['incomplete_disc_queries']:
            return finish('INCONCLUSIVE', reason='one or more endpoint disc queries were capped')
        return finish('COMPLETE_BOUNDED_COVER_FAMILY')
    except CocycleLimit as error:
        return finish('INCONCLUSIVE', reason=str(error))


@_shield_callback
def find_pachner_descent(triangulation, heights, *, max_upward=0,
                         max_region_size=None, method='sleep', max_nodes=10000,
                         max_regions=None, max_work=None, cover_backend='auto',
                         max_oracle_states=None,check=lambda: None):
    """Find a strictly smaller triangulation with at most max_upward 2--3 moves.

    With the default radius min(t, 3*max_upward+3), connected-cover exhaustion
    excludes every strict descent within the total upward bound.  This uses
    the first-descent birth-component theorem, not an assumption that every
    input trace has connected consumption.  An explicitly smaller radius
    provides only a bounded local conclusion.  No result recognizes a knot.
    """
    _limit('max_upward', max_upward)
    _limit('max_region_size', max_region_size, optional=True)
    budget = _Budget(check, max_work)
    try:
        # This validates shape and provides t without assuming a raw dict is
        # well formed.  The general search independently validates its source.
        n = len(_prepare(triangulation, budget.tick)['tetrahedra'])
        sufficient = min(n, 3*max_upward+3)
        radius = sufficient if max_region_size is None else max_region_size

        def smaller(proof):
            trace = proof['moves']
            return bool(trace and len(trace[-1]['triangulation']['tetrahedra']) < n)

        answer = search_pachner_cover(triangulation, heights,
            max_region_size=radius, max_components=1, max_upward=max_upward,
            method=method, max_nodes=max_nodes, max_regions=max_regions,
            cover_backend=cover_backend,max_oracle_states=max_oracle_states,
            endpoint=smaller, check=budget.tick)
        answer['descent_scope'] = dict(max_upward=max_upward,
            sufficient_connected_radius=sufficient, searched_radius=radius,
            covers_all_bounded_upward_descents=radius >= sufficient)
        if answer['status'] == 'ENDPOINT_SELECTED':
            from .pachner_cover_verify import inspect_pachner_descent
            replay = inspect_pachner_descent(triangulation, heights, answer['certificate'],
                max_upward=max_upward, max_region_size=radius, check=budget.tick)
            if replay is None:
                raise ArithmeticError('strict descent failed independent source replay')
            answer['status'] = 'DESCENT_FOUND'
            answer['descent'] = dict(initial_tetrahedra=n,
                final_tetrahedra=len(replay['triangulation']['tetrahedra']),
                upward_moves=replay['upward_moves'], downward_moves=replay['downward_moves'],
                consumed_initial_tetrahedra=replay['consumed_initial_tetrahedra'])
        elif answer['status'] == 'COMPLETE_BOUNDED_COVER_FAMILY':
            answer['status'] = ('COMPLETE_BOUNDED_DESCENT' if radius >= sufficient
                                else 'COMPLETE_BOUNDED_LOCAL_DESCENT')
        answer['stats']['aggregate_work'] = budget.work
        return answer
    except CocycleLimit as error:
        return dict(status='INCONCLUSIVE', reason=str(error),
                    stats=dict(aggregate_work=budget.work),
                    trust='bounded descent search; no knot verdict')
