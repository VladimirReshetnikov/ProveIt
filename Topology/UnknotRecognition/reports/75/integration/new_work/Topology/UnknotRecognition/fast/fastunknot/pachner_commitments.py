"""Complete bounded-upward Pachner cochain search with exact local commitments.

A tetrahedron incarnation is assigned idle, one of its six edges (3--2),
or one of its four faces (2--3).  A move is ready only when all its source
cells agree.  Ready moves have disjoint sources and commute.  A deterministic
ready-move scheduler therefore preserves every bounded-upward endpoint up to
the stable marked cell names.  New tetrahedra start unassigned.

For t initial cells and at most u upward moves, at most 3t+5u incarnations
are assigned.  There are at most 11 choices per assignment, or seven when
u=0.  The sleep-set route removes commuting permutations and inherits this
bound by visiting at most one representative per commuting trace class.
This uses the actual geometric event relation: disjoint replacements preserve
each other's geometric enabledness and keys, while a move that consumes a
source incarnation permanently disables every different event needing it.
The argument does not assert such a bound for arbitrary state-dependent
independence relations.  The naive route is a small-input validation oracle.

Every route uses the same complete legal move generator and independently
replayed integral cochain transport.  Exhaustion concerns this cochain family
only and is never an unqualified negative unknot verdict.
"""
from copy import deepcopy
from dataclasses import dataclass

from .cocycle_transport import _integer_heights, _collapse_region, transport_cocycle
from .cocycle_transport_verify import _shield_callback, _CallbackAbort
from .normal_cocycle import _Budget, CocycleLimit, local_coordinates
from .normal_surface_geometry import _prepare, _EDGES
from .pachner23 import pachner_23
from .pachner32 import pachner_32


_IDLE = ('idle', 0)
_DOWN = tuple(('down', i) for i in range(6))
_UP = tuple(('up', i) for i in range(4))


@dataclass(frozen=True)
class _Event:
    kind: str
    ports: tuple
    key: tuple

    @property
    def cells(self):
        return frozenset(cell for cell, _ in self.ports)


@dataclass
class _State:
    raw: dict
    heights: list
    cells: tuple
    upward: int
    downward: int
    trace: tuple
    events: tuple | None = None


class _Names:
    """Exact DAG interning; neither hashes nor path-local birth counters merge."""
    def __init__(self, count):
        self.names = {('source', i): i for i in range(count)}

    def children(self, event):
        result = []
        for slot in range(3 if event.kind == 'up' else 2):
            key = ('birth', event.key, slot)
            if key not in self.names:
                self.names[key] = len(self.names)
            result.append(self.names[key])
        return tuple(result)


def _event(kind, ports):
    ports = tuple(sorted(ports))
    return _Event(kind, ports, (kind, ports))


def _events(state, allow_upward, check):
    if state.events is not None:
        return state.events
    prepared = _prepare(state.raw, check)
    rows, cells = prepared['tetrahedra'], state.cells
    groups = {}
    for local, root in enumerate(prepared['edge_roots']):
        check()
        groups.setdefault(root, []).append((local//6, *_EDGES[local % 6]))
    answer = []
    for occurrences in groups.values():
        check()
        if _collapse_region(rows, occurrences, check) is None:
            continue
        ports = [(cells[t], _EDGES.index((a, b))) for t, a, b in occurrences]
        answer.append(_event('down', ports))
    if allow_upward:
        for t, f, u, g, permutation in prepared['pairs']:
            check()
            if t != u:
                answer.append(_event('up', [(cells[t], f), (cells[u], g)]))
    state.events = tuple(sorted(answer, key=lambda move: move.key))
    return state.events


def _advance(state, event, names, check):
    positions = {cell: t for t, cell in enumerate(state.cells)}
    cell, port = event.ports[0]
    t = positions[cell]
    replacement = (pachner_32(state.raw, t, list(_EDGES[port]), check=check)
                   if event.kind == 'down'
                   else pachner_23(state.raw, t, port, check=check))
    after = replacement['triangulation']
    transport = transport_cocycle(state.raw, state.heights, after,
                                  replacement['certificate'], check=check)
    survivors = tuple(c for c in state.cells if c not in event.cells)
    cells = survivors + names.children(event)
    if len(cells) != len(after['tetrahedra']):
        raise ArithmeticError('Pachner incarnation bookkeeping disagrees with replacement')
    step = dict(triangulation=after, transport=transport['certificate'])
    return _State(after, transport['heights'], cells,
                  state.upward + (event.kind == 'up'),
                  state.downward + (event.kind == 'down'), state.trace+(step,))


def _state_key(state, include_budget=False):
    """Exact marked cochain serialization, invariant under row reindexing."""
    ordered = sorted(range(len(state.cells)), key=lambda i: state.cells[i])
    records = []
    for i in ordered:
        row = state.raw['tetrahedra'][i]
        faces = tuple(None if r is None else
                      (state.cells[r['tetrahedron']], tuple(r['permutation'])) for r in row)
        h = state.heights[i]
        records.append((state.cells[i], faces, tuple(x-h[0] for x in h)))
    answer = tuple(records)
    return (state.upward, answer) if include_budget else answer


def _certificate(state, maximum, active, disc=None):
    return dict(schema='pachner-cochain-endpoint-v1', max_upward=maximum,
                active_initial_tetrahedra=list(active),
                moves=list(state.trace),
                coordinates=[local_coordinates(row) for row in state.heights],
                disc_certificate=disc)


def _validate_limit(name, value):
    if value is not None and (type(value) is not int or value < 0):
        raise ValueError(name+' must be a nonnegative integer or None')


@_shield_callback
def search_pachner_endpoints(triangulation, heights, *, max_upward=0,
                              method='commitments', max_nodes=10000,
                              max_work=None, max_cycles=None, seek_disc=False,
                              collect_endpoints=False, endpoint=None,
                              active_initial_tetrahedra=None,
                              check=lambda: None):
    """Enumerate a complete bounded-upward family, or stop with explicit status.

    ``method`` is commitments, sleep, or naive.  The commitments assignment
    tree has bound 11^(3t+5u), up to polynomial factors.  Sleep inherits the
    bound through unique commuting-trace representatives and retains every
    bounded trace modulo exchanges of disjoint moves.  This requires stable
    geometric event keys, persistence through disjoint replacements, and
    nonresurrection after a source incarnation is consumed.  The upward
    allowance is a total trace count, so commuting a legal bounded trace
    preserves that allowance.  Naive is an uncached reference enumeration.
    All moves count toward the
    same shared work cap.  ``max_nodes`` counts popped search frames.

    ``endpoint`` optionally receives a private source-replay certificate at
    every new marked endpoint.  Returning True selects it and stops, with
    ENDPOINT_SELECTED rather than a topological verdict.  Its exceptions
    propagate.  ``seek_disc`` invokes the maintained complete supplied-vector
    disc counter at each new endpoint and independently replays positives.
    Disc query caps are per endpoint and make final exhaustion inconclusive.

    COMPLETE_BOUNDED_FAMILY means all represented endpoints were visited.  It
    is no assertion that every disc or unknot has a witness in that family.
    Source triangulations, height rows and all callback certificates are
    copied, so callback mutation cannot change the search state.

    ``active_initial_tetrahedra`` optionally restricts the initial footprint.
    Only listed original tetrahedra may ever be consumed; every newly created
    tetrahedron is eligible.  For r allowed original cells the commitment
    bound improves to 11^(3r+5u), or 7^(3r) for pure descent.
    """
    if type(max_upward) is not int or max_upward < 0:
        raise ValueError('max_upward must be a nonnegative integer')
    if method not in ('commitments', 'sleep', 'naive'):
        raise ValueError('method must be commitments, sleep, or naive')
    for name, value in (('max_nodes', max_nodes), ('max_work', max_work),
                        ('max_cycles', max_cycles)):
        _validate_limit(name, value)
    if type(seek_disc) is not bool or type(collect_endpoints) is not bool:
        raise ValueError('seek_disc and collect_endpoints must be bool')
    if endpoint is not None and not callable(endpoint):
        raise ValueError('endpoint must be callable or None')
    budget = _Budget(check, max_work)
    stats = dict(method=method, nodes=0, assignments=0, moves=0,
                 unique_endpoints=0, terminal_frames=0, sleep_pruned=0,
                 disc_queries=0, incomplete_disc_queries=0,
                 maximum_upward=0, maximum_downward=0,
                 maximum_live_cells=0, maximum_assigned_incarnations=0)
    collected, seen = [], set()
    active = None

    def finish(status, **fields):
        result = dict(status=status, max_upward=max_upward,
                      stats=dict(stats, work=budget.work),
                      active_initial_tetrahedra=active,
                      trust='bounded cochain family in the supplied manifold only', **fields)
        if collect_endpoints:
            result['endpoints'] = collected
        return result

    try:
        prepared = _prepare(triangulation, budget.tick)
        initial_heights = _integer_heights(prepared, heights, budget.tick)
        n = len(prepared['tetrahedra'])
        if active_initial_tetrahedra is not None and (
                type(active_initial_tetrahedra) not in (list, tuple)
                or any(type(i) is not int or not 0 <= i < n
                       for i in active_initial_tetrahedra)
                or len(set(active_initial_tetrahedra)) != len(active_initial_tetrahedra)):
            raise ValueError('active_initial_tetrahedra must contain distinct source indices')
        active = sorted(range(n) if active_initial_tetrahedra is None
                        else active_initial_tetrahedra)
        protected = frozenset(set(range(n))-set(active))
        r = len(active)
        stats['initial_tetrahedra'] = n
        stats['active_initial_tetrahedra'] = r
        names = _Names(n)
        first = _State(deepcopy(triangulation), initial_heights, tuple(range(n)), 0, 0, ())
        # payload = commitments + number of assignments, or a sleep set.
        stack = [(first, {i: _IDLE for i in protected}, 0)] if method == 'commitments' else [
            (first, frozenset(), 0)]
        while stack:
            budget.tick()
            if max_nodes is not None and stats['nodes'] >= max_nodes:
                return finish('INCONCLUSIVE', reason='search node allowance exhausted')
            state, payload, assignments = stack.pop()
            stats['nodes'] += 1
            stats['maximum_upward'] = max(stats['maximum_upward'], state.upward)
            stats['maximum_downward'] = max(stats['maximum_downward'], state.downward)
            stats['maximum_live_cells'] = max(stats['maximum_live_cells'], len(state.cells))
            stats['maximum_assigned_incarnations'] = max(
                stats['maximum_assigned_incarnations'], assignments)
            if (len(state.cells) > n+max_upward or assignments > 3*r+5*max_upward
                    or state.downward > r+state.upward):
                raise ArithmeticError('bounded-upward incarnation invariant failed')
            key = _state_key(state)
            if key not in seen:
                seen.add(key)
                stats['unique_endpoints'] += 1
                proof = _certificate(state, max_upward, active)
                if collect_endpoints:
                    collected.append(deepcopy(proof))
                if endpoint is not None:
                    try:
                        selected = endpoint(deepcopy(proof))
                    except BaseException as error:
                        raise _CallbackAbort(error) from None
                    if selected:
                        return finish('ENDPOINT_SELECTED', certificate=deepcopy(proof))
                if seek_disc:
                    from .normal_disk_kernel import normal_compressing_disk_count
                    from .pachner_commitments_verify import inspect_pachner_endpoint
                    stats['disc_queries'] += 1
                    answer = normal_compressing_disk_count(state.raw, proof['coordinates'],
                        max_cycles=max_cycles, record_certificate=True, check=budget.tick)
                    if answer['status'] != 'COMPLETE':
                        stats['incomplete_disc_queries'] += 1
                    elif answer['contains_compressing_disk']:
                        proof['disc_certificate'] = answer['certificate']
                        summary = inspect_pachner_endpoint(triangulation, heights, proof,
                                                          check=budget.tick)
                        if summary is None or not summary['contains_compressing_disk']:
                            raise ArithmeticError('source-bound positive endpoint replay failed')
                        return finish('DISC_FOUND', certificate=proof)
            available = tuple(move for move in
                _events(state, state.upward < max_upward, budget.tick)
                if protected.isdisjoint(move.cells))
            # The upward part is immutable for this state's fixed upward count.
            if not available:
                stats['terminal_frames'] += 1
                continue
            if method == 'commitments':
                ready = [move for move in available if all(
                    payload.get(cell) == (move.kind, port) for cell, port in move.ports)]
                if ready:
                    selected = ready[0]
                    child = _advance(state, selected, names, budget.tick)
                    stats['moves'] += 1
                    inherited = {c: x for c, x in payload.items() if c not in selected.cells}
                    stack.append((child, inherited, assignments))
                    continue
                unassigned = sorted(set(state.cells)-set(payload))
                if not unassigned:
                    stats['terminal_frames'] += 1
                    continue
                cell = unassigned[0]
                choices = (_IDLE,)+_DOWN+(_UP if max_upward else ())
                stats['assignments'] += 1
                for choice in reversed(choices):
                    copied = dict(payload)
                    copied[cell] = choice
                    stack.append((state, copied, assignments+1))
            else:
                sleep = set(payload)
                children = []
                for move in available:
                    budget.tick()
                    if method == 'sleep' and move.key in sleep:
                        stats['sleep_pruned'] += 1
                        continue
                    child = _advance(state, move, names, budget.tick)
                    stats['moves'] += 1
                    retained = frozenset(key for key in sleep
                        if move.cells.isdisjoint(cell for cell, port in key[1]))
                    children.append((child, retained, 0))
                    if method == 'sleep':
                        sleep.add(move.key)
                stack.extend(reversed(children))
        stats['interned_incarnations'] = len(names.names)
        if stats['incomplete_disc_queries']:
            return finish('INCONCLUSIVE', reason='one or more endpoint disc queries were capped')
        return finish('COMPLETE_BOUNDED_FAMILY')
    except CocycleLimit as error:
        return finish('INCONCLUSIVE', reason=str(error))
