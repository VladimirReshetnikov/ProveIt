"""Extract a connected first descent from a verified generalized Pachner trace.

An event depends on the events that produced the tetrahedron incarnations it
consumes.  Components of this birth graph replay independently because both
formal bipyramid replacements preserve their boundary facets.  A shortest
descending subtrace is connected and has d=u+1, hence consumes at most 3u+3
original tetrahedra.  The output uses the existing independently checkable
endpoint-certificate schema; dependency metadata is never trusted as a proof
of a move.
"""
from copy import deepcopy

from .cocycle_transport import _integer_heights, transport_cocycle
from .cocycle_transport_verify import _shield_callback
from .normal_cocycle import _Budget, local_coordinates
from .normal_surface_geometry import _prepare
from .pachner23 import pachner_23
from .pachner32 import pachner_32
from .pachner_commitments_verify import inspect_pachner_endpoint


def _components(indices, parents):
    remaining = set(indices)
    neighbours = {i: set() for i in remaining}
    for i in remaining:
        for j in parents[i]:
            if j in remaining:
                neighbours[i].add(j)
                neighbours[j].add(i)
    answer = []
    while remaining:
        todo = [min(remaining)]
        found = set(todo)
        for i in todo:
            new = neighbours[i] - found
            found.update(new)
            todo.extend(sorted(new))
        remaining.difference_update(found)
        answer.append(tuple(sorted(found)))
    return answer


def _read_events(triangulation, certificate, check):
    n = len(triangulation['tetrahedra'])
    live = [('source', i) for i in range(n)]
    raw = triangulation
    events = []
    parents = []
    ancestry = {name: frozenset((name[1],)) for name in live}
    for index, step in enumerate(certificate['moves']):
        check()
        move = step['transport']['move']
        if move['schema'] == 'pachner-23-v1':
            t, face = move['tetrahedron'], move['face']
            used = {t, raw['tetrahedra'][t][face]['tetrahedron']}
            kind, port, count = 'up', face, 3
            formal_region = None
        else:
            # The seed row is the unique old tetrahedron without belt label 2.
            # Its two remaining belt vertices may have 0,1 in either local order.
            seed = next(item for item in move['region']
                        if 2 not in item['vertices'])
            t = seed['tetrahedron']
            labels = seed['vertices']
            port = [labels.index(3), labels.index(4)]
            used = {item['tetrahedron'] for item in move['region']}
            kind, count = 'down', 2
            formal_region = tuple((live[item['tetrahedron']],
                                   tuple(item['vertices'])) for item in move['region'])
        consumed = tuple(live[i] for i in sorted(used))
        parent_list = tuple(name[1] for name in consumed if name[0] == 'birth')
        source = frozenset(name[1] for name in consumed if name[0] == 'source')
        origin = frozenset().union(*(ancestry[name] for name in consumed))
        births = tuple(('birth', index, slot) for slot in range(count))
        events.append(dict(index=index, kind=kind, seed=live[t], port=port,
                           consumed=consumed, births=births,
                           sources=source, ancestry=origin,
                           formal_region=formal_region,
                           birth_consumptions=len(parent_list)))
        parents.append(frozenset(parent_list))
        live = [name for i, name in enumerate(live) if i not in used] + list(births)
        for name in births:
            ancestry[name] = origin
        raw = step['triangulation']
    return events, parents


def _connected_sources(triangulation, sources, check):
    if not sources:
        return False
    seen = {min(sources)}
    todo = list(seen)
    for i in todo:
        check()
        for entry in triangulation['tetrahedra'][i]:
            if entry is not None:
                j = entry['tetrahedron']
                if j in sources and j not in seen:
                    seen.add(j)
                    todo.append(j)
    return seen == set(sources)


def _summary(indices, events, parents, triangulation, check):
    components = _components(indices, parents)
    result = []
    for component in components:
        check()
        sources = frozenset().union(*(events[i]['sources'] for i in component))
        up = sum(events[i]['kind'] == 'up' for i in component)
        down = len(component) - up
        q = sum(events[i]['birth_consumptions'] for i in component)
        result.append(dict(events=list(component), upward_moves=up,
                           downward_moves=down, loss=down-up,
                           birth_consumptions=q,
                           consumed_initial_tetrahedra=sorted(sources),
                           connected_initial_footprint=_connected_sources(
                               triangulation, sources, check)))
    return result


@_shield_callback
def analyze_pachner_causality(triangulation, heights, certificate, *,
                              max_work=None, check=lambda: None):
    """Validate a supplied endpoint and return its exact birth-graph census.

    A malformed certificate returns None.  Resource/callback exceptions
    propagate, and no unverified partial census is returned.
    """
    budget = _Budget(check, max_work)
    endpoint = inspect_pachner_endpoint(triangulation, heights, certificate,
                                        check=budget.tick)
    if endpoint is None:
        return None
    events, parents = _read_events(triangulation, certificate, budget.tick)
    return dict(event_count=len(events),
                dependency_edges=[[j, i] for i, row in enumerate(parents)
                                  for j in sorted(row)],
                components=_summary(range(len(events)), events, parents,
                                    triangulation, budget.tick),
                upward_moves=endpoint['upward_moves'],
                downward_moves=endpoint['downward_moves'], work=budget.work)


def _descending_core(events, parents, check):
    chosen = tuple(range(len(events)))
    while True:
        check()
        components = _components(chosen, parents)
        positive = [c for c in components if sum(
            1 if events[i]['kind'] == 'down' else -1 for i in c) > 0]
        if not positive:
            raise ValueError('the supplied trace does not strictly reduce tetrahedra')
        component = min(positive, key=lambda c: (len(c), c))
        balance = 0
        prefix = []
        for i in component:
            check()
            prefix.append(i)
            balance += 1 if events[i]['kind'] == 'down' else -1
            if balance > 0:
                break
        next_chosen = tuple(prefix)
        # Truncation can disconnect a component.  Recompute until both the
        # connectedness and first-descent conditions hold simultaneously.
        if next_chosen == chosen and len(components) == 1:
            return chosen
        chosen = next_chosen


def _retain_declared_down_frame(replacement, event, live, check):
    """Preserve all birth-local labels admitted by the independent checker.

    A valid input can choose either order of belt labels 0,1 on its unique
    missing-2 source tetrahedron.  The canonical producer instead uses local
    vertex order.  Its apices were explicitly supplied in the declared 3,4
    order, so the only possible frame difference is this belt transposition.
    Relabel both new tetrahedra and every incident gluing before transport.
    """
    positions = {cell: i for i, cell in enumerate(live)}
    declared = {positions[name]: list(labels)
                for name, labels in event['formal_region']}
    canonical = {item['tetrahedron']: item['vertices']
                 for item in replacement['certificate']['region']}
    seed = positions[event['seed']]
    old, new = canonical[seed], declared[seed]
    sigma = [None] * 5
    for a, b in zip(old, new):
        sigma[a] = b
    sigma[2] = 2
    if sigma not in ([0, 1, 2, 3, 4], [1, 0, 2, 3, 4]):
        raise ArithmeticError('unexpected source-frame discrepancy')
    if any([sigma[v] for v in row] != declared[t]
           for t, row in canonical.items()):
        raise ArithmeticError('declared formal frame is not globally coherent')
    if sigma[0] != 0:
        raw = replacement['triangulation']['tetrahedra']
        n = len(raw)
        permutations = [list(range(4)) for _ in range(n-2)] + [[1, 0, 2, 3]]*2
        relabelled = [[None]*4 for _ in raw]
        for t, row in enumerate(raw):
            check()
            p = permutations[t]
            inverse = [p.index(v) for v in range(4)]
            for f, entry in enumerate(row):
                if entry is not None:
                    u, gluing = entry['tetrahedron'], entry['permutation']
                    relabelled[t][p[f]] = dict(tetrahedron=u, permutation=[
                        permutations[u][gluing[inverse[v]]] for v in range(4)])
        replacement['triangulation'] = dict(tetrahedra=relabelled)
    replacement['certificate'] = dict(schema='pachner-32-v1', region=[
        dict(tetrahedron=t, vertices=declared[t]) for t in sorted(declared)])
    return replacement


@_shield_callback
def extract_local_descent(triangulation, heights, certificate, *,
                          max_work=None, check=lambda: None):
    """Replay a connected first-descending subtrace of a valid descending trace.

    Return the standard endpoint certificate, the selected original event
    indices, and a census.  Input/output certificates are both checked by the
    existing independent verifier.  Raises ValueError for invalid input or a
    trace without strict descent, and ArithmeticError on an invariant failure.
    The extraction does not minimize the upward count or the footprint.
    """
    budget = _Budget(check, max_work)
    initial = inspect_pachner_endpoint(triangulation, heights, certificate,
                                       check=budget.tick)
    if initial is None:
        raise ValueError('invalid source-bound Pachner endpoint certificate')
    if initial['downward_moves'] <= initial['upward_moves']:
        raise ValueError('the supplied trace does not strictly reduce tetrahedra')
    events, parents = _read_events(triangulation, certificate, budget.tick)
    chosen = _descending_core(events, parents, budget.tick)
    n = len(triangulation['tetrahedra'])
    raw = deepcopy(triangulation)
    prepared = _prepare(raw, budget.tick)
    h = _integer_heights(prepared, heights, budget.tick)
    live = [('source', i) for i in range(n)]
    moves = []
    for i in chosen:
        budget.tick()
        event = events[i]
        if not set(event['consumed']) <= set(live):
            raise ArithmeticError('component projection omitted a required producer')
        t = live.index(event['seed'])
        replacement = (pachner_23(raw, t, event['port'], check=budget.tick)
                       if event['kind'] == 'up' else
                       pachner_32(raw, t, list(event['port']), check=budget.tick))
        if event['kind'] == 'down':
            replacement = _retain_declared_down_frame(
                replacement, event, live, budget.tick)
        transport = transport_cocycle(raw, h, replacement['triangulation'],
                                      replacement['certificate'], check=budget.tick)
        used = set(event['consumed'])
        live = [name for name in live if name not in used] + list(event['births'])
        raw, h = replacement['triangulation'], transport['heights']
        moves.append(dict(triangulation=raw, transport=transport['certificate']))
    census = _summary(chosen, events, parents, triangulation, budget.tick)
    component = census[0]
    up = component['upward_moves']
    active = component['consumed_initial_tetrahedra']
    if (len(census) != 1 or component['loss'] != 1
            or not component['connected_initial_footprint']
            or len(active) > 3*up + 3
            or len(moves) != 2*up + 1):
        raise ArithmeticError('causal localization bound failed')
    output = dict(schema='pachner-cochain-endpoint-v1', max_upward=up,
                  active_initial_tetrahedra=active, moves=moves,
                  coordinates=[local_coordinates(row) for row in h],
                  disc_certificate=None)
    verified = inspect_pachner_endpoint(triangulation, heights, output,
                                        check=budget.tick)
    if (verified is None or verified['downward_moves'] != up+1
            or len(verified['triangulation']['tetrahedra']) != n-1):
        raise ArithmeticError('independent extracted-descent replay failed')
    return dict(schema='pachner-causal-extraction-v1', certificate=output,
                selected_events=list(chosen), summary=component,
                original_events=len(events), work=budget.work)


def _namespace_event(event, trace_index):
    """Give independently supplied traces distinct incarnation birth names."""
    def name(cell):
        return cell if cell[0] == 'source' else (
            'birth', trace_index, cell[1], cell[2])

    formal = event['formal_region']
    return dict(event, seed=name(event['seed']),
        consumed=tuple(name(cell) for cell in event['consumed']),
        births=tuple(name(cell) for cell in event['births']),
        formal_region=None if formal is None else tuple(
            (name(cell), labels) for cell, labels in formal))


@_shield_callback
def compose_disjoint_traces(triangulation, heights, certificates, *,
                            max_work=None, check=lambda: None):
    """Replay source-bound traces with pairwise disjoint actual footprints.

    Each input endpoint certificate is independently verified against the same
    supplied source.  Disjointness concerns original tetrahedra actually
    consumed, reconstructed by that verifier; supplied covering regions may
    overlap.  Birth names are private to each input trace.  The trace order is
    the supplied order, and every declared down-move frame is preserved.

    The result contains one standard endpoint certificate independently
    checked against the source, together with per-input supports and additive
    actual upward/downward counts and loss.  max_upward in the output proof is
    the sum of actual upward counts, not the sum of unused input allowances.
    Any input disc certificates are verified but no disc claim is copied to
    the composed endpoint.  Empty input and identity traces are permitted.

    Invalid certificates, non-sequence input, and overlapping actual supports
    raise ValueError.  Work/callback exceptions propagate as in the other
    causality APIs, and a cap never returns an unverified partial certificate.
    Input structures are snapshotted before invoking user callbacks.
    """
    if type(certificates) not in (list, tuple):
        raise ValueError('certificates must be a finite list or tuple')
    budget = _Budget(check, max_work)
    source, source_heights, proofs = deepcopy((triangulation, heights, certificates))
    budget.tick()
    prepared = _prepare(source, budget.tick)
    initial_heights = _integer_heights(prepared, source_heights, budget.tick)
    n = len(prepared['tetrahedra'])
    occupied = set()
    inputs, event_lists = [], []
    upward = downward = 0
    for trace_index, proof in enumerate(proofs):
        budget.tick()
        endpoint = inspect_pachner_endpoint(source, source_heights, proof,
                                            check=budget.tick)
        if endpoint is None:
            raise ValueError('invalid source-bound Pachner endpoint certificate')
        support = set(endpoint['consumed_initial_tetrahedra'])
        if occupied & support:
            raise ValueError('input traces have overlapping actual initial footprints')
        occupied.update(support)
        up, down = endpoint['upward_moves'], endpoint['downward_moves']
        upward += up
        downward += down
        inputs.append(dict(trace_index=trace_index,
            consumed_initial_tetrahedra=sorted(support),
            upward_moves=up, downward_moves=down, loss=down-up))
        events, _ = _read_events(source, proof, budget.tick)
        event_lists.append([_namespace_event(event, trace_index) for event in events])

    raw, h = deepcopy(source), initial_heights
    live = [('source', i) for i in range(n)]
    moves, replayed = [], []
    for trace_index, events in enumerate(event_lists):
        for event in events:
            budget.tick()
            used = set(event['consumed'])
            if not used <= set(live):
                raise ArithmeticError('disjoint composition lost a required incarnation')
            t = live.index(event['seed'])
            replacement = (pachner_23(raw, t, event['port'], check=budget.tick)
                           if event['kind'] == 'up' else
                           pachner_32(raw, t, list(event['port']), check=budget.tick))
            if event['kind'] == 'up':
                move = replacement['certificate']
                a, face = move['tetrahedron'], move['face']
                actual = {live[a], live[raw['tetrahedra'][a][face]['tetrahedron']]}
            else:
                actual = {live[item['tetrahedron']]
                          for item in replacement['certificate']['region']}
            if actual != used:
                raise ArithmeticError('composition changed a declared event source')
            if event['kind'] == 'down':
                replacement = _retain_declared_down_frame(
                    replacement, event, live, budget.tick)
            transported = transport_cocycle(raw, h, replacement['triangulation'],
                                            replacement['certificate'], check=budget.tick)
            live = [cell for cell in live if cell not in used] + list(event['births'])
            raw, h = replacement['triangulation'], transported['heights']
            if len(live) != len(raw['tetrahedra']) or len(set(live)) != len(live):
                raise ArithmeticError('namespaced composition incarnation count failed')
            moves.append(dict(triangulation=raw, transport=transported['certificate']))
            replayed.append([trace_index, event['index']])

    active = sorted(occupied)
    output = dict(schema='pachner-cochain-endpoint-v1', max_upward=upward,
        active_initial_tetrahedra=active, moves=moves,
        coordinates=[local_coordinates(row) for row in h], disc_certificate=None)
    verified = inspect_pachner_endpoint(source, source_heights, output, check=budget.tick)
    if (verified is None or verified['upward_moves'] != upward
            or verified['downward_moves'] != downward
            or verified['consumed_initial_tetrahedra'] != active
            or len(verified['triangulation']['tetrahedra']) != n+upward-downward
            or len(moves) != upward+downward):
        raise ArithmeticError('independent composed endpoint replay failed')
    summary = dict(input_traces=len(proofs), initial_tetrahedra=n,
        final_tetrahedra=n+upward-downward, upward_moves=upward,
        downward_moves=downward, loss=downward-upward,
        consumed_initial_tetrahedra=active)
    return dict(schema='pachner-disjoint-composition-v1', certificate=output,
                inputs=inputs, summary=summary, replayed_events=replayed,
                work=budget.work)
