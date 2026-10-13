"""Factorial-free exact forest selection by nonlinear output assignments.

For each choice of one unit output per nonlinear column, a distinguished
partition block records prerequisite rows that need no initial seed witness.
Every other block is served by a single graphic-independent seed.  Restricted
Horn closure decides whether these initial prerequisites suffice, without
enumerating event orders.  The number of partitions is at most Bell(P + 1).

The ordered solver remains available as a separately frozen baseline.  This
producer reuses its ordinary graph and matroid primitives; the output checker
uses only independent checker primitives and its own nonlinear closure.
"""

from collections import deque
from itertools import product

from .model import parse_problem
from .solver import (Work, ResourceLimit, _unrooted, _peel, _owners,
                     _nonlinear, _compile, _reach, _rainbow, _partitions, _success)


def _output_closure(starts, outgoing, exceptional, columns, outputs, work):
    waiting = [[] for _ in outgoing]
    pending = []
    for gate, (column, target) in enumerate(zip(columns, outputs)):
        prerequisites = [row for row, _ in exceptional[column] if row != target]
        pending.append(len(prerequisites))
        for row in prerequisites:
            waiting[row].append(gate)
            work.tick('restricted_gate_incidences')
    active = set(starts)
    queue = deque(sorted(active))
    for gate, count in enumerate(pending):
        if count == 0 and outputs[gate] not in active:
            active.add(outputs[gate])
            queue.append(outputs[gate])
    while queue:
        row = queue.popleft()
        work.tick('restricted_closure_rows')
        for target in outgoing[row]:
            work.tick('restricted_unary_arcs')
            if target not in active:
                active.add(target)
                queue.append(target)
        for gate in waiting[row]:
            work.tick('restricted_gate_visits')
            pending[gate] -= 1
            if pending[gate] == 0:
                target = outputs[gate]
                if target not in active:
                    active.add(target)
                    queue.append(target)
    return active


def solve_output(problem, *, max_work=None, max_assignments=None,
                 max_partitions=None, use_rank_layer=True):
    """Return a complete forest decision or an honest resource refusal.

    Compared with ``solve``, this exact strategy removes the factorial event
    ordering factor.  With k unit triples the structural bound is
    ``3**k * Bell(2*k+1) * poly(input)``.  No event ordering is enumerated.
    """
    data = parse_problem(problem)
    if type(use_rank_layer) is not bool:
        raise ValueError('use_rank_layer must be Boolean')
    work = Work(max_work, max_assignments, max_partitions)
    rank_layer = use_rank_layer and data.raw_parity
    summary = {'raw_parity': data.raw_parity, 'rank_layer_active': rank_layer,
               'graph_rank_if_connected': data.vertices - 1}

    def answer(status, certificate=None, **extra):
        counts = work.export()
        if 'scenarios' in counts:
            counts['output_assignments'] = counts.pop('scenarios')
        result = {'status': status, 'method': 'output_activation_partitions',
                  'stats': dict(counts, **summary)}
        if certificate is not None:
            result['certificate'] = certificate
        result.update(extra)
        return result

    def negative(kind, **fields):
        return answer('NO_FOREST', {'schema': 'activation-output-no-v1',
                      'input_sha256': data.digest, 'kind': kind, **fields})

    try:
        disconnected = _unrooted(data, work)
        if disconnected is not None:
            return negative('disconnected', vertices=disconnected)
        eligible = {row for row, edge in enumerate(data.edges)
                    if edge is not None and edge[0] != edge[1]}
        _, immutable = _peel(data, eligible, work)
        if immutable:
            return negative('immutable_stopping', rows=sorted(immutable))
        initial_trace, _ = _peel(data, (), work)
        free = {row for row, _ in initial_trace}
        raw_exceptions = _nonlinear(_owners(data))
        outgoing, incoming, seeds, sources, exceptional = _compile(data, free, work)
        columns = tuple(exceptional)
        summary.update(raw_exceptional_columns=len(raw_exceptions),
            raw_premise_budget=sum(len(v)-1 for v in raw_exceptions.values()),
            exceptional_columns=len(exceptional),
            premise_budget=sum(len(v)-1 for v in exceptional.values()),
            initially_free_rows=len(free))
        ancestors = {}
        assignments = []
        choices = [tuple(row for row, count in exceptional[column] if count == 1)
                   for column in columns]
        for outputs in product(*choices):
            work.tick('scenarios')
            selected_outputs = set(outputs)
            mandatory = [group for group in sources if group.isdisjoint(selected_outputs)]
            header = {'outputs': list(outputs)}
            if rank_layer and len(mandatory) > data.vertices - 1:
                work.tick('rank_layer_pruned_assignments')
                assignments.append(dict(header, kind='rank_layer_impossible'))
                continue
            partial, obstruction = _rainbow(data, mandatory, work)
            if obstruction is not None:
                assignments.append(dict(header, kind='mandatory_rank', **obstruction))
                continue
            guaranteed_starts = set(seeds)
            for group in mandatory:
                guaranteed_starts.update(group)
            guaranteed = _reach(guaranteed_starts, outgoing, work)
            prerequisites = sorted({row for column, target in zip(columns, outputs)
                                     for row, _ in exceptional[column]
                                     if row != target and row not in guaranteed})
            q = len(prerequisites)
            summary['maximum_distinct_prerequisites'] = max(
                summary.get('maximum_distinct_prerequisites', 0), q)
            if rank_layer and len(mandatory) + q < data.vertices - 1:
                work.tick('rank_layer_pruned_assignments')
                assignments.append(dict(header, kind='rank_layer_impossible'))
                continue
            demands = []
            for row in prerequisites:
                if row not in ancestors:
                    ancestors[row] = _reach([row], incoming, work)
                demands.append(ancestors[row] & eligible)
            required_blocks = (data.vertices - len(mandatory)) if rank_layer else None
            failures = []
            for partition in _partitions(q + 1, required_blocks):
                work.tick('partitions')
                selected_prerequisites = {row for row, block in
                                          zip(prerequisites, partition[1:]) if block != 0}
                active = _output_closure(guaranteed_starts | selected_prerequisites,
                                         outgoing, exceptional, columns, outputs, work)
                if len(active) != len(data.rows):
                    unreached = next(row for row in range(len(data.rows)) if row not in active)
                    work.tick('nonclosure_partition_prunes')
                    failures.append({'partition': partition, 'kind': 'nonclosure',
                                     'unreached': unreached})
                    continue
                groups = [set(group) for group in mandatory]
                for block in range(1, max(partition) + 1):
                    members = [demands[i] for i, value in enumerate(partition[1:])
                               if value == block]
                    group = set(members[0])
                    for member in members[1:]:
                        group.intersection_update(member)
                    groups.append(group)
                if len(groups) == len(mandatory):
                    selected, failure = partial, None
                else:
                    selected, failure = _rainbow(data, groups, work)
                if failure is None:
                    return answer('SUCCESS', _success(data, selected, work),
                                  selected_assignment=dict(header, partition=partition,
                                                           prerequisites=prerequisites))
                failures.append(dict(partition=partition, kind='rank', **failure))
            assignments.append(dict(header, kind='partitions', failures=failures))
        return negative('exhaustive_assignments', rank_layer=rank_layer,
                        assignments=assignments)
    except (ResourceLimit, RecursionError) as error:
        return answer('INCONCLUSIVE', reason=str(error))
