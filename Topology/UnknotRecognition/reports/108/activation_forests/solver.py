"""Exact forest selection through ordered nonlinear activation scenarios.

Unary columns reduce to reachability.  A nonlinear column is fired at most
once, after all rows except a unit target have activated.  Ordered output
scenarios leave at most P antecedent demands.  Partitioning demands by their
shared seed converts each scenario to graphic/partition matroid intersection.

The shortest augmenting-path implementation below adapts the classical
graphic/partition implementation in ProveIt's incoming Dual Forest
Normalization package (12 October 2026), adding edge clones for overlapping
groups.  That package and Rado's theorem are credited in the article.
"""

from collections import deque
from itertools import permutations, product

from .model import parse_problem, integer


class ResourceLimit(RuntimeError):
    pass


class Work:
    def __init__(self, maximum=None, scenarios=None, partitions=None):
        for value in (maximum, scenarios, partitions):
            if value is not None and (not integer(value) or value < 0):
                raise ValueError('resource limits must be nonnegative integers or None')
        self.maximum = maximum
        self.scenarios = scenarios
        self.partitions = partitions
        self.total = 0
        self.counts = {}

    def tick(self, label, amount=1):
        self.counts[label] = self.counts.get(label, 0) + amount
        self.total += amount
        if self.maximum is not None and self.total > self.maximum:
            raise ResourceLimit('structural work limit')
        if label == 'scenarios' and self.scenarios is not None:
            if self.counts[label] > self.scenarios:
                raise ResourceLimit('scenario limit')
        if label == 'partitions' and self.partitions is not None:
            if self.counts[label] > self.partitions:
                raise ResourceLimit('demand partition limit')

    def export(self):
        return dict(self.counts, structural_work=self.total)


class DSU:
    def __init__(self):
        self.parent = {}
        self.size = {}

    def find(self, vertex):
        if vertex not in self.parent:
            self.parent[vertex] = vertex
            self.size[vertex] = 1
        top = vertex
        while self.parent[top] != top:
            top = self.parent[top]
        while self.parent[vertex] != vertex:
            previous = vertex
            vertex = self.parent[vertex]
            self.parent[previous] = top
        return top

    def join(self, a, b):
        a, b = self.find(a), self.find(b)
        if a == b:
            return False
        if self.size[a] < self.size[b]:
            a, b = b, a
        self.parent[b] = a
        self.size[a] += self.size[b]
        return True


def _unrooted(data, work):
    adjacency = {0: []}
    for edge in data.edges:
        work.tick('graph_edge_visits')
        if edge is not None:
            a, b = edge
            adjacency.setdefault(a, []).append(b)
            adjacency.setdefault(b, []).append(a)
    if len(adjacency) < data.vertices:
        absent = 0
        for vertex in sorted(adjacency):
            if vertex != absent:
                break
            absent += 1
        return [absent]
    reached, queue = {0}, deque([0])
    while queue:
        for v in adjacency[queue.popleft()]:
            work.tick('graph_arc_visits')
            if v not in reached:
                reached.add(v)
                queue.append(v)
    return None if len(reached) == data.vertices else sorted(set(adjacency) - reached)


def _peel(data, excluded, work):
    live = set(range(len(data.rows))) - set(excluded)
    totals, owners = {}, {}
    for row in sorted(live):
        work.tick('peel_row_visits')
        for col, count in data.rows[row]:
            work.tick('peel_incidence_visits')
            totals[col] = totals.get(col, 0) + count
            owners[col] = owners.get(col, 0) ^ row
    queue = deque(sorted(c for c, a in totals.items() if a == 1))
    trace = []
    while queue:
        col = queue.popleft()
        work.tick('peel_queue_pops')
        if totals[col] != 1:
            continue
        row = owners[col]
        if row not in live:
            raise AssertionError('invalid sole row in peel queue')
        live.remove(row)
        trace.append([row, col])
        for c, a in data.rows[row]:
            work.tick('peel_removal_visits')
            totals[c] -= a
            owners[c] ^= row
            if totals[c] == 1:
                queue.append(c)
    work.tick('peel_calls')
    return trace, live


def _owners(data, excluded=()):
    omitted = set(excluded)
    owners = {}
    for r, row in enumerate(data.rows):
        if r not in omitted:
            for c, a in row:
                owners.setdefault(c, []).append((r, a))
    return owners


def _nonlinear(owners):
    return {c: values for c, values in sorted(owners.items())
            if len(values) >= 3 and any(a == 1 for _, a in values)}


def parameters(problem):
    """Report exact raw and automatically peeled nonlinear parameters."""
    data = parse_problem(problem)
    work = Work()
    trace, _ = _peel(data, (), work)
    free = {row for row, _ in trace}
    initial = _nonlinear(_owners(data))
    residual = _nonlinear(_owners(data, free))
    return {'raw_exceptional_columns': len(initial),
            'raw_premise_budget': sum(len(v) - 1 for v in initial.values()),
            'exceptional_columns': len(residual),
            'premise_budget': sum(len(v) - 1 for v in residual.values()),
            'initially_free_rows': len(free),
            'raw_parity': data.raw_parity,
            'raw_unit_triple_regime': all(len(v) == 3 and all(a == 1 for _, a in v)
                                        for v in initial.values()),
            'unit_triple_regime': all(len(v) == 3 and all(a == 1 for _, a in v)
                                    for v in residual.values())}


def _compile(data, free, work):
    owners = _owners(data, free)
    outgoing = [[] for _ in data.rows]
    incoming = [[] for _ in data.rows]
    seeds = set(free)
    exceptional = {}
    for col, values in sorted(owners.items()):
        work.tick('compiled_incidence_visits', len(values))
        if not any(a == 1 for _, a in values):
            continue
        if len(values) >= 3:
            exceptional[col] = tuple(values)
        elif len(values) == 1:
            seeds.add(values[0][0])
        else:
            for target, count in values:
                if count == 1:
                    source = values[1][0] if target == values[0][0] else values[0][0]
                    outgoing[source].append(target)
                    incoming[target].append(source)
                    work.tick('unary_arcs')
    seen, finish = set(), []
    for start in range(len(data.rows)):
        if start in seen:
            continue
        seen.add(start)
        stack = [(start, 0)]
        while stack:
            u, i = stack[-1]
            work.tick('scc_steps')
            if i < len(outgoing[u]):
                v = outgoing[u][i]
                stack[-1] = (u, i + 1)
                if v not in seen:
                    seen.add(v)
                    stack.append((v, 0))
            else:
                finish.append(u)
                stack.pop()
    component = [-1] * len(data.rows)
    groups = []
    for start in reversed(finish):
        if component[start] != -1:
            continue
        index, group, stack = len(groups), [], [start]
        component[start] = index
        while stack:
            u = stack.pop()
            group.append(u)
            work.tick('scc_vertices')
            for v in incoming[u]:
                if component[v] == -1:
                    component[v] = index
                    stack.append(v)
        groups.append(set(group))
    source = [True] * len(groups)
    for u, targets in enumerate(outgoing):
        for v in targets:
            if component[u] != component[v]:
                source[component[v]] = False
    source_groups = sorted((g for i, g in enumerate(groups)
                            if source[i] and seeds.isdisjoint(g)),
                           key=lambda group: min(group))
    return outgoing, incoming, seeds, source_groups, exceptional


def _reach(starts, adjacency, work):
    reached, queue = set(starts), deque(starts)
    while queue:
        for v in adjacency[queue.popleft()]:
            work.tick('reach_arc_visits')
            if v not in reached:
                reached.add(v)
                queue.append(v)
    return reached


def _rank(data, rows, work):
    dsu, rank = DSU(), 0
    for row in sorted(set(rows)):
        work.tick('graphic_edge_visits')
        edge = data.edges[row]
        if edge is not None and dsu.join(*edge):
            rank += 1
    return rank


def _rainbow(data, groups, work):
    """Find distinct graphic-independent representatives of overlapping groups.

    Every row/group membership is a separate clone with the same endpoints.
    The graphic matroid makes two clones of one row parallel, so it forbids
    reusing an edge for distinct blocks.  Shared demands are handled before
    this call by putting them in the same partition block.
    """
    clones = [(row, color) for color, group in enumerate(groups)
              for row in sorted(group) if data.edges[row] is not None
              and data.edges[row][0] != data.edges[row][1]]
    work.tick('clones_created', len(clones))
    chosen = set()

    def independent(members):
        work.tick('graphic_oracle_calls')
        dsu = DSU()
        for clone in sorted(members):
            work.tick('graphic_oracle_edge_visits')
            if not dsu.join(*data.edges[clones[clone][0]]):
                return False
        return True

    while len(chosen) < len(groups):
        work.tick('matroid_rounds')
        outside = [i for i in range(len(clones)) if i not in chosen]
        used = {clones[i][1] for i in chosen}
        sources = [i for i in outside if independent(chosen | {i})]
        previous = {i: None for i in sources}
        queue, target = deque(sources), None
        while queue:
            u = queue.popleft()
            work.tick('exchange_pops')
            if u not in chosen and clones[u][1] not in used:
                target = u
                break
            if u not in chosen:
                adjacent = [v for v in sorted(chosen)
                            if clones[v][1] == clones[u][1]]
                work.tick('partition_exchange_tests', len(chosen))
            else:
                adjacent = [v for v in outside
                            if independent((chosen - {u}) | {v})]
            for v in adjacent:
                if v not in previous:
                    previous[v] = u
                    queue.append(v)
        if target is None:
            reachable_colors = {clones[i][1] for i in previous}
            deficient = [i for i in range(len(groups)) if i not in reachable_colors]
            union = set().union(*(groups[i] for i in deficient)) if deficient else set()
            rank = _rank(data, union, work)
            if not deficient or rank >= len(deficient):
                raise AssertionError('failed augmentation has no Rado defect')
            return None, {'groups': deficient, 'rank': rank}
        path = []
        while target is not None:
            path.append(target)
            target = previous[target]
        chosen.symmetric_difference_update(path)
        work.tick('augmentations')
        work.tick('augmentation_path_vertices', len(path))
        if len({clones[i][1] for i in chosen}) != len(chosen) or not independent(chosen):
            raise AssertionError('shortest exchange path lost independence')
    return sorted(clones[i][0] for i in chosen), None


def _partitions(size, blocks=None):
    """Restricted-growth encodings of set partitions, lexicographic order."""
    if size == 0:
        if blocks in (None, 0):
            yield []
        return
    word = [0] * size

    def visit(index, largest):
        if blocks is not None and (largest + 1 > blocks
                or largest + 1 + size - index < blocks):
            return
        if index == size:
            yield word.copy()
            return
        for color in range(largest + 2):
            word[index] = color
            yield from visit(index + 1, max(largest, color))

    yield from visit(1, 0)


def _block_groups(demands, partition):
    groups = [None] * (max(partition, default=-1) + 1)
    for demand, color in zip(demands, partition):
        groups[color] = set(demand) if groups[color] is None else groups[color] & demand
    return groups


def _success(data, seeds, work):
    dsu, tree = DSU(), set()
    for row in seeds:
        edge = data.edges[row]
        if edge is None or not dsu.join(*edge):
            raise AssertionError('selected activation seeds are not a forest')
        tree.add(row)
    for row, edge in enumerate(data.edges):
        work.tick('tree_extension_edges')
        if edge is not None and row not in tree and dsu.join(*edge):
            tree.add(row)
    if len(tree) != data.vertices - 1:
        raise AssertionError('connected forest failed to extend to a tree')
    trace, residual = _peel(data, tree, work)
    if residual:
        raise AssertionError('activation scenario did not imply original peeling')
    return {'schema': 'activation-forest-success-v1', 'input_sha256': data.digest,
            'tree': sorted(tree), 'peeling': trace}


def solve(problem, *, max_work=None, max_scenarios=None, max_partitions=None,
          use_rank_layer=True):
    """Decide existence of a top tree whose complement completely peels.

    SUCCESS and NO_FOREST carry independently checkable certificates.
    INCONCLUSIVE is returned on the supplied resource caps, never NO_FOREST.
    The top graph is required to be connected, with vertex zero its root.
    None edges and loops can never be selected as activation seeds.
    """
    data = parse_problem(problem)
    if type(use_rank_layer) is not bool:
        raise ValueError('use_rank_layer must be Boolean')
    work = Work(max_work, max_scenarios, max_partitions)
    rank_layer = use_rank_layer and data.raw_parity
    summary = {'raw_parity': data.raw_parity, 'rank_layer_active': rank_layer,
               'graph_rank_if_connected': data.vertices - 1}

    def answer(status, certificate=None, **extra):
        result = {'status': status, 'method': 'ordered_activation_partitions',
                  'stats': dict(work.export(), **summary)}
        if certificate is not None:
            result['certificate'] = certificate
        result.update(extra)
        return result

    def negative(kind, **fields):
        return answer('NO_FOREST', {'schema': 'activation-forest-no-v1',
                      'input_sha256': data.digest, 'kind': kind, **fields})

    try:
        disconnected = _unrooted(data, work)
        if disconnected is not None:
            return negative('disconnected', vertices=disconnected)
        eligible = {r for r, e in enumerate(data.edges)
                    if e is not None and e[0] != e[1]}
        _, immutable = _peel(data, eligible, work)
        if immutable:
            return negative('immutable_stopping', rows=sorted(immutable))
        initial_trace, _ = _peel(data, (), work)
        free = {r for r, _ in initial_trace}
        raw_exceptions = _nonlinear(_owners(data))
        outgoing, incoming, seeds, sources, exceptional = _compile(data, free, work)
        columns = tuple(exceptional)
        summary.update(raw_exceptional_columns=len(raw_exceptions),
            raw_premise_budget=sum(len(v)-1 for v in raw_exceptions.values()),
            exceptional_columns=len(exceptional),
            premise_budget=sum(len(v)-1 for v in exceptional.values()),
            initially_free_rows=len(free))
        ancestors = {}
        branches = []
        for order in permutations(columns):
            choices = [tuple(r for r, a in exceptional[c] if a == 1) for c in order]
            for outputs in product(*choices):
                work.tick('scenarios')
                selected_outputs = set(outputs)
                mandatory = [g for g in sources if g.isdisjoint(selected_outputs)]
                header = {'order': list(order), 'outputs': list(outputs)}
                if rank_layer and len(mandatory) > data.vertices - 1:
                    work.tick('rank_layer_pruned_scenarios')
                    branches.append(dict(header, kind='rank_layer_impossible'))
                    continue
                partial, obstruction = _rainbow(data, mandatory, work)
                if obstruction is not None:
                    branches.append(dict(header, kind='mandatory_rank', **obstruction))
                    continue
                guaranteed_seeds = seeds | set().union(*mandatory) if mandatory else set(seeds)
                guaranteed = _reach(guaranteed_seeds, outgoing, work)
                demands, demand_events = [], []
                for event, (column, target) in enumerate(zip(order, outputs)):
                    for row, _ in exceptional[column]:
                        if row != target and row not in guaranteed:
                            if row not in ancestors:
                                ancestors[row] = _reach([row], incoming, work)
                            demand = ancestors[row] & eligible
                            if any(not group.isdisjoint(demand) for group in mandatory):
                                raise AssertionError('mandatory source can meet a residual demand')
                            demands.append(demand)
                            demand_events.append([event, row])
                    guaranteed.update(_reach([target], outgoing, work))
                summary['maximum_demands'] = max(summary.get('maximum_demands', 0), len(demands))
                if rank_layer and len(mandatory) + len(demands) < data.vertices - 1:
                    work.tick('rank_layer_pruned_scenarios')
                    branches.append(dict(header, kind='rank_layer_impossible'))
                    continue
                empty = next((i for i, demand in enumerate(demands) if not demand), None)
                if empty is not None:
                    branches.append(dict(header, kind='empty_demand', demand=empty))
                    continue
                if not demands:
                    return answer('SUCCESS', _success(data, partial, work),
                                  selected_scenario=header)
                failures = []
                required_blocks = data.vertices - 1 - len(mandatory) if rank_layer else None
                for partition in _partitions(len(demands), required_blocks):
                    work.tick('partitions')
                    groups = mandatory + _block_groups(demands, partition)
                    selected, failure = _rainbow(data, groups, work)
                    if failure is None:
                        return answer('SUCCESS', _success(data, selected, work),
                                      selected_scenario=dict(header, partition=partition,
                                                             demand_events=demand_events))
                    failures.append(dict(partition=partition, **failure))
                branches.append(dict(header, kind='partitions', failures=failures))
        return negative('exhaustive_scenarios', rank_layer=rank_layer, branches=branches)
    except (ResourceLimit, RecursionError) as error:
        return answer('INCONCLUSIVE', reason=str(error))
