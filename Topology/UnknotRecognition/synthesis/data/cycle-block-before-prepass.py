"""Exact weighted positive-cancellation optimization by cycle-block kernels.

All output is about unsigned incidence matrices, never knot/manifold verdicts.
Adapted from report 116 (MIT No Attribution). Skeleton enumeration uses an
explicit stack and rollback transitive closure to reject directed cycles
before completing an assignment. This module is not on the verdict path.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from heapq import heappop, heappush
from typing import Callable, Iterable, Mapping


class ResourceLimit(RuntimeError):
    """A resource refusal is not an infeasibility or optimality certificate."""


@dataclass(frozen=True)
class Limits:
    max_work: int | None = 2_000_000
    max_block_rank: int | None = 12
    max_paths: int | None = 128
    max_entries: int | None = 1_000_000


class Budget:
    def __init__(self, limits: Limits, check: Callable[[], None]):
        self.limits, self.check, self.work = limits, check, 0
        self.callback_failed = False
        for name in ('max_work', 'max_block_rank', 'max_entries', 'max_paths'):
            value = getattr(limits, name)
            if value is not None and (type(value) is not int or value < 0):
                raise ValueError(f'{name} must be a nonnegative integer or None')

    def tick(self, amount: int = 1) -> None:
        self.work += amount
        try:
            self.check()
        except BaseException:
            self.callback_failed = True
            raise
        if self.limits.max_work is not None and self.work > self.limits.max_work:
            raise ResourceLimit('cumulative work allowance exhausted')


def _nat(x: object, name: str) -> int:
    if type(x) is not int or x < 0:
        raise ValueError(f'{name} must be a nonnegative integer (not bool)')
    return x


def normalize(counts: Mapping[int, Mapping[int, int]], weights=None, allowed=None,
              budget: Budget | None = None):
    if not isinstance(counts, Mapping):
        raise ValueError('counts must be a mapping of row labels to mappings')
    clean, entries = {}, 0
    for r, row in counts.items():
        _nat(r, 'row label')
        if not isinstance(row, Mapping):
            raise ValueError('each row must be a mapping')
        clean[r] = {}
        for c, a in row.items():
            if budget: budget.tick()
            _nat(c, 'column label'); _nat(a, 'occurrence count')
            if a:
                clean[r][c] = a
                entries += 1
                if budget and budget.limits.max_entries is not None:
                    if entries > budget.limits.max_entries:
                        raise ResourceLimit('input entry allowance exhausted')
    if weights is None:
        weights = {r: 1 for r in clean}
    if not isinstance(weights, Mapping) or set(weights) != set(clean):
        raise ValueError('weights must have exactly the row-label inventory')
    w = {r: _nat(weights[r], 'row weight') for r in clean}
    if allowed is None:
        ok = {(r, c) for r, row in clean.items() for c, a in row.items() if a == 1}
    else:
        ok = set()
        for pair in allowed:
            if not isinstance(pair, (tuple, list)) or len(pair) != 2:
                raise ValueError('allowed entries must be row/column pairs')
            r, c = pair
            _nat(r, 'allowed row'); _nat(c, 'allowed column')
            if clean.get(r, {}).get(c) != 1:
                raise ValueError('an allowed pivot must be an original unit entry')
            ok.add((r, c))
    return clean, w, ok


@dataclass(frozen=True)
class Edge:
    u: int
    v: int
    row: int
    col: int
    eligible: bool
    weight: int


@dataclass(frozen=True)
class Score:
    value: int
    trace: int = 0


class Arena:
    """Persistent witness DAG; flattening is iterative, never recursive."""
    def __init__(self):
        self.nodes: list[tuple] = [('empty',)]
        self.leaves: dict[int, int] = {}

    def leaf(self, edge: int) -> int:
        if edge not in self.leaves:
            self.leaves[edge] = len(self.nodes)
            self.nodes.append(('edge', edge))
        return self.leaves[edge]

    def join(self, *traces: int) -> int:
        nonempty = tuple(x for x in traces if x)
        if not nonempty: return 0
        if len(nonempty) == 1: return nonempty[0]
        self.nodes.append(('join', nonempty))
        return len(self.nodes) - 1

    def flatten(self, trace: int) -> list[int]:
        answer, pending = [], [trace]
        while pending:
            i = pending.pop()
            node = self.nodes[i]
            if node[0] == 'edge': answer.append(node[1])
            elif node[0] == 'join': pending.extend(reversed(node[1]))
        return answer


def _forced_peel(counts, allowed, budget):
    cols = {}
    for r, row in counts.items():
        for c in row: cols.setdefault(c, set()).add(r)
    queue = deque(sorted(cols))
    live, schedule = set(counts), []
    while queue:
        budget.tick()
        c = queue.popleft()
        if len(cols[c]) != 1: continue
        r = next(iter(cols[c]))
        if (r, c) not in allowed: continue
        schedule.append((r, c)); live.remove(r)
        for h in counts[r]:
            budget.tick(); cols[h].remove(r)
            if len(cols[h]) == 1: queue.append(h)
    return live, schedule


def _build_graph(counts, weights, allowed, budget):
    row_labels = sorted(counts)
    col_labels = sorted({c for r, c in allowed if r in counts})
    row_id = {r: i for i, r in enumerate(row_labels)}
    col_id = {c: i + len(row_labels) for i, c in enumerate(col_labels)}
    n = len(row_labels) + len(col_labels)
    adj = [[] for _ in range(n)]
    edges = []
    for r in row_labels:
        for c in sorted(counts[r]):
            budget.tick()
            if c not in col_id: continue  # never pivot-capable: retain in source only
            e = Edge(row_id[r], col_id[c], r, c, (r, c) in allowed, weights[r])
            adj[e.u].append(len(edges)); adj[e.v].append(len(edges)); edges.append(e)
    colors = [0] * len(row_labels) + [1] * len(col_labels)
    return adj, edges, colors


def biconnected_blocks(adj, edges, budget):
    """Iterative Tarjan decomposition; bridge edges are one-edge blocks."""
    n, clock = len(adj), 0
    discovery, low = [-1] * n, [0] * n
    parent_edge = [-1] * n
    edge_stack, blocks = [], []
    for root in range(n):
        if discovery[root] != -1: continue
        discovery[root] = low[root] = clock; clock += 1
        stack = [(root, iter(adj[root]))]
        while stack:
            v, iterator = stack[-1]
            try:
                ei = next(iterator); budget.tick()
            except StopIteration:
                stack.pop()
                pe = parent_edge[v]
                if pe >= 0:
                    e = edges[pe]; p = e.v if e.u == v else e.u
                    low[p] = min(low[p], low[v])
                    if low[v] >= discovery[p]:
                        block = []
                        while True:
                            x = edge_stack.pop(); block.append(x)
                            if x == pe: break
                        blocks.append(tuple(sorted(block)))
                continue
            if ei == parent_edge[v]: continue
            e = edges[ei]; u = e.v if e.u == v else e.u
            if discovery[u] == -1:
                parent_edge[u] = ei
                edge_stack.append(ei)
                discovery[u] = low[u] = clock; clock += 1
                stack.append((u, iter(adj[u])))
            elif discovery[u] < discovery[v]:
                edge_stack.append(ei)
                low[v] = min(low[v], discovery[u])
        if edge_stack:
            raise ArithmeticError('unclosed Tarjan edge stack')
    return blocks


def _direction(color: int, selected: int) -> int:
    return (1 if selected else -1) if color == 0 else (-1 if selected else 1)


def path_table(vertices, edge_ids, edges, colors, potentials, arena, budget):
    """Six feasible endpoint/through-direction states; internal scores included.

    potentials[v] = (occupied-by-this-block, free-for-descendants).
    Endpoints' potentials are deliberately not included.
    """
    if len(vertices) != len(edge_ids) + 1 or not edge_ids:
        raise ValueError('a path must have at least one edge')
    e0 = edges[edge_ids[0]]
    table = {}
    for a in (0, 1):
        if a and not e0.eligible: continue
        d = _direction(colors[vertices[0]], a)
        table[a, a, d] = Score(a * e0.weight, arena.leaf(edge_ids[0]) if a else 0)
    for i in range(1, len(edge_ids)):
        v, ei = vertices[i], edge_ids[i]
        edge = edges[ei]
        next_table = {}
        for (first, prev, direct), old in table.items():
            for chosen in (0, 1):
                budget.tick()
                if prev + chosen > 1 or (chosen and not edge.eligible): continue
                orient = _direction(colors[v], chosen)
                newdir = direct if direct == orient else 0
                branch = potentials[v][0 if prev or chosen else 1]
                key = first, chosen, newdir
                value = old.value + chosen * edge.weight + branch.value
                if key not in next_table or value > next_table[key].value:
                    trace = arena.join(old.trace, branch.trace,
                                       arena.leaf(ei) if chosen else 0)
                    next_table[key] = Score(value, trace)
        table = next_table
    if len(table) > 6:
        raise ArithmeticError('six-state path invariant violated')
    return table


def _acyclic(vertices, arcs):
    outgoing = {v: [] for v in vertices}
    indegree = {v: 0 for v in vertices}
    for u, v in arcs:
        outgoing[u].append(v); indegree[v] += 1
    pending = [v for v in vertices if indegree[v] == 0]
    seen = 0
    while pending:
        v = pending.pop(); seen += 1
        for u in outgoing[v]:
            indegree[u] -= 1
            if indegree[u] == 0: pending.append(u)
    return seen == len(vertices)


def _solve_block(block, root, edges, colors, potentials, arena, budget, stats):
    local = {}
    for ei in block:
        e = edges[ei]
        local.setdefault(e.u, []).append(ei); local.setdefault(e.v, []).append(ei)
    rank = len(block) - len(local) + 1
    stats['max_block_rank'] = max(stats['max_block_rank'], rank)
    stats['total_cycle_rank'] += rank
    stats['blocks'] += 1
    if budget.limits.max_block_rank is not None and rank > budget.limits.max_block_rank:
        raise ResourceLimit(f'block cycle rank {rank} exceeds allowance')
    if len(block) == 1:
        ei = block[0]; e = edges[ei]
        other = e.v if e.u == root else e.u
        free = potentials[other][1]
        matched = None
        if e.eligible:
            occupied = potentials[other][0]
            matched = Score(e.weight + occupied.value,
                            arena.join(arena.leaf(ei), occupied.trace))
        return (free, matched)
    terminals = sorted({root} | {v for v in local if len(local[v]) != 2})
    used, paths = set(), []
    terminal_set = set(terminals)
    for v in terminals:
        for ei in sorted(local[v]):
            if ei in used: continue
            vs, es, current, edge_id = [v], [], v, ei
            while True:
                budget.tick(); used.add(edge_id); es.append(edge_id)
                e = edges[edge_id]
                nxt = e.v if e.u == current else e.u
                vs.append(nxt)
                if nxt in terminal_set: break
                alternatives = local[nxt]
                following = alternatives[1] if alternatives[0] == edge_id else alternatives[0]
                current, edge_id = nxt, following
            paths.append((vs, es))
    if used != set(block): raise ArithmeticError('path decomposition missed an edge')
    if budget.limits.max_paths is not None and len(paths) > budget.limits.max_paths:
        raise ResourceLimit('branch-path enumeration depth allowance exhausted')
    if rank >= 2 and len(paths) > 3 * rank - 2:
        raise ArithmeticError('cycle-rank path bound violated')
    stats['paths'] += len(paths)
    stats['max_paths_per_block'] = max(stats['max_paths_per_block'], len(paths))
    choices = []
    for vs, es in paths:
        table = path_table(vs, es, edges, colors, potentials, arena, budget)
        stats['path_states'] += len(table)
        choices.append(sorted(table.items()))
    capacity = {v: 0 for v in terminals}
    traces = []
    best: list[Score | None] = [None, None]
    index = {v: i for i, v in enumerate(terminals)}
    reach = [0] * len(terminals)
    # Each frame holds a choice iterator, its accumulated score, and the
    # changes made by its parent edge. Exhaustion restores that exact prefix.
    stack = [(iter(choices[0]), 0, None)]
    budget.tick()
    while stack:
        iterator, value, undo = stack[-1]
        try:
            (a, b, direction), score = next(iterator)
        except StopIteration:
            stack.pop()
            if undo is not None:
                u, v, x, y, changed = undo
                capacity[u] -= x; capacity[v] -= y
                traces.pop()
                for vertex, previous in changed:
                    reach[vertex] = previous
            continue
        budget.tick()
        i = len(stack) - 1
        u, v = paths[i][0][0], paths[i][0][-1]
        if u == v:
            if capacity[u] + a + b > 1: continue
        elif capacity[u] + a > 1 or capacity[v] + b > 1:
            continue
        changed = []
        if direction:
            start, end = (index[u], index[v]) if direction == 1 else (index[v], index[u])
            if start == end or reach[end] & (1 << start):
                stats['cycle_prefix_prunes'] += 1
                continue
            successors = reach[end] | (1 << end)
            for vertex in range(len(reach)):
                budget.tick()
                if vertex == start or reach[vertex] & (1 << start):
                    updated = reach[vertex] | successors
                    if updated != reach[vertex]:
                        changed.append((vertex, reach[vertex]))
                        reach[vertex] = updated
        capacity[u] += a; capacity[v] += b
        traces.append(score.trace)
        value += score.value
        budget.tick()
        if i + 1 < len(paths):
            stack.append((iter(choices[i + 1]), value, (u, v, a, b, changed)))
            continue
        stats['kernel_assignments'] += 1
        extra, extras = 0, []
        for terminal in terminals:
            if terminal == root: continue
            s = potentials[terminal][0 if capacity[terminal] else 1]
            extra += s.value; extras.append(s.trace)
        flag = capacity[root]
        total = value + extra
        if best[flag] is None or total > best[flag].value:
            best[flag] = Score(total, arena.join(*(traces + extras)))
        traces.pop()
        capacity[u] -= a; capacity[v] -= b
        for vertex, previous in changed:
            reach[vertex] = previous
    if best[0] is None: raise ArithmeticError('empty local matching disappeared')
    return tuple(best)


def _vertex_messages(children, arena, budget):
    """At most one child block can consume the shared articulation vertex."""
    base = 0
    for a, _ in children:
        budget.tick(); base += a.value
    a_trace = arena.join(*(a.trace for a, _ in children))
    best_gain, which = 0, -1
    for i, (a, b) in enumerate(children):
        if b is not None and b.value - a.value > best_gain:
            best_gain, which = b.value - a.value, i
    b_trace = arena.join(*(b.trace if i == which else a.trace
                           for i, (a, b) in enumerate(children)))
    return Score(base, a_trace), Score(base + best_gain, b_trace)


def _solve_graph(adj, edges, colors, budget, stats):
    blocks = biconnected_blocks(adj, edges, budget)
    nv = len(adj)
    incidence = [[] for _ in range(nv + len(blocks))]
    for i, block in enumerate(blocks):
        vertices = sorted({x for ei in block for x in (edges[ei].u, edges[ei].v)})
        for v in vertices:
            incidence[nv + i].append(v); incidence[v].append(nv + i)
    parent, order, roots = [-2] * len(incidence), [], []
    for root in range(nv):
        if parent[root] != -2: continue
        roots.append(root); parent[root] = -1; pending = [root]
        while pending:
            v = pending.pop(); order.append(v)
            for u in incidence[v]:
                budget.tick()
                if u == parent[v]: continue
                if parent[u] != -2:
                    raise ArithmeticError('block incidence graph is not a forest')
                parent[u] = v; pending.append(u)
    arena, messages = Arena(), {}
    for node in reversed(order):
        budget.tick()
        children = [v for v in incidence[node] if parent[v] == node]
        if node < nv:
            messages[node] = _vertex_messages([messages[x] for x in children], arena, budget)
        else:
            root = parent[node]
            potentials = {v: messages[v] for v in children}
            messages[node] = _solve_block(blocks[node - nv], root, edges, colors,
                                          potentials, arena, budget, stats)
    total = sum(messages[r][1].value for r in roots)
    trace = arena.join(*(messages[r][1].trace for r in roots))
    selected = arena.flatten(trace)
    if len(selected) != len(set(selected)):
        raise ArithmeticError('duplicate edge in witness DAG')
    stats['witness_nodes'] = len(arena.nodes)
    return total, [(edges[i].row, edges[i].col) for i in selected]


def schedule_from_matching(counts, matching):
    """Independent source-private ordering; detects alternating cycles."""
    mate = dict(matching)
    if len(mate) != len(matching) or len(set(mate.values())) != len(mate):
        raise ValueError('not a matching')
    owner = {c: r for r, c in mate.items()}
    predecessors = {r: 0 for r in mate}
    dependencies = {r: [] for r in mate}
    for r, c in mate.items():
        if counts.get(r, {}).get(c) != 1: raise ValueError('nonunit matching entry')
    for r in mate:
        for c in counts[r]:
            if c in owner and owner[c] != r:
                dependencies[r].append(owner[c]); predecessors[owner[c]] += 1
    queue = []
    for r, d in predecessors.items():
        if d == 0: heappush(queue, r)
    answer = []
    while queue:
        r = heappop(queue); answer.append((r, mate[r]))
        for s in dependencies[r]:
            predecessors[s] -= 1
            if predecessors[s] == 0: heappush(queue, s)
    if len(answer) != len(mate): raise ValueError('matching has an alternating cycle')
    return answer


def optimize_counts(counts, weights=None, *, allowed=None, prepeel=True,
                    limits=Limits(), check=lambda: None):
    """Return an exact optimal matrix plan, or an explicitly inconclusive refusal.

    Input errors raise ValueError. Caller cancellation exceptions propagate.
    `allowed` restricts private pivots; equivalence with arbitrary fill-producing
    positive pivots is asserted only when every original unit is allowed.
    """
    budget = Budget(limits, check)
    stats = dict(blocks=0, max_block_rank=0, total_cycle_rank=0, paths=0,
                 max_paths_per_block=0, path_states=0, kernel_assignments=0,
                 witness_nodes=0, work=0, forced_rows=0, cycle_prefix_prunes=0)
    try:
        budget.tick()
        clean, weights, ok = normalize(counts, weights, allowed, budget)
        live, forced = (_forced_peel(clean, ok, budget) if prepeel
                        else (set(clean), []))
        stats['forced_rows'] = len(forced)
        remainder = {r: clean[r] for r in clean if r in live}
        adj, edges, colors = _build_graph(remainder, weights, ok, budget)
        stats['optimization_vertices'], stats['optimization_edges'] = len(adj), len(edges)
        score, matching = _solve_graph(adj, edges, colors, budget, stats)
        matching.extend(forced)
        schedule = schedule_from_matching(clean, matching)
        total = score + sum(weights[r] for r, _ in forced)
        stats['work'] = budget.work
        retained = {r for r, _ in matching}
        plan = dict(schema='cycle-block-matrix-plan-v1', status='OPTIMAL_MATRIX_PLAN',
                    cancellations=[list(p) for p in schedule],
                    cancelled_rows=sorted(retained),
                    remaining_rows=sorted(set(clean) - retained),
                    matched_weight=total,
                    deferred_weight=sum(weights.values()) - total,
                    stats=stats)
        if not verify_plan(clean, plan, weights, allowed=ok):
            raise ArithmeticError('independent source-private replay failed')
        return plan
    except ResourceLimit as exc:
        if budget.callback_failed:
            raise
        stats['work'] = budget.work
        return dict(schema='cycle-block-matrix-plan-v1', status='RESOURCE_LIMIT',
                    reason=str(exc), stats=stats)


def verify_plan(counts, plan, weights=None, *, allowed=None) -> bool:
    """Linear-incidence feasibility replay, NOT a general optimality checker."""
    try:
        if type(plan) is not dict or plan.get('schema') != 'cycle-block-matrix-plan-v1':
            return False
        clean, w, ok = normalize(counts, weights, allowed)
        if plan.get('status') != 'OPTIMAL_MATRIX_PLAN': return False
        pairs = plan['cancellations']
        pos_r, pos_c = {}, {}
        for i, pair in enumerate(pairs):
            if type(pair) is not list or len(pair) != 2: return False
            r, c = pair
            if type(r) is not int or type(c) is not int: return False
            if (r, c) not in ok or r in pos_r or c in pos_c: return False
            pos_r[r], pos_c[c] = i, i
        for r, i in pos_r.items():
            for c in clean[r]:
                if c in pos_c and pos_c[c] < i: return False
        if type(plan['cancelled_rows']) is not list or type(plan['remaining_rows']) is not list: return False
        if any(type(r) is not int for r in plan['cancelled_rows'] + plan['remaining_rows']): return False
        if plan['cancelled_rows'] != sorted(pos_r): return False
        if plan['remaining_rows'] != sorted(set(clean) - set(pos_r)): return False
        score = sum(w[r] for r in pos_r)
        return (type(plan['matched_weight']) is int and type(plan['deferred_weight']) is int
                and plan['matched_weight'] == score
                and plan['deferred_weight'] == sum(w.values()) - score)
    except (KeyError, TypeError, ValueError, AttributeError):
        return False
