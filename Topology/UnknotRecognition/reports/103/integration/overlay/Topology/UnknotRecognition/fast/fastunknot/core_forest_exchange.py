"""Polynomial forest choice for a specified class of raw handle systems.

This is a graph planner, not a source authenticator or a topology recognizer.
The caller supplies the geometric 3-handle endpoint occurrences and unsigned
1-handle crossing rows after a fixed primal forest quotient. Missing endpoints
are exterior boundary. Two equal endpoints are retained as a loop.

Rows whose entrywise saturation at two has sum greater than two are required
to be deleted by 2/3 cancellation. The other rows are edges of a second graph:
two unit crossings join their columns; a single crossing joins the ground;
a repeated crossing is a loop; an empty row is a ground loop. Such rows peel
exactly when their edges form a forest. Edmonds--Fulkerson matroid partition
therefore gives a complete polynomial planner for this restricted strategy.

No maintained recognizer dispatch is changed. All failures are INCONCLUSIVE
for topology. The separate verifier imports none of this implementation.
"""

from collections import deque
from heapq import heappop, heappush


class _DisjointSets:
    def __init__(self, size):
        self.parents = list(range(size))

    def root(self, vertex):
        while self.parents[vertex] != vertex:
            self.parents[vertex] = self.parents[self.parents[vertex]]
            vertex = self.parents[vertex]
        return vertex

    def join(self, a, b):
        a, b = self.root(a), self.root(b)
        if a == b:
            return False
        self.parents[max(a, b)] = min(a, b)
        return True


def _rank(vertices, edges, selected):
    components = _DisjointSets(vertices)
    return sum(components.join(*edges[e]) for e in selected)


def _prepare(three_handles, endpoints, occurrences, check):
    check()
    three = list(three_handles)
    if any(type(v) is not int or v < 0 for v in three):
        raise ValueError('three-handle labels must be nonnegative integers')
    if len(set(three)) != len(three):
        raise ValueError('duplicate three-handle label')
    if type(endpoints) is not dict or type(occurrences) is not dict:
        raise ValueError('endpoint and occurrence maps must be dictionaries')
    if set(endpoints) != set(occurrences):
        raise ValueError('endpoint and occurrence row labels differ')
    if any(type(e) is not int or e < 0 for e in endpoints):
        raise ValueError('row labels must be nonnegative integers')
    labels = sorted(endpoints)
    three.sort()
    dual_index = {v: i + 1 for i, v in enumerate(three)}
    dual_edges, rows, columns = [], [], set()
    for e in labels:
        check()
        ends = endpoints[e]
        if type(ends) not in (list, tuple) or len(ends) > 2:
            raise ValueError('each row needs zero, one or two endpoint occurrences')
        if any(type(v) is not int or v not in dual_index for v in ends):
            raise ValueError('unknown three-handle endpoint')
        mapped = [dual_index[v] for v in ends]
        dual_edges.append(tuple(mapped + [0] * (2 - len(mapped))))
        raw = occurrences[e]
        if type(raw) is not dict:
            raise ValueError('an occurrence row must be a dictionary')
        row = {}
        for c, value in raw.items():
            if type(c) is not int or c < 0 or type(value) is not int or value < 0:
                raise ValueError('invalid nonnegative geometric occurrence')
            if value:
                row[c] = min(value, 2)
                columns.add(c)
        rows.append(row)
    return three, labels, dual_edges, rows, sorted(columns)


def _forest_path(adjacency, start, end, check):
    """Return the unique path's edge IDs, or None for different components."""
    if start == end:
        return []
    previous = [None] * len(adjacency)
    previous[start] = (-1, -1)
    queue = deque([start])
    while queue:
        check()
        vertex = queue.popleft()
        for neighbour, edge in adjacency[vertex]:
            if previous[neighbour] is not None:
                continue
            previous[neighbour] = (vertex, edge)
            if neighbour == end:
                path = []
                while neighbour != start:
                    neighbour, edge = previous[neighbour]
                    path.append(edge)
                return path
            queue.append(neighbour)
    return None


def _graphic_partition(vertex_counts, graphs, check, stats):
    """Partition a shared edge set into two forests, or return a rank witness.

    Breadth-first search uses shortest augmenting paths in the two-matroid
    exchange graph. At failure, the reached edge set Y satisfies
    |Y| > rank_G(Y) + rank_H(Y). Loops have empty exchange circuits.
    """
    count = len(graphs[0])
    colours = [-1] * count
    while -1 in colours:
        check()
        stats['searches'] += 1
        adjacency = [[[] for _ in range(n)] for n in vertex_counts]
        for e, colour in enumerate(colours):
            if colour >= 0:
                a, b = graphs[colour][e]
                adjacency[colour][a].append((b, e))
                adjacency[colour][b].append((a, e))
        previous = [None] * count
        queue = deque()
        for e, colour in enumerate(colours):
            if colour == -1:
                previous[e] = -1
                queue.append(e)
        terminal = None
        while queue and terminal is None:
            check()
            e = queue.popleft()
            for colour in (0, 1):
                if colours[e] == colour:
                    continue
                a, b = graphs[colour][e]
                path = _forest_path(adjacency[colour], a, b, check)
                if path is None:
                    terminal = (e, colour)
                    break
                for f in sorted(path):
                    stats['exchange_arcs'] += 1
                    if previous[f] is None:
                        previous[f] = e
                        queue.append(f)
        if terminal is None:
            reached = [e for e in range(count) if previous[e] is not None]
            ranks = [_rank(n, g, reached) for n, g in zip(vertex_counts, graphs)]
            if len(reached) <= sum(ranks):
                raise ArithmeticError('invalid matroid-union obstruction')
            return colours, reached, ranks
        e, target = terminal
        path = [e]
        while previous[path[-1]] != -1:
            path.append(previous[path[-1]])
        path.reverse()
        old = colours[:]
        colours[path[-1]] = target
        for j in range(len(path) - 1):
            colours[path[j]] = old[path[j + 1]]
        stats['augmentations'] += 1
        stats['recoloured_edges'] += len(path) - 1
    return colours, None, None


def _dual_schedule(three, labels, edges, forest, check):
    adjacency = [[] for _ in range(len(three) + 1)]
    for e in sorted(forest):
        a, b = edges[e]
        adjacency[a].append((b, e))
        adjacency[b].append((a, e))
    seen, queue, schedule = {0}, deque([0]), []
    while queue:
        check()
        v = queue.popleft()
        for w, e in sorted(adjacency[v], key=lambda item: item[1]):
            if w not in seen:
                seen.add(w)
                queue.append(w)
                schedule.append([labels[e], three[w - 1]])
    if len(schedule) != len(three):
        raise ArithmeticError('dual forest did not reach every three-handle')
    return schedule


def _column_schedule(labels, rows, retained, check):
    totals, incident = {}, {}
    for e in sorted(retained):
        for column, weight in rows[e].items():
            totals[column] = totals.get(column, 0) + weight
            incident.setdefault(column, set()).add(e)
    queue = [c for c in sorted(totals) if totals[c] == 1]
    # An ascending list is a valid heap.
    alive, schedule = set(retained), []
    while queue:
        check()
        c = heappop(queue)
        if totals[c] != 1:
            continue
        e = next(iter(incident[c]))
        alive.remove(e)
        schedule.append([labels[e], c])
        for h, weight in rows[e].items():
            totals[h] -= weight
            incident[h].remove(e)
            if totals[h] == 1:
                heappush(queue, h)
    if alive:
        raise ArithmeticError('a purported occurrence forest did not peel')
    return schedule


def plan_forest_exchange(three_handles, endpoints, occurrences, *, check=lambda: None):
    """Return a full graph schedule or a certified obstruction to this strategy.

    ``three_handles`` lists source 3-handle IDs. ``endpoints`` maps every
    2-handle ID to a list of 0..2 3-handle endpoint occurrences; missing ends
    mean exterior boundary. ``occurrences`` maps the same IDs to sparse
    nonnegative integer counts on a fixed set of surviving 1-handles.

    COMPLETE refers only to this combinatorial cancellation model. The source
    geometric gate, component census, boundary-pattern transport and knot
    interpretation are responsibilities of an authenticated caller.
    """
    three, labels, dual_edges, rows, columns = _prepare(
        three_handles, endpoints, occurrences, check)
    stats = dict(searches=0, augmentations=0, exchange_arcs=0, recoloured_edges=0)
    result = dict(status='INCONCLUSIVE', scope='supplied graph cancellation strategy',
                  stats=stats)
    proof = dict(schema='core-forest-exchange-v1')
    vertices = len(three) + 1
    all_components = _DisjointSets(vertices)
    for a, b in dual_edges:
        check()
        all_components.join(a, b)
    missing = [i for i in range(1, vertices) if all_components.root(i) != 0]
    if missing:
        component = all_components.root(missing[0])
        proof.update(kind='boundary_disconnected',
                     vertices=[three[i - 1] for i in missing
                               if all_components.root(i) == component])
        result.update(reason=proof['kind'], certificate=proof)
        return result

    forced = [e for e, row in enumerate(rows) if sum(row.values()) > 2]
    contraction = _DisjointSets(vertices)
    cyclic = False
    for e in forced:
        check()
        if not contraction.join(*dual_edges[e]):
            cyclic = True
    if cyclic:
        proof.update(kind='forced_long_cycle', rows=[labels[e] for e in forced],
                     rank=_rank(vertices, dual_edges, forced))
        result.update(reason=proof['kind'], certificate=proof)
        return result

    forced_set = set(forced)
    short = [e for e in range(len(labels)) if e not in forced_set]
    roots = sorted({contraction.root(v) for v in range(vertices)})
    root_index = {v: i for i, v in enumerate(roots)}
    contracted = [(root_index[contraction.root(a)], root_index[contraction.root(b)])
                  for e in short for a, b in [dual_edges[e]]]
    column_index = {c: i + 1 for i, c in enumerate(columns)}
    occurrence_edges = []
    for e in short:
        ends = [column_index[c] for c in sorted(rows[e]) for _ in range(rows[e][c])]
        occurrence_edges.append(tuple(ends + [0] * (2 - len(ends))))
    stats.update(forced_long_rows=len(forced), short_rows=len(short))
    colours, witness, ranks = _graphic_partition(
        (len(roots), len(columns) + 1), (contracted, occurrence_edges), check, stats)
    # A maximum partial partition also extends to a dual spanning tree using
    # occurrence-forest edges: an unassigned edge joining dual components
    # would itself augment the partition and contradict maximality.
    span = _DisjointSets(len(roots))
    for e, colour in enumerate(colours):
        if colour == 0:
            span.join(*contracted[e])
    for e in range(len(short)):
        check()
        if span.join(*contracted[e]):
            if colours[e] == -1:
                raise ArithmeticError('unassigned edge augmented a maximum partition')
            colours[e] = 0
    forest = forced_set | {short[e] for e, colour in enumerate(colours) if colour == 0}
    retained = set(range(len(labels))) - forest
    top_schedule = _dual_schedule(three, labels, dual_edges, forest, check)
    if witness is not None:
        unassigned = [short[e] for e, colour in enumerate(colours) if colour == -1]
        proof.update(kind='short_row_rank_obstruction',
                     rows=[labels[short[e]] for e in witness], ranks=ranks,
                     deficiency=len(unassigned),
                     dual_forest=[labels[e] for e in sorted(forest)],
                     two_three_cancellations=top_schedule,
                     occurrence_forest=[labels[short[e]] for e, colour in enumerate(colours)
                                        if colour == 1],
                     unassigned_rows=[labels[e] for e in unassigned])
        result.update(reason=proof['kind'], certificate=proof)
        return result
    proof.update(kind='complete', dual_forest=[labels[e] for e in sorted(forest)],
                 two_three_cancellations=top_schedule,
                 one_two_cancellations=_column_schedule(labels, rows, retained, check))
    result.update(status='COMPLETE', certificate=proof,
                  retained_rows=[labels[e] for e in sorted(retained)])
    check()
    return result
