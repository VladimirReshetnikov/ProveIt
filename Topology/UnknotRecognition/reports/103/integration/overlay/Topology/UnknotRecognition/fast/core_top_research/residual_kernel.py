"""Exact exceptional-row quotient of a fixed raw occurrence matrix.

Research prototype only: this module neither changes recognizer dispatch nor
authenticates geometric inputs. Nonnegative crossing counts are saturated at
two. Short rows become edges of a graph on the columns and a ground vertex.
When those edges form a forest, its free components are quotient columns;
the grounded component is omitted. The quotient preserves full peeling and
determines the exact original stopping set. Equal quotient columns are merged.

The output includes a lifted source column-leaf schedule. Its elementary
legality can be checked directly against the input matrix, independently of
the quotient construction. A short cycle is already a stopping obstruction.
"""

from collections import deque
from heapq import heappop, heappush


def _prepare(occurrences, exceptional_rows, check):
    if type(occurrences) is not dict:
        raise ValueError('occurrences must be a sparse row dictionary')
    rows, columns = {}, set()
    for r, raw in occurrences.items():
        check()
        if type(r) is not int or r < 0 or type(raw) is not dict:
            raise ValueError('row labels must be nonnegative integers')
        row = {}
        for c, count in raw.items():
            if type(c) is not int or c < 0 or type(count) is not int or count < 0:
                raise ValueError('columns and counts must be nonnegative integers')
            if count:
                row[c] = min(2, count)
                columns.add(c)
        rows[r] = row
    if exceptional_rows is None:
        exceptional = sorted(r for r in rows if sum(rows[r].values()) > 2)
    else:
        exceptional = list(exceptional_rows)
        if (any(type(r) is not int or r not in rows for r in exceptional)
                or len(set(exceptional)) != len(exceptional)):
            raise ValueError('exceptional rows must be distinct input row labels')
        exceptional.sort()
    exceptional_set = set(exceptional)
    short = sorted(set(rows) - exceptional_set)
    if any(sum(rows[r].values()) > 2 for r in short):
        raise ValueError('every nonexceptional row must have capped length at most two')
    return rows, sorted(columns), short, exceptional


def _peel(rows, check):
    """Sparse quotient queue; the audit uses a separate literal source peel."""
    support = {}
    for r, row in rows.items():
        for c, count in row.items():
            support.setdefault(c, {})[r] = count
    totals = {c: sum(incident.values()) for c, incident in support.items()}
    queue = []
    for c in sorted(totals):
        if totals[c] == 1:
            heappush(queue, c)
    active, schedule = set(rows), []
    while queue:
        check()
        c = heappop(queue)
        if totals[c] != 1:
            continue
        r = next(iter(support[c]))
        if support[c][r] != 1 or r not in active:
            raise ArithmeticError('invalid quotient leaf queue')
        schedule.append([r, c])
        active.remove(r)
        for d, count in rows[r].items():
            del support[d][r]
            totals[d] -= count
            if totals[d] == 1:
                heappush(queue, d)
    return schedule, sorted(active)


def short_forest_kernel(occurrences, *, exceptional_rows=None, check=lambda: None):
    """Build and solve an exact quotient after the caller fixes its top forest.

    Default exceptional rows are precisely those with capped length > 2.
    Callers may instead supply any exceptional row set containing those rows.
    A forest quotient preserves the exact stopping set, not just its emptiness.
    COMPLETE/INCONCLUSIVE here concern this raw matrix only, never topology.
    """
    check()
    rows, columns, short, exceptional = _prepare(occurrences, exceptional_rows, check)
    index = {c: i + 1 for i, c in enumerate(columns)}
    labels = [None] + columns
    size = len(labels)
    adjacency = [[] for _ in range(size)]
    edges, parents = {}, list(range(size))

    def root(v):
        while parents[v] != v:
            parents[v] = parents[parents[v]]
            v = parents[v]
        return v

    for r in short:
        check()
        items = sorted(rows[r].items())
        if not items:
            a = b = 0
        elif len(items) == 1:
            c, count = items[0]
            a, b = index[c], 0 if count == 1 else index[c]
        else:
            a, b = (index[c] for c, _ in items)
        edges[r] = (a, b)
        ra, rb = root(a), root(b)
        if ra == rb:
            previous, queue = {a: None}, deque([a])
            while b not in previous:
                v = queue.popleft()
                for e in adjacency[v]:
                    x, y = edges[e]
                    w = y if x == v else x
                    if w not in previous:
                        previous[w] = (v, e)
                        queue.append(w)
            cycle, v = [r], b
            while previous[v] is not None:
                v, e = previous[v]
                cycle.append(e)
            return dict(schema='residual-short-forest-kernel-v1', status='INCONCLUSIVE',
                        reason='short_row_cycle', exceptional_rows=exceptional,
                        short_cycle=sorted(cycle),
                        stats=dict(source_rows=len(rows), source_columns=len(columns),
                                   short_rows=len(short), exceptional_rows=len(exceptional)))
        parents[max(ra, rb)] = min(ra, rb)
        adjacency[a].append(r)
        adjacency[b].append(r)

    groups = {}
    for v in range(size):
        groups.setdefault(root(v), []).append(v)
    representatives = sorted(groups)
    component_of = {v: i for i, rep in enumerate(representatives) for v in groups[rep]}
    grounded = component_of[0]
    components = []
    for i, rep in enumerate(representatives):
        vertices = groups[rep]
        component_edges = sorted({e for v in vertices for e in adjacency[v]})
        components.append(dict(id=i, grounded=(i == grounded),
                               columns=[labels[v] for v in vertices if v != 0],
                               short_rows=component_edges))
    quotient = {r: {} for r in exceptional}
    for r in exceptional:
        check()
        for c, count in rows[r].items():
            k = component_of[index[c]]
            if k != grounded:
                quotient[r][k] = min(2, quotient[r].get(k, 0) + count)

    equal_columns = {}
    for k in range(len(components)):
        if k == grounded:
            continue
        signature = tuple(quotient[r].get(k, 0) for r in exceptional)
        if any(signature):
            equal_columns.setdefault(signature, []).append(k)
    types = [dict(representative=ks[0], components=ks, values=list(signature))
             for signature, ks in equal_columns.items()]
    types.sort(key=lambda item: item['representative'])
    compressed = {r: {} for r in exceptional}
    for item in types:
        for r, count in zip(exceptional, item['values']):
            if count:
                compressed[r][item['representative']] = count
    quotient_schedule, quotient_stopping = _peel(compressed, check)

    # Lift a quotient pivot by pruning its free tree toward its unique active
    # exceptional incidence. No source count update or word expansion is used.
    active_short, active_long = set(short), set(exceptional)
    source_schedule = []
    for r, k in quotient_schedule:
        check()
        hits = [(s, c, count) for s in active_long for c, count in rows[s].items()
                if component_of[index[c]] == k]
        if len(hits) != 1 or hits[0][0] != r or hits[0][2] != 1:
            raise ArithmeticError('quotient pivot has no unique source incidence')
        pivot_column = hits[0][1]
        start = index[pivot_column]
        previous, order = {start: None}, [start]
        for v in order:
            for e in adjacency[v]:
                if e not in active_short:
                    continue
                a, b = edges[e]
                w = b if a == v else a
                if w not in previous:
                    previous[w] = (v, e)
                    order.append(w)
        for v in reversed(order[1:]):
            _, e = previous[v]
            source_schedule.append([e, labels[v]])
            active_short.remove(e)
        source_schedule.append([r, pivot_column])
        active_long.remove(r)

    # The short rows of Stop(A) are the minimal subtrees connecting the active
    # exceptional incidence sites, with ground additionally pinned. Pruning
    # all unmarked nonground leaves both finds these trees and lifts a maximal
    # source peeling prefix, even when the quotient leaves a stopping set.
    marked = {0}
    for r in active_long:
        marked.update(index[c] for c in rows[r])
    degrees = [sum(e in active_short for e in incident) for incident in adjacency]
    queue = []
    for v in range(1, size):
        if v not in marked and degrees[v] == 1:
            heappush(queue, v)
    while queue:
        check()
        v = heappop(queue)
        if v in marked or degrees[v] != 1:
            continue
        e = next(e for e in adjacency[v] if e in active_short)
        a, b = edges[e]
        w = b if a == v else a
        source_schedule.append([e, labels[v]])
        active_short.remove(e)
        degrees[v] -= 1
        degrees[w] -= 1
        if w not in marked and degrees[w] == 1:
            heappush(queue, w)
    remaining = sorted(active_short | active_long)
    if sorted(active_long) != quotient_stopping:
        raise ArithmeticError('quotient stopping projection disagrees')
    stats = dict(source_rows=len(rows), source_columns=len(columns), short_rows=len(short),
                 exceptional_rows=len(exceptional), short_components=len(components),
                 free_components=len(components) - 1,
                 nonzero_quotient_columns=sum(len(item['components']) for item in types),
                 distinct_column_types=len(types),
                 quotient_nonzero_entries=sum(len(row) for row in quotient.values()),
                 compressed_nonzero_entries=sum(len(row) for row in compressed.values()),
                 source_cancellations=len(source_schedule), remaining_rows=len(remaining))
    return dict(schema='residual-short-forest-kernel-v1',
                status='COMPLETE' if not remaining else 'INCONCLUSIVE',
                reason=None if not remaining else 'quotient_stopping_set',
                exceptional_rows=exceptional, components=components,
                quotient_rows=quotient, column_types=types, compressed_rows=compressed,
                quotient_cancellations=quotient_schedule,
                quotient_stopping_rows=quotient_stopping,
                source_cancellations=source_schedule, remaining_rows=remaining, stats=stats)
