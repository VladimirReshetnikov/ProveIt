"""Optimal weighted deferral when every column meets at most two rows."""
from collections import deque
from .model import Matrix, Check, noop
from .certificates import package_plan


def reachability_graph(matrix: Matrix):
    pivot_cols = {c for row in matrix.entries.values() for c,a in row.items() if a == 1}
    columns = {c: [] for c in matrix.cols if c in pivot_cols}
    for r, row in matrix.entries.items():
        for c, a in row.items():
            if c in columns:
                columns[c].append((r, a))
    if any(len(x) > 2 for x in columns.values()):
        raise ValueError('two-incidence theorem requires pivot-capable column support at most two')
    adj = {r: set() for r in matrix.rows}; roots = set()
    for c, inc in columns.items():
        if len(inc) == 1:
            r, a = inc[0]
            if a == 1:
                roots.add(r)
        else:
            (r, a), (s, b) = inc
            if a == 1:
                adj[s].add(r)
            if b == 1:
                adj[r].add(s)
    return adj, roots


def reachable(adj, seeds, check=noop):
    found = set(seeds); queue = deque(seeds)
    while queue:
        check(); v = queue.popleft()
        for w in adj[v]:
            if w not in found:
                found.add(w); queue.append(w)
    return found


def sccs(adj, vertices, check=noop):
    # Iterative Kosaraju: avoids recursion depth limits on long native cores.
    vertices = set(vertices); seen = set(); finish = []
    for start in sorted(vertices):
        if start in seen:
            continue
        seen.add(start); stack = [(start, iter(adj[start]))]
        while stack:
            check(); v, it = stack[-1]
            w = next(it, None)
            if w is None:
                finish.append(v); stack.pop()
            elif w in vertices and w not in seen:
                seen.add(w); stack.append((w, iter(adj[w])))
    reverse = {v: [] for v in vertices}
    for v in vertices:
        for w in adj[v]:
            if w in vertices:
                reverse[w].append(v)
    assigned = set(); parts = []
    for start in reversed(finish):
        if start in assigned:
            continue
        block = []; stack = [start]; assigned.add(start)
        while stack:
            check(); v = stack.pop(); block.append(v)
            for w in reverse[v]:
                if w not in assigned:
                    assigned.add(w); stack.append(w)
        parts.append(sorted(block))
    return parts


def two_incidence_plan(counts: dict, weights: dict | None = None,
                       *, check: Check = noop) -> dict:
    matrix = Matrix.parse(counts, weights); check()
    adj, roots = reachability_graph(matrix)
    initial = reachable(adj, roots, check)
    parts = sccs(adj, set(matrix.rows) - initial, check)
    block = {v: i for i, part in enumerate(parts) for v in part}
    incoming = set()
    for v in block:
        for w in adj[v]:
            if w in block and block[v] != block[w]:
                incoming.add(block[w])
    sources = [part for i, part in enumerate(parts) if i not in incoming]
    deferred = [min(part, key=lambda r: (matrix.weights[r], r)) for part in sources]
    result = package_plan(matrix, deferred, method='two-incidence-scc',
                          stats=dict(rows=len(matrix.rows), columns=len(matrix.cols),
                                     arcs=sum(map(len, adj.values())), source_sccs=len(sources)),
                          check=check)
    result['lower_bound_certificate'] = {'schema': 'source-scc-lower-bound-v1',
                                         'source_components': sorted(sources)}
    return result


def verify_two_incidence_optimality(counts: dict, plan: dict,
                                   weights: dict | None = None, *, check: Check = noop) -> bool:
    """Check the optimality conclusion by weighted stopping-set packing.

    Does not call the SCC finder or reconstruct a reachability graph. The
    supplied source components need only satisfy the weaker stopping property.
    Soundness of this checker therefore also holds on higher-arity matrices.
    """
    from .certificates import verify_weighted_stopping_optimality
    try:
        obj=plan['lower_bound_certificate']
        if obj['schema']!='source-scc-lower-bound-v1':
            return False
        return verify_weighted_stopping_optimality(counts,plan,obj['source_components'],
                                                  weights,check=check)
    except (KeyError,TypeError):
        return False
