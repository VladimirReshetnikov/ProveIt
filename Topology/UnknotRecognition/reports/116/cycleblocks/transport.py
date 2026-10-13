"""Exact positive transport circuits and deferred primal forests.

These functions preserve unsigned arithmetic, not ordered embedded curves.
Uncapped counts are necessary for the graph-parity contract.
"""
from __future__ import annotations
from collections.abc import Mapping
from .core import normalize, verify_plan, _nat


def transport_circuit(counts, plan, weights=None, *, allowed=None):
    clean, w, ok = normalize(counts, weights, allowed)
    if not verify_plan(clean, plan, w, allowed=ok):
        raise ValueError('invalid source-private matrix plan')
    pairs = [tuple(p) for p in plan['cancellations']]
    pivot_index = {c: i for i, (_, c) in enumerate(pairs)}
    chosen = {r for r, _ in pairs}
    nodes = []
    for i, (r, pivot) in enumerate(pairs):
        outside, later = [], []
        for c, a in sorted(clean[r].items()):
            if c == pivot: continue
            if c in pivot_index:
                j = pivot_index[c]
                if j <= i: raise ArithmeticError('nontriangular donor')
                later.append([j, a])
            else: outside.append([c, a])
        nodes.append(dict(row=r, pivot=pivot, outside=outside, later=later))
    passive = []
    for r in sorted(set(clean) - chosen):
        outside, refs = [], []
        for c, a in sorted(clean[r].items()):
            if c in pivot_index: refs.append([pivot_index[c], a])
            else: outside.append([c, a])
        passive.append(dict(row=r, outside=outside, refs=refs))
    return dict(schema='source-private-positive-circuit-v1', nodes=nodes,
                passive=passive,
                outside_columns=sorted({c for row in clean.values() for c in row
                                        if c not in pivot_index}))


def _validate_circuit(circuit):
    if not isinstance(circuit, Mapping) or circuit.get('schema') != 'source-private-positive-circuit-v1':
        raise ValueError('unknown circuit schema')
    nodes, passive = circuit['nodes'], circuit['passive']
    if type(nodes) is not list or type(passive) is not list:
        raise ValueError('invalid node inventory')
    outside = circuit['outside_columns']
    if type(outside) is not list or outside != sorted(set(outside)):
        raise ValueError('outside columns must be sorted and unique')
    for c in outside: _nat(c, 'outside column')
    external = set(outside)
    rows, pivots = set(), set()
    for i, node in enumerate(nodes):
        r, c = node['row'], node['pivot']
        _nat(r, 'donor row'); _nat(c, 'pivot')
        if r in rows or c in pivots or c in external: raise ValueError('repeated donor/pivot')
        rows.add(r); pivots.add(c)
        _pairs(node['outside'], lambda j: j in external)
        _pairs(node['later'], lambda j: i < j < len(nodes))
    for item in passive:
        r = item['row']; _nat(r, 'passive row')
        if r in rows: raise ValueError('repeated passive row')
        rows.add(r)
        _pairs(item['outside'], lambda j: j in external)
        _pairs(item['refs'], lambda j: j < len(nodes))
    return nodes, passive


def _pairs(items, valid):
    if type(items) is not list: raise ValueError('expected a list of coefficient pairs')
    seen = set()
    for pair in items:
        if type(pair) is not list or len(pair) != 2: raise ValueError('bad coefficient pair')
        j, a = pair
        _nat(j, 'reference'); _nat(a, 'coefficient')
        if not a or j in seen or not valid(j): raise ValueError('invalid or repeated reference')
        seen.add(j)


def evaluate_circuit(circuit, observable):
    """Evaluate one integer linear observable on every unresolved source row.

    observable maps surviving columns to integers. Missing columns have value 0.
    The circuit is validated arithmetically but is not independently source-bound.
    """
    nodes, passive = _validate_circuit(circuit)
    if not isinstance(observable, Mapping): raise ValueError('observable must be a mapping')
    for c, v in observable.items():
        _nat(c, 'observable column')
        if type(v) is not int: raise ValueError('observable values must be integers')
    vals = [0] * len(nodes)
    for i in reversed(range(len(nodes))):
        node = nodes[i]
        vals[i] = (sum(a * observable.get(c, 0) for c, a in node['outside'])
                   + sum(a * vals[j] for j, a in node['later']))
    return {item['row']: sum(a * observable.get(c, 0) for c, a in item['outside'])
            + sum(a * vals[j] for j, a in item['refs']) for item in passive}


def expand_circuit(circuit, *, max_output_entries=1_000_000):
    """Explicit residual expansion. The output guard is not a memory hard limit.

    Use evaluate_circuit instead when only totals or marked linear queries are
    needed. Empty residual rows are deliberately retained.
    """
    nodes, passive = _validate_circuit(circuit)
    _nat(max_output_entries, 'output entry limit')
    vals = [{} for _ in nodes]
    count = 0
    def combine(outside, refs):
        nonlocal count
        answer = dict(outside)
        for j, a in refs:
            for c, b in vals[j].items(): answer[c] = answer.get(c, 0) + a * b
        count += len(answer)
        if count > max_output_entries:
            raise ValueError('explicit expansion allowance exhausted; use a circuit observable')
        return answer
    for i in reversed(range(len(nodes))):
        vals[i] = combine(nodes[i]['outside'], nodes[i]['later'])
    return {item['row']: combine(item['outside'], item['refs']) for item in passive}


def deferred_forest(n_vertices, edges, counts, plan, *, forced_forest=(), weights=None,
                    allowed=None):
    """Extend a fixed forest disjoint from pivots after checking uncapped parity.

    edges is a mapping column -> [endpoint, endpoint], including unused handles.
    This checks cycle-space parity, not embedded handle-chart authenticity.
    """
    _nat(n_vertices, 'vertex count')
    clean, w, ok = normalize(counts, weights, allowed)
    if not verify_plan(clean, plan, w, allowed=ok): raise ValueError('invalid matrix plan')
    if not isinstance(edges, Mapping): raise ValueError('edges must map source labels to endpoints')
    graph = {}
    for c, pair in edges.items():
        _nat(c, 'edge label')
        if not isinstance(pair, (tuple, list)) or len(pair) != 2: raise ValueError('bad endpoints')
        u, v = pair; _nat(u, 'endpoint'); _nat(v, 'endpoint')
        if u >= n_vertices or v >= n_vertices: raise ValueError('endpoint out of range')
        graph[c] = (u, v)
    for r, row in clean.items():
        odd = set()
        for c, a in row.items():
            if c not in graph: raise ValueError('count references a missing source edge')
            if a % 2:
                for v in graph[c]:
                    if v in odd: odd.remove(v)
                    else: odd.add(v)
        if odd: raise ValueError(f'uncapped cycle parity fails in row {r}')
    pivots = {c for _, c in plan['cancellations']}
    parent, size = list(range(n_vertices)), [1] * n_vertices
    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]; v = parent[v]
        return v
    def add(c):
        u, v = map(root, graph[c])
        if u == v: return False
        if size[u] < size[v]: u, v = v, u
        parent[v] = u; size[u] += size[v]
        return True
    tree, seen = [], set()
    for c in forced_forest:
        _nat(c, 'forced forest edge')
        if c not in graph or c in seen or c in pivots or not add(c):
            raise ValueError('forced forest is invalid, cyclic, or uses a pivot')
        seen.add(c); tree.append(c)
    for c in sorted(set(graph) - pivots - seen):
        if add(c): tree.append(c)
    for u, v in graph.values():
        if root(u) != root(v):
            raise ArithmeticError('private pivots violated the proved coforest property')
    return dict(schema='deferred-matrix-forest-v1', forest=tree,
                pivot_edges=sorted(pivots),
                components=len({root(v) for v in range(n_vertices)}),
                parity_checked=True, source_geometry_authenticated=False)
