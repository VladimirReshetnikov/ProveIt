"""Literal-expansion oracle and complete direct-coloring reference.

Independent from sparse_cuts; expansion is deliberately resource-capped.
"""
from __future__ import annotations
from itertools import combinations


def expand(grammar: dict, max_vertices: int = 5000, max_edges: int = 10000) -> dict:
    from checker import validate
    validate(grammar, 0)
    sizes = []
    for node in grammar["nodes"]:
        if node["kind"] == "leaf":
            nv, ne = node["vertices"], len(node["edges"])
        else:
            cs = [node["child"]] if node["kind"] == "map" else [node["left"], node["right"]]
            maps = [node["mapping"]] if node["kind"] == "map" else [node["left_map"], node["right_map"]]
            nv = sum(sizes[c][0] for c in cs)-sum(len(m) for m in maps)+len(set(x for m in maps for x in m))
            ne = sum(sizes[c][1] for c in cs)
        if nv > max_vertices or ne > max_edges:
            raise ValueError("literal reference expansion cap exceeded")
        sizes.append((nv, ne))
    graphs = []
    for node in grammar["nodes"]:
        if node["kind"] == "leaf":
            graphs.append({"vertices": node["vertices"], "edges": [e[:] for e in node["edges"]],
                           "terminals": node["terminals"][:]})
            continue
        cs = [node["child"]] if node["kind"] == "map" else [node["left"], node["right"]]
        maps = [node["mapping"]] if node["kind"] == "map" else [node["left_map"], node["right_map"]]
        offset, es, boundary = 0, [], []
        for c, mp in zip(cs, maps):
            g = graphs[c]
            es += [[u+offset, v+offset, w] for u, v, w in g["edges"]]
            boundary += [(t+offset, group) for t, group in zip(g["terminals"], mp)]
            offset += g["vertices"]
        parent = list(range(offset))
        def find(x):
            while parent[x] != x:
                x = parent[x]
            return x
        owners = {}
        for v, group in boundary:
            if group in owners:
                parent[find(v)] = find(owners[group])
            else:
                owners[group] = v
        remap = {}
        image = [remap.setdefault(find(v), len(remap)) for v in range(offset)]
        graphs.append({"vertices": len(remap), "edges": [[image[u], image[v], w] for u, v, w in es],
                       "terminals": [image[owners[t]] for t in node["terminals"]]})
    return graphs[grammar.get("root", len(graphs)-1)]


def brute_signature(graph: dict, k: int, max_vertices: int = 20) -> dict:
    n = graph["vertices"]
    if n > max_vertices:
        raise ValueError("direct-coloring reference cap exceeded")
    out = {}
    for coloring in range(1 << n):
        cost = flags = 0
        for u, v, weight in graph["edges"]:
            a, b = (coloring >> u) & 1, (coloring >> v) & 1
            if a != b:
                cost += weight
            else:
                flags |= 1 << a
        if cost <= k:
            mask = sum(((coloring >> t) & 1) << i for i, t in enumerate(graph["terminals"]))
            key = (mask, flags)
            out[key] = min(out.get(key, k+1), cost)
    return out


def expanded_small_cut_signature(graph: dict, k: int) -> dict:
    """Benchmark comparator: explicit connected graph, tree-edge cut enumeration.

    Uses the same elementary cut-counting principle as the producer's leaf
    algorithm, but no producer routines; direct vertex enumeration remains
    the independent correctness oracle on small inputs.
    """
    n, edges, ts = graph["vertices"], graph["edges"], graph["terminals"]
    adj = [[] for _ in range(n)]
    for u, v, _ in edges:
        adj[u].append(v)
        adj[v].append(u)
    parent, order = {0: None}, [0]
    for v in order:
        for w in adj[v]:
            if w not in parent:
                parent[w] = v
                order.append(w)
    if len(order) != n:
        raise ValueError("benchmark comparator requires a connected graph")
    subtrees = {v: {v} for v in order}
    for v in reversed(order[1:]):
        subtrees[parent[v]].update(subtrees[v])
    switches = [sum(1 << v for v in subtrees[w]) for w in order[1:]]
    out, whole = {}, (1 << n)-1
    for size in range(min(k, n-1)+1):
        for chosen in combinations(switches, size):
            mask = 0
            for block in chosen:
                mask ^= block
            for coloring in (mask, whole ^ mask):
                cost = flags = 0
                for u, v, w in edges:
                    x, y = (coloring >> u) & 1, (coloring >> v) & 1
                    if x == y:
                        flags |= 1 << x
                    else:
                        cost += w
                        if cost > k:
                            break
                if cost <= k:
                    boundary = sum(((coloring >> t) & 1) << j for j, t in enumerate(ts))
                    key = (boundary, flags)
                    out[key] = min(out.get(key, k+1), cost)
    return out
