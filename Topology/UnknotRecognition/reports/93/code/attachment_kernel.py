"""Rooted-forest kernels for unused-handle attachment networks.

This is a combinatorial certificate producer.  The inference that a vertex
with Euler characteristic one is a ball requires independently authenticated
irreducibility of the source manifold.  No knot verdict is produced here.
"""

from __future__ import annotations

import hashlib
import json


def _source(vertices, edges):
    vs = []
    for row in vertices:
        if not isinstance(row, dict):
            raise ValueError("each vertex must be an object")
        v, chi = row.get("id"), row.get("euler_characteristic")
        if type(v) is not int or v < 0 or type(chi) is not int or chi > 1:
            raise ValueError("vertices require distinct nonnegative ids and integer chi <= 1")
        vs.append([v, chi])
    vs.sort()
    ids = {v for v, _ in vs}
    if not vs or len(ids) != len(vs):
        raise ValueError("the vertex list must be nonempty and have unique ids")
    es = []
    for row in edges:
        if not isinstance(row, dict):
            raise ValueError("each edge must be an object")
        e, ends = row.get("id"), row.get("ends")
        if type(e) is not int or e < 0 or not isinstance(ends, (list, tuple)):
            raise ValueError("invalid edge id or ends")
        if len(ends) != 2 or any(type(v) is not int or v not in ids for v in ends):
            raise ValueError("edge ends must be source vertex ids")
        es.append([e, ends[0], ends[1]])
    es.sort()
    if len({e for e, _, _ in es}) != len(es):
        raise ValueError("edge ids must be unique")
    return {"vertices": vs, "edges": es}


def _digest(source):
    raw = json.dumps(source, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def kernelize_attachment_network(vertices, edges, *, check=lambda: None):
    """Return a source-addressable, independently replayable forest quotient.

    Vertices contain ``id`` and ``euler_characteristic``; edges contain ``id``
    and ``ends``.  Parallel edges and loops are allowed.  Every nonball-type
    vertex (chi <= 0) is retained.  If all vertices have chi = 1, the least
    source vertex is retained as a single ball-type vertex.

    Runtime: O((v+e) log(v+e)) comparisons, plus quasi-linear union/find work.
    Integers and identifiers are charged at their actual binary lengths.
    The small operational graph has a linear-size source provenance forest.
    """
    check()
    source = _source(vertices, edges)
    chis = dict(source["vertices"])
    roots = sorted(v for v, chi in source["vertices"] if chi <= 0)
    nonball_count = len(roots)
    if not roots:
        roots = [source["vertices"][0][0]]
    root_set = set(roots)
    parent = {v: v for v in chis}
    size = dict.fromkeys(chis, 1)
    anchor = {v: (v if v in root_set else None) for v in chis}

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    forest = []
    for e, u, v in source["edges"]:
        check()
        a, b = find(u), find(v)
        if a == b or (anchor[a] is not None and anchor[b] is not None):
            continue
        if size[a] < size[b] or (size[a] == size[b] and a > b):
            a, b = b, a
        parent[b] = a
        size[a] += size[b]
        if anchor[a] is None:
            anchor[a] = anchor[b]
        forest.append(e)
    if any(anchor[find(v)] is None for v in chis):
        raise ValueError("the attachment graph is disconnected")
    # A disconnected graph with one or more anchored components also needs
    # rejection.  Connectivity of the quotient is checked independently.
    root_map = {v: anchor[find(v)] for v in chis}
    forest_set = set(forest)
    kept = [[e, root_map[u], root_map[v]] for e, u, v in source["edges"]
            if e not in forest_set]
    adjacency = {r: set() for r in roots}
    for _, u, v in kept:
        adjacency[u].add(v)
        adjacency[v].add(u)
    seen, stack = set(), [roots[0]]
    while stack:
        v = stack.pop()
        if v not in seen:
            seen.add(v)
            stack.extend(adjacency[v] - seen)
    if len(seen) != len(roots):
        raise ValueError("the attachment graph is disconnected")

    tree_adjacency = {v: [] for v in chis}
    for e, u, v in source["edges"]:
        if e in forest_set:
            tree_adjacency[u].append((v, e))
            tree_adjacency[v].append((u, e))
    parent_rows = []
    for r in roots:
        stack = [(r, None, None)]
        while stack:
            check()
            v, prev, e = stack.pop()
            parent_rows.append([v, prev, e])
            stack.extend((w, v, f) for w, f in tree_adjacency[v] if w != prev)
    parent_rows.sort()
    beta = len(source["edges"]) - len(source["vertices"]) + 1
    deficit = beta + sum(1 - chi for _, chi in source["vertices"])
    kernel = {
        "vertices": [[v, chis[v]] for v in roots],
        "edges": kept,
        "cycle_rank": beta,
        "euler_deficit": deficit,
        "nonball_type_vertices": nonball_count,
        "case": "all_ball_types" if nonball_count == 0 else "retained_nonball_types",
    }
    return {
        "schema": "unused-attachment-kernel-v1",
        "input_sha256": _digest(source),
        "forest_edges": forest,
        "vertex_roots": [[v, root_map[v]] for v in sorted(chis)],
        "parent_forest": parent_rows,
        "kernel": kernel,
        "trust": "combinatorial quotient only; ball substitutions require source irreducibility",
    }


def kernel_from_decomposition(decomposition, *, check=lambda: None):
    """Adapt the source-bound output of ``unused_handles`` without assuming topology."""
    return kernelize_attachment_network(
        decomposition["components"],
        [{"id": e["one_handle"], "ends": e["ends"]}
         for e in decomposition["unused_handles"]],
        check=check,
    )


def build_route_index(certificate):
    """Index the shared parent forest once in O(q) time and space."""
    return {v: (p, e) for v, p, e in certificate["parent_forest"]}


def source_route(certificate, vertex, *, index=None):
    """Expand just one source vertex's oriented forest route to its root.

    With a prebuilt ``index``, this optional operation costs the output length.
    Without one it first spends O(q) to index the parent forest.  Kernel
    construction and checking never expand all root routes.
    """
    parent = build_route_index(certificate) if index is None else index
    if vertex not in parent:
        raise ValueError("unknown source vertex")
    result, seen = [], set()
    while parent[vertex][0] is not None:
        if vertex in seen:
            raise ValueError("invalid cyclic parent forest")
        seen.add(vertex)
        p, e = parent[vertex]
        result.append([e, vertex, p])
        vertex = p
    return result
