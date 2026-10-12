"""Cancel native core 2/3 pairs using the actual endpoint incidence graph.

The input is a source-authenticated parallelity geometry, not an arbitrary
boundary matrix.  Interior vertex link triangles identify the 3-handles.  An
interior edge gap of weight zero has both original endpoint caps; a positive
weight extreme gap has one original cap and one exposed normal-surface cap.
The exposed boundary is one formal root.  Its rooted spanning tree specifies
geometric 2/3 cancellations while leaving the remaining 0/1 charts and their
exposed port labels available to the existing finite boundary kernel.
"""

from collections import deque


_EDGES = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
_DISJOINT_QUAD = (0, 1, 2, 2, 1, 0)


def source_core_dual_graph(geometry, *, check=lambda: None):
    """Return occurrence-level dual edges; -1 denotes exposed boundary.

    The edge number in the authenticated source is its signed union-find root.
    It is therefore a local representative with orientation parity zero.  This
    fact determines which original endpoint belongs to rank zero, including
    loop edges whose two global vertices happen to coincide.  No normal sheet
    or parallelity-base instance is expanded.
    """
    check()
    core, rows = geometry['core'], geometry['coordinates']
    owner = [-1] * (4 * len(rows))
    flag_visits = 0
    for h in core['handles3']:
        check()
        for t, v in h['link_triangles']:
            check()
            owner[4*t + v] = h['id']
            flag_visits += 1
    edges = []
    for h in core['handles2']:
        check()
        t, slot = divmod(h['edge'], 6)
        a, b = _EDGES[slot]
        row = rows[t]
        weight = row[a] + row[b] + sum(row[4:]) - row[4 + _DISJOINT_QUAD[slot]]
        left, right = owner[4*t + a], owner[4*t + b]
        if weight == 0:
            if h['rank'] != 0:
                raise ArithmeticError('zero-weight core gap has nonzero rank')
        elif h['rank'] == 0:
            right = -1
        elif h['rank'] == weight:
            left = -1
        else:
            raise ArithmeticError('a native core gap is not an extreme edge gap')
        edges.append(dict(two_handle=h['id'], ends=[left, right]))
    return dict(three_handles=len(core['handles3']), boundary_root=-1, edges=edges,
                stats=dict(vertex_flag_visits=flag_visits,
                           dual_edge_visits=len(edges)))


def source_core_dual_reduction(geometry, *, check=lambda: None):
    """Compile one rooted forest and delete its 2-handles and all 3-handles.

    Return (reduced_geometry, certificate, statistics), or None if a dual
    component cannot reach exposed boundary.  The latter is conservative;
    it is not a non-handlebody verdict.  A connected finite torus-boundary
    source satisfies root reachability, but the explicit check is retained.
    """
    check()
    graph = source_core_dual_graph(geometry, check=check)
    n = graph['three_handles']
    # Python's -1 index is the last slot, reserved for the boundary root.
    adjacent = [[] for _ in range(n + 1)]
    for edge in graph['edges']:
        check()
        a, b = edge['ends']
        adjacent[a].append((b, edge['two_handle']))
        adjacent[b].append((a, edge['two_handle']))
    reached = [False] * (n + 1)
    reached[-1] = True
    reached_count, queue, picked = 1, deque([-1]), []
    visits = 0
    while queue:
        check()
        a = queue.popleft()
        for b, e in adjacent[a]:
            check()
            visits += 1
            if not reached[b]:
                reached[b] = True
                reached_count += 1
                queue.append(b)
                picked.append(e)
    if reached_count != n + 1:
        return None
    old = geometry['core']
    removed = [False] * len(old['handles2'])
    for e in picked:
        removed[e] = True
    kept = [h for h in old['handles2'] if not removed[h['id']]]
    reduced = dict(geometry, core=dict(old, handles3=[],
        handles2=[dict(h, id=i) for i, h in enumerate(kept)]))
    proof = dict(schema='source-core-dual-forest-v1', forest=picked)
    statistics = dict(graph['stats'], adjacency_visits=visits,
                      removed_three_handles=n, removed_two_handles=len(picked),
                      retained_two_handles=len(kept))
    check()
    return reduced, proof, statistics
