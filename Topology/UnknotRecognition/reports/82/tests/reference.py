"""Literal boundary-cell oracle, deliberately independent of kernel DSU code."""
from collections import defaultdict, deque


def components(vertices, edges):
    graph = {v: [] for v in vertices}
    for a, b in edges:
        graph[a].append(b)
        graph[b].append(a)
    labels = {}
    for v in graph:
        if v in labels:
            continue
        stack = [v]
        labels[v] = v
        while stack:
            a = stack.pop()
            for b in graph[a]:
                if b not in labels:
                    labels[b] = v
                    stack.append(b)
    return labels


def literal_glue(surfaces, raw_cycles, gluings):
    """Expand every positive gap and compute an actual boundary CW quotient."""
    rows, owners, ports = [], [], {}
    active = [0]*len(surfaces)
    for owner, edges in raw_cycles:
        expanded = []
        for e in edges:
            if e.port is None:
                expanded.extend([(None, 0)]*e.length)
            else:
                expanded.append((e.port, e.reverse))
        if not expanded:
            raise ValueError('empty literal cycle')
        active[owner] += 1
        offset, m = len(owners), len(expanded)
        owners.extend([owner]*m)
        for j, (label, reverse) in enumerate(expanded):
            row = (owner, offset+j, offset+(j+1)%m, label, reverse)
            if label is not None:
                ports[label] = len(rows)
            rows.append(row)
    ce, ve, pe, used = [], [], [], set()
    for g in gluings:
        i, u, v, _, da = rows[ports[g.left]]
        j, w, z, _, db = rows[ports[g.right]]
        r = g.reverse ^ da ^ db
        ce.append((i, j))
        ve.extend(((u, z if r else w), (v, w if r else z)))
        for s in (0, 1):
            pe.append(((i, s), (j, s ^ (1 ^ r))))
        used.update((g.left, g.right))
    for i, s in enumerate(surfaces):
        if not s.orientable:
            pe.append(((i, 0), (i, 1)))
    cl = components(range(len(surfaces)), ce)
    vl = components(range(len(owners)), ve)
    pl = components([(i,s) for i in range(len(surfaces)) for s in (0,1)], pe)
    remain = [row for row in rows if row[3] not in used]
    usedv = {vl[v] for row in remain for v in row[1:3]}
    bl = components(usedv, [(vl[r[1]],vl[r[2]]) for r in remain])
    out = []
    for root in set(cl.values()):
        group = {i for i in cl if cl[i] == root}
        q0 = sum(o in group for o in owners)
        q1 = len({vl[i] for i,o in enumerate(owners) if o in group})
        k = sum(rows[ports[g.left]][0] in group for g in gluings)
        chi = sum(surfaces[i].chi for i in group) + k - q0 + q1
        passive = sum(surfaces[i].boundary-active[i] for i in group)
        b = passive + len({bl[vl[r[1]]] for r in remain if r[0] in group})
        i = next(iter(group))
        ori = pl[(i,0)] != pl[(i,1)]
        out.append((chi,b,ori))
    return tuple(sorted(out))


def finite_boundary_oracles(raw_cycles):
    from corner_kernel.oracles import ExplicitOracle
    from corner_kernel.compiler import Port
    owners, ordinary, ports = [], [], []
    for owner, edges in raw_cycles:
        expanded = []
        for e in edges:
            expanded.extend([e]*e.length if e.port is None else [e])
        offset, m = len(owners), len(expanded)
        owners.extend([owner]*m)
        for j,e in enumerate(expanded):
            a,b = offset+j,offset+(j+1)%m
            if e.port is None:
                ordinary.append((a,b))
            elif e.reverse:
                ports.append(Port(e.port, owner,b,a,1))
            else:
                ports.append(Port(e.port,owner,a,b,0))
    return tuple(ports),ExplicitOracle(len(owners),[]),ExplicitOracle(len(owners),ordinary)
