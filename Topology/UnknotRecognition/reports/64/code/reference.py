"""Independent finite graph, incidence-minor, and ribbon-surface oracles.

No import from disc_basis. These routines use deliberately different algorithms.
"""
from itertools import combinations


def partitions(r):
    if r < 1:
        raise ValueError("positive size required")
    def rec(prefix, hi):
        if len(prefix) == r:
            yield tuple(prefix)
        else:
            for x in range(hi+2):
                yield from rec(prefix+[x], max(hi, x))
    yield from rec([0], 0)


def graph_data(p, q):
    if len(p) != len(q) or not p:
        raise ValueError("nonempty matching interfaces required")
    k, ell = max(p)+1, max(q)+1
    adj = [[] for _ in range(k+ell)]
    for a, b in zip(p, q):
        adj[a].append(k+b)
        adj[k+b].append(a)
    seen = set()
    components = 0
    for start in range(k+ell):
        if start in seen:
            continue
        components += 1
        seen.add(start)
        stack = [start]
        while stack:
            for v in adj[stack.pop()]:
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
    return {"vertices": k+ell, "edges": len(p), "components": components,
            "cycle_rank": len(p)-k-ell+components}


def compatible(p, q):
    g = graph_data(p, q)
    return g["components"] == 1 and g["cycle_rank"] == 0


def acyclic(p, q):
    return graph_data(p, q)["cycle_rank"] == 0


def gf2_rank(rows):
    pivots = {}
    for x in rows:
        while x:
            j = x.bit_length()-1
            if j not in pivots:
                pivots[j] = x
                break
            x ^= pivots[j]
    return len(pivots)


def minor_feature(p):
    """Compute EVERY exterior coordinate by an actual incidence determinant."""
    r = len(p)
    grouped = {}
    for v, b in enumerate(p):
        grouped.setdefault(b, []).append(v)
    edges = [(vs[0], v) for vs in grouped.values() for v in vs[1:]]
    d = len(edges)
    result = 0
    for chosen in combinations(range(1, r), d):
        rows = []
        for v in chosen:
            row = 0
            for j, (a, b) in enumerate(edges):
                if v == a or v == b:
                    row |= 1 << j
            rows.append(row)
        if gf2_rank(rows) == d:
            index = sum(1 << (v-1) for v in chosen)
            result |= 1 << index
    return result


def best_cost(records, q, control="default"):
    # Both the uncompressed and representative query baseline filter by grade,
    # sort by cost, and return on the first feasible candidate.
    target_blocks = len(q)+1-(max(q)+1)
    for c in sorted(records, key=lambda c: (c.cost, c.id)):
        if c.control == control and max(c.partition)+1 == target_blocks and compatible(c.partition, q):
            return c.cost
    return None


def ribbon_boundaries(left_orders, right_orders):
    """Boundary cycles of an orientable band thickening of a bipartite graph.

    Each edge label occurs exactly once on each side. sigma records the cyclic
    orders, alpha pairs the two half-edges; boundary cycles are sigma*alpha.
    """
    n = sum(map(len, left_orders))
    if sorted(x for b in left_orders for x in b) != list(range(n)) or sorted(x for b in right_orders for x in b) != list(range(n)):
        raise ValueError("orders must each partition the edge labels")
    sigma = {}
    for side, orders in enumerate((left_orders, right_orders)):
        for b in orders:
            if not b:
                raise ValueError("no isolated vertices")
            for a, c in zip(b, b[1:]+b[:1]):
                sigma[(side, a)] = (side, c)
    unseen = set(sigma)
    count = 0
    while unseen:
        start = next(iter(unseen))
        x = start
        count += 1
        while x in unseen:
            unseen.remove(x)
            x = sigma[(1-x[0], x[1])]
    return count


def forest_join(p, q):
    """Classical acjoin on a fixed label set; return None for a cycle.

    This is a graph-partition operation, not a geometric surface gluing API.
    """
    if not acyclic(p, q):
        return None
    n = len(p)
    adj = [set() for _ in range(n)]
    for part in (p, q):
        for i in range(n):
            for j in range(i):
                if part[i] == part[j]:
                    adj[i].add(j)
                    adj[j].add(i)
    labels = [-1]*n
    label = 0
    for i in range(n):
        if labels[i] != -1:
            continue
        stack = [i]
        labels[i] = label
        while stack:
            for j in adj[stack.pop()]:
                if labels[j] == -1:
                    labels[j] = label
                    stack.append(j)
        label += 1
    return tuple(labels)


def mobius_homogeneous(cut_row, r, d):
    """Truth-table to square-free Boolean coefficients, then degree projection."""
    a = [(cut_row >> mask) & 1 for mask in range(1 << (r-1))]
    for j in range(r-1):
        for mask in range(1 << (r-1)):
            if mask & (1 << j):
                a[mask] ^= a[mask ^ (1 << j)]
    return sum(value << mask for mask, value in enumerate(a) if mask.bit_count() == d)
