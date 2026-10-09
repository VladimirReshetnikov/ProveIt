"""Exact integral difference optimization and independently replayed witnesses.

The sign-saturated bounded-flow construction is adapted from ProveIt's
cocycle_euler_flow.py at 8188525b70033dcfe7c51ea5ae2c8723ad0c0198.
The extension here supplies arbitrary feasible/infeasible stratum handling.
No new claim is made for the underlying minimum-cost-flow method.
"""
from __future__ import annotations
from heapq import heappop, heappush
from .model import noop, integer
from .checker import check_feasible, check_negative_cycle, check_optimum


def feasibility(n, arcs, check=noop):
    """Bellman--Ford with a zero-cost super-source implicit at every vertex."""
    if integer(n) < 1:
        raise ValueError("positive number of vertices required")
    for u, v, b in arcs:
        if not (0 <= integer(u) < n and 0 <= integer(v) < n):
            raise ValueError("constraint endpoint outside model")
        integer(b)
    p, pred = [0]*n, [None]*n
    for _ in range(n):
        last = None
        for i, (u, v, b) in enumerate(arcs):
            check()
            q = p[u]+b
            if p[v] > q:
                p[v], pred[v], last = q, i, v
        if last is None:
            answer = {'status': 'FEASIBLE', 'potential': p}
            if not check_feasible(n, arcs, p):
                raise ArithmeticError("feasibility replay failed")
            return answer
    v = last
    for _ in range(n):
        check()
        v = arcs[pred[v]][0]
    root, backward = v, []
    while True:
        check()
        i = pred[v]
        backward.append(i)
        v = arcs[i][0]
        if v == root:
            break
        if len(backward) > n:
            raise ArithmeticError("invalid predecessor cycle")
    answer = {'status': 'INFEASIBLE', 'cycle': list(reversed(backward))}
    if not check_negative_cycle(n, arcs, answer):
        raise ArithmeticError("negative-cycle replay failed")
    return answer


def minimize_difference(n, edges, arcs, initial=None, check=noop):
    """Minimize sum w*abs(c+p[v]-p[u]) with integral, exact certificates.

    Number of augmentations is at most sum(w), not polylog(sum(w)). The
    geometric theorem uses the independently justified bound sum(w)<=12T.
    """
    if integer(n) < 1:
        raise ValueError("positive number of vertices required")
    edges, arcs = tuple(map(tuple, edges)), tuple(map(tuple, arcs))
    for u, v, c, w in edges:
        if not (0 <= integer(u) < n and 0 <= integer(v) < n):
            raise ValueError("objective endpoint outside model")
        integer(c)
        if integer(w) < 0:
            raise ValueError("objective weights must be nonnegative")
    if initial is None:
        feasible = feasibility(n, arcs, check)
        if feasible['status'] == 'INFEASIBLE':
            return {'certificate': feasible, 'stats': {'augmentations': 0}}
        initial = feasible['potential']
    if not check_feasible(n, arcs, initial):
        raise ValueError("invalid supplied feasible potential")
    source, sink = n, n+1
    graph = [[] for _ in range(n+2)]
    balance = [0]*n
    potential = list(initial)+[0, 0]
    W = sum(row[3] for row in edges)
    bound = W+1

    def add(u, v, cap, cost, flow=0):
        a, b = len(graph[u]), len(graph[v])
        graph[u].append([v, b+(u == v), cap-flow, cost])
        graph[v].append([u, a, flow, -cost])
        return (u, a)

    soft, hard = [], []
    for u, v, c, w in edges:
        check()
        x = c+initial[v]-initial[u]
        f = w if x > 0 else -w if x < 0 else 0
        soft.append(add(u, v, 2*w, -c, f+w))
        balance[u] -= f
        balance[v] += f
    for u, v, b in arcs:
        check()
        hard.append(add(u, v, bound, b))
    plus = [v for v in range(n) if balance[v] > 0]
    minus = [v for v in range(n) if balance[v] < 0]
    potential[source] = max((initial[v] for v in plus), default=0)
    potential[sink] = min((initial[v] for v in minus), default=0)
    required = sum(balance[v] for v in plus)
    if required > W:
        raise ArithmeticError("imbalance exceeds the weight sum")
    for v in plus:
        add(source, v, balance[v], 0)
    for v in minus:
        add(v, sink, -balance[v], 0)
    sent = rounds = scans = 0
    while sent < required:
        check()
        distance, previous = [None]*(n+2), [None]*(n+2)
        distance[source] = 0
        heap = [(0, source)]
        while heap:
            check()
            value, u = heappop(heap)
            if distance[u] != value:
                continue
            if u == sink:
                break
            for i, (v, rev, cap, cost) in enumerate(graph[u]):
                check()
                scans += 1
                if cap == 0:
                    continue
                reduced = cost+potential[u]-potential[v]
                if reduced < 0:
                    raise ArithmeticError("negative reduced residual cost")
                candidate = value+reduced
                if distance[v] is None or candidate < distance[v]:
                    distance[v], previous[v] = candidate, (u, i)
                    heappush(heap, (candidate, v))
        limit = distance[sink]
        if limit is None:
            raise ArithmeticError("zero signed flow guarantees a feasible repair")
        for v, d in enumerate(distance):
            potential[v] += limit if d is None else min(limit, d)
        amount, v = required-sent, sink
        while v != source:
            check()
            u, i = previous[v]
            amount = min(amount, graph[u][i][2])
            v = u
        v = sink
        while v != source:
            check()
            u, i = previous[v]
            arc = graph[u][i]
            arc[2] -= amount
            graph[v][arc[1]][2] += amount
            v = u
        sent, rounds = sent+amount, rounds+1

    def flow(ref):
        u, i = ref
        v, j, _, _ = graph[u][i]
        return graph[v][j][2]

    p = potential[:n]
    offset = min(p)
    p = [x-offset for x in p]
    proof = {'status': 'OPTIMAL', 'potential': p,
             'edge_flows': [flow(ref)-row[3] for ref, row in zip(soft, edges)],
             'constraint_flows': [flow(ref) for ref in hard],
             'objective': sum(w*abs(c+p[v]-p[u]) for u, v, c, w in edges)}
    if not check_optimum(n, edges, arcs, proof):
        raise ArithmeticError("independent primal-dual replay failed")
    return {'certificate': proof, 'stats': {'augmentations': rounds,
            'sent_units': sent, 'weight_sum': W, 'arc_scans': scans}}
