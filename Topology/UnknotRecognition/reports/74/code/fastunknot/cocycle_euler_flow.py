"""Exact bounded-flow dual for a weighted absolute-difference objective.

The private solver takes an already validated feasible integral potential.
Its augmentation bound is sum of objective weights, not their bit length;
for the cocycle Euler model that sum is O(tetrahedra).
"""
from heapq import heappop, heappush
from .cocycle_euler_verify import verify_difference_optimum


def _minimize_difference_full(n, edges, constraints, initial, check):
    source, sink = n, n+1
    graph = [[] for _ in range(n+2)]
    balance = [0]*n
    potential = list(initial)+[0, 0]
    total_weight = sum(row[3] for row in edges)
    bound = total_weight+1

    def add(a, b, capacity, cost, flow=0):
        i, j = len(graph[a]), len(graph[b])
        graph[a].append([b, j+int(a == b), capacity-flow, cost])
        graph[b].append([a, i, flow, -cost])
        return a, i

    soft, hard = [], []
    for a, b, c, w in edges:
        check()
        adjusted = c+initial[b]-initial[a]
        f = w if adjusted > 0 else -w if adjusted < 0 else 0
        soft.append(add(a, b, 2*w, -c, f+w))
        balance[a] -= f
        balance[b] += f
    for a, b, d in constraints:
        check()
        if d+initial[a]-initial[b] < 0:
            raise ValueError('initial potential violates a difference constraint')
        hard.append(add(a, b, bound, d))
    positive = [v for v in range(n) if balance[v] > 0]
    negative = [v for v in range(n) if balance[v] < 0]
    potential[source] = max((initial[v] for v in positive), default=0)
    potential[sink] = min((initial[v] for v in negative), default=0)
    required = sum(balance[v] for v in positive)
    if required > total_weight:
        raise ArithmeticError('initial flow imbalance exceeds objective weights')
    for v in positive:
        check()
        add(source, v, balance[v], 0)
    for v in negative:
        check()
        add(v, sink, -balance[v], 0)
    sent = augmentations = scans = pops = 0
    while sent < required:
        check()
        distance, previous = [None]*(n+2), [None]*(n+2)
        distance[source] = 0
        heap = [(0, source, source)]
        while heap:
            check()
            value, priority, u = heappop(heap)
            pops += 1
            if distance[u] != value:
                continue
            if u == sink:
                break
            for i, (v, reverse, capacity, cost) in enumerate(graph[u]):
                check()
                scans += 1
                if not capacity:
                    continue
                reduced = cost+potential[u]-potential[v]
                if reduced < 0:
                    raise ArithmeticError('negative reduced cost in Euler flow')
                candidate = value+reduced
                if distance[v] is None or candidate < distance[v]:
                    distance[v] = candidate
                    previous[v] = u, i
                    heappush(heap, (candidate, -1 if v == sink else v, v))
        if distance[sink] is None:
            raise ArithmeticError('Euler flow balance unexpectedly infeasible')
        limit = distance[sink]
        for v, value in enumerate(distance):
            check()
            potential[v] += limit if value is None else min(value, limit)
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
        sent += amount
        augmentations += 1
    values = potential[:n]
    offset = min(values)
    values = [x-offset for x in values]
    def flow(reference):
        a, i = reference
        v, j, capacity, cost = graph[a][i]
        return graph[v][j][2]
    edge_flows, constraint_flows = [], []
    for ref, row in zip(soft, edges):
        check()
        edge_flows.append(flow(ref)-row[3])
    for ref in hard:
        check()
        constraint_flows.append(flow(ref))
    objective = 0
    for a, b, c, w in edges:
        check()
        objective += w*abs(c+values[b]-values[a])
    certificate = dict(schema='weighted-difference-optimum-v1', potential=values,
        edge_flows=edge_flows, constraint_flows=constraint_flows, objective=objective)
    if not verify_difference_optimum(n, edges, constraints, certificate, check=check):
        raise ArithmeticError('Euler flow failed independent primal/dual replay')
    return dict(certificate=certificate, stats=dict(augmentations=augmentations,
        sent_units=sent, weight_sum=total_weight, arc_scans=scans, heap_pops=pops,
        network_nodes=n+2, network_arcs=sum(map(len, graph))//2))


def _minimize_difference(n, edges, constraints, initial, check):
    """Use forced equalities when present, otherwise retain the full solver."""
    from .cocycle_euler_quotient import _contracted_difference
    return _contracted_difference(n, edges, constraints, initial, check, _minimize_difference_full)
