"""Polynomial integral span minimization with reduced-cost shortest paths.

The network and matching dual follow report 31 (MIT-0). A DAG initialization
and adaptive zero-cost blocking flows replace its repeated Bellman--Ford
passes. Dijkstra updates preserve feasible potentials. No loop or capacity
expands a height. The separate checker uses only weak duality.
"""
from heapq import heappop, heappush

from .integer_codec import encoded_integer
from .normal_cocycle import _Budget, local_coordinates


def _zero_block(graph, potential, source, sink, remaining, budget, stats):
    """Send a blocking flow through zero-reduced-cost residual arcs.

    Breadth-first levels exclude cycles. Iterative current-arc traversal
    avoids recursion limits, and every path has unit bottleneck at source.
    Newly opened reverse arcs point to lower levels, so pointers never need
    to revisit a discarded arc during this block.
    """
    stats['zero_searches'] += 1
    levels = [-1]*len(graph)
    levels[source] = 0
    queue = [source]
    for u in queue:
        budget.tick()
        if levels[sink] >= 0 and levels[u] >= levels[sink]:
            break
        for v, reverse, capacity, cost in graph[u]:
            budget.tick()
            stats['blocking_scans'] += 1
            if capacity and levels[v] < 0 and cost+potential[u]-potential[v] == 0:
                levels[v] = levels[u]+1
                queue.append(v)
    if levels[sink] < 0:
        return 0
    stats['blocking_phases'] += 1
    current = [0]*len(graph)
    sent = 0
    while sent < remaining:
        budget.tick()
        nodes, path = [source], []
        while nodes and nodes[-1] != sink:
            budget.tick()
            u = nodes[-1]
            while current[u] < len(graph[u]):
                budget.tick()
                stats['blocking_scans'] += 1
                i = current[u]
                v, reverse, capacity, cost = graph[u][i]
                if capacity and levels[v] == levels[u]+1 and cost+potential[u]-potential[v] == 0:
                    nodes.append(v)
                    path.append((u, i))
                    break
                current[u] += 1
            else:
                nodes.pop()
                if path:
                    parent, position = path.pop()
                    current[parent] = position+1
        if not nodes:
            break
        for u, i in path:
            budget.tick()
            stats['blocking_path_steps'] += 1
            arc = graph[u][i]
            arc[2] -= 1
            graph[arc[0]][arc[1]][2] += 1
        sent += 1
    stats['blocking_units'] += sent
    return sent


def minimize_cocycle_span(vertices, heights, *, max_work=None, check=lambda: None):
    """Minimize sum of tetrahedral height spans over global vertex potentials.

    This arithmetic API does not establish cocycle compatibility, manifold
    validity, primitivity, minimal genus, or an unknot verdict.
    """
    budget = _Budget(check, max_work)
    budget.tick()
    if (type(vertices) is not list or not vertices or type(heights) is not list
            or len(vertices) != len(heights)):
        raise ValueError('expected equally many nonempty vertex and height rows')
    h = []
    for vs, hs in zip(vertices, heights):
        budget.tick()
        if (type(vs) is not list or len(vs) != 4
                or any(type(v) is not int or v < 0 for v in vs)
                or type(hs) is not list or len(hs) != 4):
            raise ValueError('each row requires four vertices and four integer heights')
        h.append([encoded_integer(value) for value in hs])
    labels = sorted({v for row in vertices for v in row})
    index = {v: i for i, v in enumerate(labels)}
    n, k = len(h), len(labels)
    source, sink = 2*n+k, 2*n+k+1
    graph = [[] for _ in range(sink+1)]
    references = []

    def add(a, b, capacity, cost):
        pos = len(graph[a])
        graph[a].append([b, len(graph[b]), capacity, cost])
        graph[b].append([a, pos, 0, -cost])
        return a, pos

    for t, (vs, hs) in enumerate(zip(vertices, h)):
        budget.tick()
        add(source, t, 1, 0)
        add(n+t, sink, 1, 0)
        for i, (v, height) in enumerate(zip(vs, hs)):
            node = 2*n+index[v]
            references.append((0, t, i, add(t, node, n+1, height)))
            references.append((1, t, i, add(node, n+t, n+1, -height)))
    # All initially usable arcs follow this explicit acyclic ordering.
    distance = [None] * len(graph)
    distance[source] = 0
    order = [source] + list(range(n)) + list(range(2*n, 2*n+k)) + list(range(n, 2*n)) + [sink]
    for u in order:
        budget.tick()
        for v, reverse, capacity, cost in graph[u]:
            if capacity:
                candidate = distance[u]+cost
                if distance[v] is None or candidate < distance[v]:
                    distance[v] = candidate
    potential = distance
    relaxations, pops, flow = 0, 0, 0
    blocking = dict(zero_searches=0, blocking_phases=0, blocking_scans=0,
                    blocking_path_steps=0, blocking_units=0, dijkstra_searches=0,
                    blocking_fallbacks=0, blocking_restarts=0)
    active, poor = True, 0
    while flow < n:
        budget.tick()
        sent = 0
        if active:
            sent = _zero_block(graph, potential, source, sink, n-flow, budget, blocking)
            poor = 0 if sent >= 2 else poor+1
            if poor >= 2:
                active = False
                blocking['blocking_fallbacks'] += 1
        if sent:
            flow += sent
            continue
        blocking['dijkstra_searches'] += 1
        distance, previous = [None]*len(graph), [None]*len(graph)
        distance[source] = 0
        heap = [(0, source, source)]
        while heap:
            budget.tick()
            value, priority, u = heappop(heap)
            pops += 1
            if distance[u] != value:
                continue
            if u == sink:
                break
            for i, (v, reverse, capacity, cost) in enumerate(graph[u]):
                budget.tick()
                if not capacity:
                    continue
                reduced = cost+potential[u]-potential[v]
                if reduced < 0:
                    raise ArithmeticError('negative reduced cost in cocycle flow')
                candidate = value+reduced
                relaxations += 1
                if distance[v] is None or candidate < distance[v]:
                    distance[v] = candidate
                    previous[v] = u, i
                    # The capped update needs no distances beyond the sink.
                    # Settle it first among ties, including zero-cost regions.
                    heappush(heap, (candidate, -1 if v == sink else v, v))
        if distance[sink] is None:
            raise ArithmeticError('unit transshipment unexpectedly infeasible')
        limit = distance[sink]
        # Two poor blocks hand off to ordinary shortest paths. A later
        # zero-distance augmentation is fresh evidence of another level
        # where batching may help; allow a bounded attempt there again.
        if not active and limit == 0:
            active, poor = True, 0
            blocking['blocking_restarts'] += 1
        # Capping all increments at the sink distance also preserves reduced
        # costs on arcs from unreachable nodes into the reachable subgraph.
        for v, value in enumerate(distance):
            budget.tick()
            potential[v] += limit if value is None else min(value, limit)
        v = sink
        while v != source:
            budget.tick()
            u, i = previous[v]
            arc = graph[u][i]
            arc[2] -= 1
            graph[v][arc[1]][2] += 1
            v = u
        flow += 1
    values = [-potential[2*n+i] for i in range(k)]
    offset = min(values)
    values = [v-offset for v in values]
    lookup = dict(zip(labels, values))
    incoming, outgoing = {v: [] for v in labels}, {v: [] for v in labels}
    for kind, t, i, (u, pos) in references:
        budget.tick()
        arc = graph[u][pos]
        flow = graph[arc[0]][arc[1]][2]
        if flow not in (0, 1):
            raise ArithmeticError('nonbinary unit-transshipment arc')
        if flow:
            (incoming if kind == 0 else outgoing)[vertices[t][i]].append((t, i))
    matching = []
    for v in labels:
        budget.tick()
        left, right = sorted(incoming[v]), sorted(outgoing[v])
        if len(left) != len(right):
            raise ArithmeticError('vertex flow does not balance')
        matching.extend([t, i, s, j] for (t, i), (s, j) in zip(left, right))
    coordinates = []
    for vs, hs in zip(vertices, h):
        budget.tick()
        coordinates.append(local_coordinates([height+lookup[v] for v, height in zip(vs, hs)]))
    count = sum(sum(row) for row in coordinates)
    certificate = dict(schema='normal-cocycle-span-v1', vertex_ids=labels, potential=values,
                       matching=sorted(matching), coordinates=coordinates, disc_count=count)
    from .cocycle_span_verify import verify_cocycle_span
    if not verify_cocycle_span(vertices, h, certificate, check=budget.tick):
        raise ArithmeticError('cocycle-span primal/dual replay failed')
    return dict(coordinates=coordinates, certificate=certificate,
                stats=dict(work=budget.work, augmentations=n, relaxations=relaxations,
                           heap_pops=pops, network_nodes=len(graph), network_arcs=10*n,
                           initial_disc_count=sum(max(row)-min(row) for row in h), disc_count=count,
                           **blocking))
