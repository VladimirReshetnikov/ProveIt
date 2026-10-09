"""Independent finite expansion oracle; deliberately not a compressed algorithm."""
from collections import Counter


def expanded(model, defects=()):
    """Input is the normalized dataclass, but no producer algorithm is reused."""
    n, W, D = model.vertices, model.sheets, model.dimension
    graph = [set() for _ in range(n * W)]
    for e in model.edges:
        for x in range(W):
            u = e.u * W + x
            v = e.v * W + (e.sign * x + e.shift) % W
            graph[u].add(v)
            graph[v].add(u)
    for e in defects:
        u, v = e.u * W + e.x, e.v * W + e.y
        graph[u].add(v)
        graph[v].add(u)
    local = [[0] * D for _ in graph]
    for w in model.weights:
        for x in range(w.start, w.stop):
            for j, z in enumerate(w.value):
                local[w.v * W + x][j] += z
    label = [-1] * len(graph)
    weights = []
    for u in range(len(graph)):
        if label[u] >= 0:
            continue
        label[u] = len(weights)
        total = [0] * D
        stack = [u]
        while stack:
            x = stack.pop()
            total = [a + b for a, b in zip(total, local[x])]
            for y in graph[x]:
                if label[y] < 0:
                    label[y] = label[u]
                    stack.append(y)
        weights.append(total)
    for e in defects:
        out = weights[label[e.u * W + e.x]]
        for j, z in enumerate(e.payload):
            out[j] += z
    weights = [tuple(x) for x in weights]
    return Counter(weights), label, weights
