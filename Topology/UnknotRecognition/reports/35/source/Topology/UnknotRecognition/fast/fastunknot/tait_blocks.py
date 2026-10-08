"""Exact signed spanning-tree products over articulation blocks.

Parallel weights are summed before decomposition. This may disconnect the
weighted graph even when the projection is connected, in which case its
spanning-tree sum is zero. Loops do not contribute to this sum; the caller
must retain their separate Jones phase.
"""


def edge_blocks(n, edges, tick):
    """Return weighted edge blocks, or None if the nonzero graph disconnects.

    Iterative low-link DFS avoids a recursion-depth limit on long block chains.
    The input has unique unordered nonloop edges with nonzero integer weights.
    """
    tick(n + 2 * len(edges))
    adjacent = [[] for _ in range(n)]
    for index, (u, v, _) in enumerate(edges):
        tick()
        adjacent[u].append((v, index))
        adjacent[v].append((u, index))
    discovery, low, parent = [-1] * n, [0] * n, [-1] * n
    discovery[0] = 0
    clock = 1
    frames = [(0, iter(adjacent[0]))]
    stack, blocks = [], []
    while frames:
        tick()
        u, neighbors = frames[-1]
        item = next(neighbors, None)
        if item is not None:
            v, edge = item
            if v == parent[u]:
                continue
            if discovery[v] < 0:
                parent[v] = u
                discovery[v] = low[v] = clock
                clock += 1
                stack.append(edge)
                frames.append((v, iter(adjacent[v])))
            elif discovery[v] < discovery[u]:
                low[u] = min(low[u], discovery[v])
                stack.append(edge)
            continue
        frames.pop()
        p = parent[u]
        if p < 0:
            continue
        low[p] = min(low[p], low[u])
        if low[u] >= discovery[p]:
            block = []
            while stack:
                tick()
                edge = edges[stack.pop()]
                block.append(edge)
                if {edge[0], edge[1]} == {p, u}:
                    break
            blocks.append(block)
    return blocks if clock == n else None


def spanning_tree_product(n, edges, tick, determinant, stats):
    """Evaluate a signed tree sum without allocating the full cofactor.

    The caller selects this path for larger graphs. A one-edge block is its
    weight; other blocks use the supplied interruptible exact determinant.
    All state is local, so interruption cannot publish a partial product.
    """
    weights = {}
    for u, v, weight in edges:
        tick()
        if u != v:
            key = (u, v) if u < v else (v, u)
            weights[key] = weights.get(key, 0) + weight
    combined = []
    for (u, v), weight in weights.items():
        tick()
        if weight:
            combined.append((u, v, weight))
    blocks = edge_blocks(n, combined, tick)
    if blocks is None:
        stats['tait_disconnected'] += 1
        return 0
    stats['tait_blocks'] += len(blocks)
    value = 1
    for block in blocks:
        tick()
        if len(block) == 1:
            factor = block[0][2]
            stats['tait_bridge_factors'] += 1
        else:
            vertices = set()
            for u, v, _ in block:
                tick()
                vertices.update((u, v))
            ids = {vertex: i for i, vertex in enumerate(sorted(vertices))}
            size = len(ids) - 1
            tick(size * size)
            matrix = [[0] * size for _ in range(size)]
            for u, v, weight in block:
                tick()
                a, b = ids[u] - 1, ids[v] - 1
                if a >= 0:
                    matrix[a][a] += weight
                if b >= 0:
                    matrix[b][b] += weight
                if a >= 0 and b >= 0:
                    matrix[a][b] -= weight
                    matrix[b][a] -= weight
            stats['max_cofactor_size'] = max(stats['max_cofactor_size'], size)
            stats['tait_block_determinants'] += 1
            factor = determinant(matrix, tick)
        value *= factor
        if not value:
            stats['tait_zero_factors'] += 1
            return 0
    return value
