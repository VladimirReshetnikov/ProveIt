"""Independent exponential oracle for the marked-cut semiring.

Only for small explicit tiles and exhaustive research audits. The production
four-copy kernel does not construct any 2^width table.
"""
from .core import Tile


def tile_table(tile: Tile, k: int = 3):
    if tile.n > 18:
        raise ValueError('exhaustive oracle capped at eighteen vertices')
    d = 1 << tile.width; infinity = k + 1
    table = [[[infinity] * 4 for _ in range(d)] for _ in range(d)]
    for coloring in range(1 << tile.n):
        left = sum(((coloring >> v) & 1) << i for i, v in enumerate(tile.left))
        right = sum(((coloring >> v) & 1) << i for i, v in enumerate(tile.right))
        cost = 0; flags = 0
        for a, b in tile.edges:
            ca, cb = (coloring >> a) & 1, (coloring >> b) & 1
            if ca != cb:
                cost += 1
            else:
                flags |= 1 << ca
        table[left][right][flags] = min(table[left][right][flags], cost)
    return table


def multiply(a, b, k: int = 3):
    d = len(a); infinity = k + 1
    out = [[[infinity] * 4 for _ in range(d)] for _ in range(d)]
    for i in range(d):
        for j in range(d):
            target = out[i][j]
            for h in range(d):
                x, y = a[i][h], b[h][j]
                for u in range(4):
                    if x[u] <= k:
                        for v in range(4):
                            cost = x[u] + y[v]
                            if cost < target[u | v]:
                                target[u | v] = cost
    return out


def power(table, exponent: int, k: int = 3):
    if exponent < 1:
        raise ValueError('positive exponent required')
    out = None
    while exponent:
        if exponent & 1:
            out = table if out is None else multiply(out, table, k)
        exponent >>= 1
        if exponent:
            table = multiply(table, table, k)
    return out


def closure_cost(table) -> int:
    return min(table[i][i][3] for i in range(len(table)))
