"""Small independent graph-edge dynamic program for complete cut signatures.

Unlike production routing, this consumes the assembled graph's edge list and
does not inspect component cycles.  The exponential frontier cap is deliberate.
"""
from itertools import product


def graph_table(tile, threshold=3, frontier_cap=16):
    width = tile.width
    d = 1 << width
    infinity = threshold + 1
    table = [[[infinity]*4 for _ in range(d)] for _ in range(d)]
    last = {}
    for ei, edge in enumerate(tile.edges):
        for v in edge:
            last[v] = ei
    for left in range(d):
        for right in range(d):
            fixed = {v: (left >> i) & 1 for i, v in enumerate(tile.left)}
            fixed.update({v: (right >> i) & 1 for i, v in enumerate(tile.right)})
            active = []
            states = {((), 0): 0}
            for ei, (a, b) in enumerate(tile.edges):
                introduced = [v for v in dict.fromkeys((a, b)) if v not in active]
                enlarged = active + introduced
                if len(enlarged) > frontier_cap:
                    raise ValueError('oracle frontier cap exceeded')
                keep = [v for v in enlarged if last[v] > ei]
                index = {v: i for i, v in enumerate(enlarged)}
                options = [[fixed[v]] if v in fixed else [0, 1] for v in introduced]
                updated = {}
                for (colors, flags), value in states.items():
                    for choice in product(*options):
                        all_colors = colors + choice
                        ca, cb = all_colors[index[a]], all_colors[index[b]]
                        cost = value + int(ca != cb)
                        if cost > threshold:
                            continue
                        marks = flags | (0 if ca != cb else 1 << ca)
                        key = (tuple(all_colors[index[v]] for v in keep), marks)
                        updated[key] = min(updated.get(key, infinity), cost)
                states = updated
                active = keep
            for (colors, flags), cost in states.items():
                assert not colors
                table[left][right][flags] = cost
    return table
