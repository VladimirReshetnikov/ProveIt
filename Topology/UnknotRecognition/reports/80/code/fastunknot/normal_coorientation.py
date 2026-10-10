"""Finite sufficient coorientation constraints for a normal interval system.

One bit is assigned to each nonempty global-edge block. A reversed pairing
toggles the sheet of the doubled system; a preserving pairing does not.
Exactness of these finite constraints trivializes that double cover. Failure
does not imply nonorientability: a coorientation may vary inside a block.
"""
from bisect import bisect_right


def _coorientation_graph(analysed, pairings, check):
    starts, total = [], 0
    for edge, weight in sorted(analysed['weights'].items()):
        check()
        if weight:
            starts.append(total)
        total += weight
    graph = []
    for pair in pairings:
        check()
        a, b, c, d = (bisect_right(starts,x)-1 for x in (pair.a,pair.b,pair.c,pair.d))
        if a < 0 or c < 0 or a != b or c != d or pair.d >= total or pair.b >= total:
            raise ArithmeticError('normal arc crosses an ambient-edge block')
        graph.append((a,c,int(pair.reverse)))
    return graph
