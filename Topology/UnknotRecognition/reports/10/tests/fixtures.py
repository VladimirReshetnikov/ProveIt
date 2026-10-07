"""Explicit planar matching fixtures; no knot recognizer is required.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations


def zipper_triple(discs: int, blocks: int = 1):
    """Return A,B,C with r=s=blocks*discs, t=k=blocks.

    Each block has 2*discs-1 adjacent arcs in B. A joins consecutive odd/even
    arc pairs; C joins the offset pairs. The bipartite gluing graph is a path.
    All matchings are noncrossing in the common boundary order.
    """
    if type(discs) is not int or type(blocks) is not int or discs < 1 or blocks < 1:
        raise ValueError('discs and blocks must be positive integers')
    m = 2 * discs - 1
    b = tuple((2 * j, 2 * j + 1) for j in range(m * blocks))
    a, c = list(b), list(b)
    for block in range(blocks):
        offset = block * m
        for target, start in ((a, offset), (c, offset + 1)):
            for j in range(start, offset + m - 1, 2):
                target.remove((2*j, 2*j+1))
                target.remove((2*j+2, 2*j+3))
                target.extend(((2*j, 2*j+3), (2*j+1, 2*j+2)))
    return tuple(sorted(a)), b, tuple(sorted(c))
