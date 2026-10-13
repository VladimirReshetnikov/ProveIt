"""Deterministic plane-tree medial diagrams for separator/order stress tests."""
from fastunknot import Diagram


def tree_medial(height):
    if type(height) is not int or not 1 <= height <= 16:
        raise ValueError('height must be from 1 through 16')
    vertices = 2**(height+1)-1
    edges = vertices-1
    corners = [[] for _ in range(vertices)]
    for v in range(1, vertices):
        edge = v-1
        corners[(v-1)//2].append((4*edge, 4*edge+1))
        corners[v].append((4*edge+2, 4*edge+3))
    alpha = [-1]*(4*edges)
    for around in corners:
        for i, (_, end) in enumerate(around):
            start = around[(i+1) % len(around)][0]
            alpha[start], alpha[end] = end, start
    labels, counter = [-1]*len(alpha), 0
    for d, e in enumerate(alpha):
        if labels[d] < 0:
            labels[d] = labels[e] = counter
            counter += 1
    pd = [tuple(labels[4*v:4*v+4]) for v in range(edges)]
    return Diagram.from_pd(pd)
