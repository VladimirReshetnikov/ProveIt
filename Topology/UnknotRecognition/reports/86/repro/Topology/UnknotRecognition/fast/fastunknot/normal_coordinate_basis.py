"""Injective component coordinates on the support of a supplied normal surface.

All quadrilaterals and one triangle per quotient vertex determine a matching
vector. Source-zero entries vanish in every component. Anchor each vertex at
its smallest source triangle, so peeled vertex links require no anchor weight.
This module is producer-only; the checker solves matching rows separately.
"""

from collections import deque

from .normal_surface_geometry import _quad


def coordinate_basis(prepared, analysed, check=lambda: None):
    source = [value for row in analysed['rows'] for value in row]
    anchors = {}
    for corner, root in enumerate(prepared['vertex_roots']):
        check()
        index = 7*(corner//4)+corner % 4
        if root not in anchors or (source[index], index) < (source[anchors[root]], anchors[root]):
            anchors[root] = index
    anchors = sorted(anchors.values())
    selected = sorted([i for i, value in enumerate(source) if i % 7 >= 4 and value]
                      + [i for i in anchors if source[i]])
    return selected, anchors


def coordinate_decoder(prepared, analysed, selected, anchors, check=lambda: None):
    """Precompute a corner spanning forest; each edge adds two quad entries."""
    adjacency = {}
    for t, f, u, g, permutation in prepared['pairs']:
        check()
        for v in range(4):
            if v == f:
                continue
            a, b = 7*t+v, 7*u+permutation[v]
            p, q = 7*t+4+_quad(f, v), 7*u+4+_quad(g, permutation[v])
            adjacency.setdefault(a, []).append((b, p, q))
            adjacency.setdefault(b, []).append((a, q, p))
    seen, queue, steps = set(anchors), deque(anchors), []
    while queue:
        check()
        a = queue.popleft()
        for b, p, q in adjacency.get(a, ()):
            if b not in seen:
                seen.add(b)
                queue.append(b)
                steps.append((a, b, p, q))
    if len(seen) != 4*len(analysed['rows']):
        raise ArithmeticError('triangle anchors do not span all corners')
    source = [value for row in analysed['rows'] for value in row]

    def decode(weight):
        if len(weight) != max(1, len(selected)):
            raise ValueError('compact coordinate dimension differs')
        vector = [0]*len(source)
        for index, value in zip(selected, weight):
            check()
            vector[index] = value
        for a, b, p, q in steps:
            check()
            vector[b] = vector[a]+vector[p]-vector[q]
        for value, bound in zip(vector, source):
            check()
            if not 0 <= value <= bound:
                raise ValueError('decoded component exceeds source support')
        return vector

    return decode
