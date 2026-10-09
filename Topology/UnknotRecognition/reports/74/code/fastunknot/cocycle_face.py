"""Bounded extremal search in the face certified by a span matching.

This is candidate discovery, not a complete search for discs. Every emitted
potential has the same minimum span and reuses the existing independent
primal/dual certificate format. No flow solver is imported here.
"""
from heapq import heappop, heappush

from .cocycle_span_verify import verify_cocycle_span
from .integer_codec import encoded_integer
from .normal_cocycle import local_coordinates


def _distances(graph, root, check):
    distance, heap = {root: 0}, [(0, root)]
    while heap:
        check()
        value, u = heappop(heap)
        if distance[u] != value:
            continue
        for v, weight in graph[u]:
            check()
            candidate = value+weight
            if v not in distance or candidate < distance[v]:
                distance[v] = candidate
                heappush(heap, (candidate, v))
    return distance


def cocycle_face_candidates(vertices, heights, certificate, *, roots=8, check=lambda: None):
    """Yield distinct extrema using at most two shortest searches per root.

    Equivalent roots in a zero-weight strongly connected component are
    skipped. Each counted root supplies upper and lower relative-potential
    bounds on its incidence component. Other components keep their original
    potential. All emitted certificates pass the independent span checker.
    """
    if type(roots) is not int or roots < 0:
        raise ValueError('face roots must be a nonnegative integer')
    check()
    if not roots:
        return
    if not verify_cocycle_span(vertices, heights, certificate, check=check):
        raise ValueError('a valid span optimality certificate is required')
    labels = certificate['vertex_ids']
    potential = dict(zip(labels, map(encoded_integer, certificate['potential'])))
    h = [[encoded_integer(x) for x in row] for row in heights]
    low = {t: i for t, i, s, j in certificate['matching']}
    high = {s: j for t, i, s, j in certificate['matching']}
    forward, reverse = {v: [] for v in labels}, {v: [] for v in labels}
    for t, (vs, hs) in enumerate(zip(vertices, h)):
        check()
        l, u = low[t], high[t]
        for i in range(4):
            check()
            for a, b, cost in ((vs[i], vs[l], hs[i]-hs[l]),
                               (vs[u], vs[i], hs[u]-hs[i])):
                weight = cost+potential[a]-potential[b]
                if weight < 0:
                    raise ArithmeticError('matching corner is not extremal')
                forward[a].append((b, weight))
                reverse[b].append((a, weight))
    offset = min(potential.values())
    seen = {tuple(potential[v]-offset for v in labels)}
    covered, used = set(), 0
    for root in sorted(labels, key=lambda v: (-len(forward[v])-len(reverse[v]), v)):
        check()
        if root in covered:
            continue
        if used == roots:
            break
        used += 1
        upper = _distances(forward, root, check)
        lower = _distances(reverse, root, check)
        if upper.keys() != lower.keys():
            raise ArithmeticError('optimal face is unbounded within an incidence component')
        for v in upper:
            check()
            if upper[v] == lower[v] == 0:
                covered.add(v)
        for sign, distances in ((1, upper), (-1, lower)):
            check()
            values = []
            for v in labels:
                check()
                values.append(potential[v]+sign*distances.get(v, 0))
            offset = min(values)
            values = [x-offset for x in values]
            signature = tuple(values)
            if signature in seen:
                continue
            seen.add(signature)
            lookup = dict(zip(labels, values))
            coordinates = []
            for vs, hs in zip(vertices, h):
                check()
                coordinates.append(local_coordinates([x+lookup[v] for v, x in zip(vs, hs)]))
            result = dict(certificate, potential=values, coordinates=coordinates)
            if not verify_cocycle_span(vertices, h, result, check=check):
                raise ArithmeticError('optimal-face candidate failed span replay')
            yield dict(root=root, direction=sign, root_trial=used, certificate=result,
                       coordinates=coordinates)
