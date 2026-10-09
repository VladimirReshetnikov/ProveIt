"""Linear arithmetic replay of a cocycle-span primal/dual certificate.

The network solver is not imported. Normal coordinates are reconstructed
from six absolute edge differences, independently of the producer's gaps.
"""
from itertools import combinations

from .integer_codec import encoded_integer, certificate_equal


def verify_cocycle_span(vertices, heights, certificate, *, check=lambda: None):
    """Prove the stated span minimum over real and integral vertex potentials."""
    check()
    fields = {'schema', 'vertex_ids', 'potential', 'matching', 'coordinates', 'disc_count'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] != 'normal-cocycle-span-v1'
            or type(vertices) is not list or not vertices
            or type(heights) is not list or len(heights) != len(vertices)):
        return False
    h = []
    for vs, hs in zip(vertices, heights):
        check()
        if (type(vs) is not list or len(vs) != 4
                or any(type(v) is not int or v < 0 for v in vs)
                or type(hs) is not list or len(hs) != 4):
            return False
        try:
            h.append([encoded_integer(value) for value in hs])
        except ValueError:
            return False
    labels = sorted({v for row in vertices for v in row})
    if not certificate_equal(certificate['vertex_ids'], labels):
        return False
    supplied = certificate['potential']
    if type(supplied) is not list or len(supplied) != len(labels):
        return False
    try:
        potential = dict(zip(labels, map(encoded_integer, supplied)))
    except ValueError:
        return False
    coordinates, primal = [], 0
    for vs, hs in zip(vertices, h):
        check()
        adjusted = [height+potential[v] for v, height in zip(vs, hs)]
        edges = {(a, b): abs(adjusted[a]-adjusted[b]) for a, b in combinations(range(4), 2)}
        def weight(a, b):
            return edges[min(a, b), max(a, b)]
        triangles = []
        for v in range(4):
            slacks = [weight(v, a)+weight(v, b)-weight(a, b)
                      for a, b in combinations([i for i in range(4) if i != v], 2)]
            triangles.append(min(slacks)//2)
        a, b, c = [weight(0, v)-triangles[0]-triangles[v] for v in (1, 2, 3)]
        quads = [(b+c-a)//2, (a+c-b)//2, (a+b-c)//2]
        coordinates.append(triangles+quads)
        primal += max(adjusted)-min(adjusted)
    if (not certificate_equal(certificate['coordinates'], coordinates)
            or not certificate_equal(certificate['disc_count'], primal)):
        return False
    matching = certificate['matching']
    n = len(vertices)
    if type(matching) is not list or len(matching) != n:
        return False
    sources, targets, dual = set(), set(), 0
    for row in matching:
        check()
        if type(row) is not list or len(row) != 4 or any(type(v) is not int for v in row):
            return False
        t, i, s, j = row
        if (not 0 <= t < n or not 0 <= s < n or not 0 <= i < 4 or not 0 <= j < 4
                or t in sources or s in targets or vertices[t][i] != vertices[s][j]):
            return False
        sources.add(t)
        targets.add(s)
        dual += h[s][j]-h[t][i]
    check()
    return primal == dual
