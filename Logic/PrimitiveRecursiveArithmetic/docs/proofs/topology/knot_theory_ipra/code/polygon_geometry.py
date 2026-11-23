"""Exact regular projections and four-dimensional cone certificates for cyclic polygons.

Regular projection assumes an embedded 3D polygon with distinct rational
vertices, as in the projection theorem. Cone certificates assume the same
conditions in dimension four. The finite upper bounds are proved in the report.
"""
from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement


def subtract(a, b):
    return tuple(x-y for x, y in zip(a, b))


def det(a, b):
    return a[0]*b[1] - a[1]*b[0]


def edges(p):
    return list(zip(p, p[1:] + p[:1]))


def between(x, a, b):
    return all(min(lo, hi) <= v <= max(lo, hi) for v, lo, hi in zip(x, a, b))


def crossings_for(vertices, u, v):
    """None indicates a non-regular chart. Otherwise return exact crossing rows."""
    flat = [(x-u*z, y-v*z) for x, y, z in vertices]
    if len(set(flat)) != len(flat):
        return None
    segments = edges(flat)
    seen = set()
    answer = []
    for (i, (a, b)), (j, (c, d)) in combinations(enumerate(segments), 2):
        adjacent = j == i+1 or (i == 0 and j+1 == len(segments))
        r, s, gap = subtract(b, a), subtract(d, c), subtract(c, a)
        divisor = det(r, s)
        if divisor == 0:
            if det(r, gap) != 0:
                continue
            contacts = {point for point in (a,b,c,d)
                        if between(point, a,b) and between(point, c,d)}
            if len(contacts) > int(adjacent):
                return None
            continue
        t, w = Q(det(gap,s), divisor), Q(det(gap,r), divisor)
        if not (0 <= t <= 1 and 0 <= w <= 1) or adjacent:
            continue
        point = (a[0]+t*r[0], a[1]+t*r[1])
        if t in (0,1) or w in (0,1) or point in seen:
            return None
        z1 = (1-t)*vertices[i][2] + t*vertices[(i+1) % len(vertices)][2]
        z2 = (1-w)*vertices[j][2] + w*vertices[(j+1) % len(vertices)][2]
        if z1 == z2:
            raise ValueError("Space edges intersect")
        seen.add(point)
        answer.append((i,j,point,t,w,i if z1 > z2 else j))
    return answer


def projection(vertices):
    n = len(vertices)
    bound = 10*(n+1)**3
    # Square shells make small slopes quick to find.
    for k in range(bound+1):
        for u,v in [(k,j) for j in range(k+1)] + [(j,k) for j in range(k)]:
            result = crossings_for(vertices,u,v)
            if result is not None:
                return u,v,result
    raise ValueError("No regular chart for this input")


def rank(rows):
    basis = []
    for row in rows:
        w = list(map(Q,row))
        for pivot,vector in basis:
            w = [x-w[pivot]*y for x,y in zip(w,vector)]
        pivot = next((i for i,x in enumerate(w) if x), None)
        if pivot is not None:
            w = [x/w[pivot] for x in w]
            basis.append((pivot,w))
    return len(basis)


def affine_rank(points):
    origin, *rest = points
    return rank(subtract(point,origin) for point in rest)


def cone_certificate(vertices):
    n = len(vertices)
    spans = [list(first+second) for first,second in
             combinations_with_replacement(edges(vertices), 2)]
    ranks = [affine_rank(span) for span in spans]
    for t in range(4*n*n+1):
        apex = tuple(t**j for j in range(1,5))
        if all(affine_rank(span+[apex]) > base for span,base in zip(spans,ranks)):
            # First insert apex between v0 and v1, then remove v1,...,v(n-2).
            insert = (vertices[0],apex,vertices[1])
            removals = [(apex,vertices[i],vertices[i+1]) for i in range(1,n-1)]
            return t,apex,insert,removals
    raise ValueError("No admissible apex for this input")


if __name__ == "__main__":
    bow = [(-2,-2,0),(2,2,1),(-2,2,4),(2,-2,4)]
    u,v,rows = projection(bow)
    assert (u,v) == (0,0) and len(rows) == 1 and rows[0][-1] == 2
    vertical = [(0,0,0),(0,0,3),(1,0,4),(1,2,2),(-1,1,1)]
    u,v,rows = projection(vertical)
    assert (u,v) != (0,0) and len(rows) <= 5
    for n in range(3,11):
        # Vertices on the moment curve give pairwise disjoint nonadjacent edges.
        p = [tuple(j**k for k in range(1,5)) for j in range(n)]
        t,apex,insert,delete = cone_certificate(p)
        assert t == n and len(delete)+1 == n-1
        boundary = [p[0],apex,*p[1:]]
        for left,middle,right in delete:
            assert tuple(boundary[1:4]) == (left,middle,right)
            boundary.pop(2)
        assert boundary == [p[0],apex,p[-1]]
    print("Passed rational regular-projection examples and eight 4D cone-fan certificates.")
