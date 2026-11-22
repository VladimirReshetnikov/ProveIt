"""Exact certificates for the icosahedron section. Run with Python 3."""
from fractions import Fraction
from itertools import combinations

def minus(a, b):
    return (a[0] - b[0], a[1] - b[1])

def norm2(a):
    u, v = a
    return u*u + u*v + v*v

def ring(i):
    return i % 5

def face(name):
    kind, i = name[0], int(name[1])
    a = lambda j: 1 + ring(j)
    b = lambda j: 6 + ring(j)
    return {
        'T': (0, a(i), a(i + 1)),
        'U': (a(i), a(i + 1), b(i)),
        'V': (a(i), b(i - 1), b(i)),
        'W': (11, b(i), b(i + 1)),
    }[kind]

def average(*points):
    return tuple(Fraction(sum(coords), len(points)) for coords in zip(*points))

def chamber(triangle, vertex, neighbor):
    return [triangle[vertex], average(triangle[vertex], triangle[neighbor]),
            average(*triangle.values())]

def unfold(word, inside):
    start = dict(zip(face(word[0]), [(0, 0), (1, 0), (0, 1)]))
    triangle = start
    cells = [triangle]
    for name in word[1:]:
        vertices = set(face(name))
        shared = vertices & triangle.keys()
        a, b = [triangle[v] for v in shared]
        c, = [p for v, p in triangle.items() if v not in shared]
        point = (a[0] + b[0] - c[0], a[1] + b[1] - c[1])
        new, = vertices - shared
        triangle = {v: triangle[v] for v in shared}
        triangle[new] = point
        cells.append(triangle)
    # Six distinct elementary lattice triangles have total coordinate area
    # three. Containment in the indicated parallelogram of area three proves
    # coverage, since the elementary triangles have disjoint interiors.
    shapes = [frozenset(t.values()) for t in cells]
    assert len(set(shapes)) == 6
    for t in shapes:
        assert all(inside(u, v) for u, v in t)
        assert all(norm2(minus(a, b)) == 1 for a, b in combinations(t, 2))
    return chamber(start, 0, 1), chamber(triangle, 11, 8)

def upper():
    words = ['T0 T4 T3 U3 V3 W2', 'T0 U0 V1 W0 W1 W2']
    regions = [lambda u,v: 0 <= u <= 1 and -2 <= u+v <= 1,
               lambda u,v: 0 <= u <= 1 and 0 <= v <= 3]
    paths = [unfold(w.split(), region) for w, region in zip(words, regions)]
    matrix = [[sum((norm2(minus(src[i], dst[j])) for src,dst in paths),
                   Fraction(0)) / 2 for j in range(3)] for i in range(3)]
    expected = [[7, Fraction(13,2), Fraction(41,6)],
                [Fraction(13,2), Fraction(25,4), Fraction(19,3)],
                [Fraction(41,6), Fraction(19,3), Fraction(19,3)]]
    assert matrix == expected
    assert all(6*(7 - matrix[i][j]) >= 1
               for i in range(3) for j in range(3) if (i,j) != (0,0))

def lower():
    N, A, A1, B, S = (0,0), (1,0), (0,1), (1,1), (2,1)
    M = (Fraction(3,2), Fraction(1,2))
    assert [norm2(x) for x in [N,A,B,S]] == [0,1,3,7]
    assert [4*norm2(x) for x in [average(N,A), average(A,A1), average(A,B),
                                   M, average(B,S)]] == [1,3,7,13,19]
    for triangle in [(N,A,A1), (A,A1,B)]:
        assert all(norm2(minus(x,y)) == 1 for x,y in combinations(triangle,2))
    for apex in [A,S]:
        assert [4*norm2(minus(x,y)) for x,y in [(B,M),(apex,M),(apex,B)]] == [1,3,4]
    edges = {tuple(sorted(e)) for k in 'TUVW' for i in range(5)
             for e in combinations(face(k+str(i)),2)}
    nbr = [set(j for j in range(12) if tuple(sorted((i,j))) in edges) for i in range(12)]
    assert nbr[0] | set.union(*(nbr[j] for j in nbr[0])) == set(range(11))

if __name__ == '__main__':
    upper()
    lower()
    print('Icosahedron: both convex strips, averaged matrix, ring calibration verified.')
