"""Verify the variable-pose space-worm upper bound with exact arithmetic.

Run python3 check_adaptive.py with the two JSON files in this directory.
The only floating-point conversions display the checked rational quantities.
"""
from fractions import Fraction as F
from pathlib import Path
from functools import reduce
from math import comb, gcd
from collections import Counter
import json
DIR = Path(__file__).resolve().parent
SCALE = 10 ** 8

def direction(t):
    """Rational circle parametrization for the four planar support normals."""
    return ((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))

def intersect(a, d, b, e):
    D = a[0] * b[1] - a[1] * b[0]
    return ((d * b[1] - a[1] * e) / D, (a[0] * e - d * b[0]) / D)

def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])

def dot(a, b):
    return sum((x * y for x, y in zip(a, b)))

def interpolation_inverse():
    """Inverse of the degree-five Bernstein evaluation matrix at j/5."""
    M = [[F(comb(5, k) * j ** k * (5 - j) ** (5 - k), 5 ** 5) for k in range(6)] + [F(k == j) for k in range(6)] for j in range(6)]
    for k in range(6):
        m = M[k][k]
        assert m
        M[k] = [x / m for x in M[k]]
        for j in range(6):
            if j != k:
                f = M[j][k]
                M[j] = [x - f * y for x, y in zip(M[j], M[k])]
    return [r[6:] for r in M]

def points():
    """Generate every homogeneous control point, then round in each coordinate."""
    ns = list(map(direction, [F(-631, 58), F(-1), F(7, 16), F(37, 56)]))
    ds = [F(0), F(0), F(130783, 250000), F(446199, 10 ** 6)]
    C = [intersect(ns[i], ds[i], ns[i - 1], ds[i - 1]) for i in range(4)]
    assert all((nx * x + ny * y <= offset for (nx, ny), offset in zip(ns, ds) for x, y in C))
    poses = [[F(s, SCALE) for s in row] for row in json.loads((DIR / 'poses.json').read_text())]
    assert len(poses) == 32 and poses[0][0] == 0 and (poses[-1][0] == 1)
    assert poses[18][0] == poses[19][0]
    B = interpolation_inverse()
    Q = set()
    for L, R in zip(poses, poses[1:]):
        if L[0] == R[0]:
            continue
        assert L[0] < R[0] and dot(L[1:5], R[1:5]) > 0
        for sub in range(3):
            rows = [[] for i in range(8)]
            for j in range(6):
                s = F(sub * 5 + j, 15)
                t, x, y, z, w, tx, ty, tz = [a * (1 - s) + b * s for a, b in zip(L, R)]
                q = (x, y, z)
                qq = dot(q, q)
                Q2 = qq + w * w
                D = (1 + t * t) * Q2
                for i, (a, b) in enumerate(C + C):
                    v = (a * (1 - t * t), b * (1 - t * t), F(2, 3) * t * (i >= 4))
                    qqv = 2 * dot(q, v)
                    qxv = cross(q, v)
                    num = [(w * w - qq) * v[k] + qqv * q[k] + 2 * w * qxv[k] + D * g for k, g in enumerate((tx, ty, tz))]
                    rows[i].append(num + [D])
            for samples in rows:
                cols = list(zip(*samples))
                for coeffs in B:
                    nx, ny, nz, d = [dot(col, coeffs) for col in cols]
                    assert d > 0
                    Q.add(tuple((round(c * SCALE / d) for c in (nx, ny, nz))))
    return sorted(Q)

def face(p, q, r):
    """Integer coefficients of the plane through three noncollinear grid points."""
    n = cross([a - b for a, b in zip(q, p)], [a - b for a, b in zip(r, p)])
    n = (*n, -dot(n, p))
    g = reduce(gcd, n)
    assert g
    return tuple((x // g for x in n))

def ring(points, inds, n):
    """Project a facet to a coordinate plane and recover its convex boundary."""
    skip = next((i for i in range(3) if n[i]))
    a, b = [i for i in range(3) if i != skip]
    order = sorted(inds, key=lambda i: (points[i][a], points[i][b]))

    def half(seq):
        out = []
        for i in seq:
            z = points[i]
            while len(out) >= 2:
                y = points[out[-1]]
                x = points[out[-2]]
                if (y[a] - x[a]) * (z[b] - x[b]) - (y[b] - x[b]) * (z[a] - x[a]) > 0:
                    break
                out.pop()
            out.append(i)
        return out[:-1]
    return half(order) + half(reversed(order))

def certify(points, hints):
    """Check facet support, completeness, volume, and the dilation margin."""
    c = (17000000, 13000000, 7000000)
    r = SCALE // 40
    edges = Counter()
    facets = set()
    mass = 0
    for i, j, k in hints:
        plane = face(points[i], points[j], points[k])
        a, b, c0, d = plane
        vals = [a * x + b * y + c0 * z + d for x, y, z in points]
        if max(vals) > 0:
            vals = [-v for v in vals]
            plane = tuple((-v for v in plane))
        assert max(vals) == 0 and min(vals) < 0 and (plane not in facets)
        facets.add(plane)
        n = plane[:3]
        assert dot(n, c) + plane[3] + r * sum((abs(v) for v in n)) <= 0
        polygon = ring(points, [i for i, v in enumerate(vals) if v == 0], n)
        for i, j in zip(polygon, polygon[1:] + polygon[:1]):
            edges[tuple(sorted((i, j)))] += 1
        for j, k in zip(polygon[1:-1], polygon[2:]):
            a, b, d = ([points[i][l] - c[l] for l in range(3)] for i in (polygon[0], j, k))
            mass += abs(dot(a, cross(b, d)))
    assert set(edges.values()) == {2}
    v = F(mass, 6 * SCALE ** 3)
    upper = v * (1 + F(1, 2 * r)) ** 3
    assert len(points) == 3606 and len(facets) == 2955
    print(f"{len(points)} generators, {len(facets)} facets.")
    print(f"Exact volume of the covering polytope: {upper}")
    assert F('0.052942305537') < upper < F('0.052942305538')
    print('Certified universal volume < 0.052942305538.')
if __name__ == '__main__':
    certify(points(), json.loads((DIR / 'adaptive_facets.json').read_text()))
