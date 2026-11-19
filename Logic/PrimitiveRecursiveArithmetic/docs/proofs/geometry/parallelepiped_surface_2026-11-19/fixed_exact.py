#!/usr/bin/env python3
"""Exact fixed-vertex farthest points for rationally unfoldable parallelepipeds.

All calculations use fractions. Arguments and returned points use edge coordinates.
The six Gram entries are g11,g22,g33,g12,g13,g23. JSON lists all maximizing points.
"""
import argparse
import json
from fractions import Fraction as F
from itertools import combinations, product
from math import isqrt


def gram_matrix(entries):
    a, b, c, d, e, f = map(F, entries)
    if a <= 0 or a*b <= d*d or a*b*c + 2*d*e*f <= a*f*f + b*e*e + c*d*d:
        raise ValueError("the Gram matrix must be positive definite")
    return ((a, d, e), (d, b, f), (e, f, c))


def sqroot(a):
    x, y = isqrt(a.numerator), isqrt(a.denominator)
    if x*x != a.numerator or y*y != a.denominator:
        raise ValueError("this chart needs an irrational square root; use SkewExact.wl or mesh_bounds.py")
    return F(x, y)


def add(p, q):
    return (p[0] + q[0], p[1] + q[1])


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def mul(t, p):
    return (t*p[0], t*p[1])


def dot(p, q):
    return p[0]*q[0] + p[1]*q[1]


def det(p, q):
    return p[0]*q[1] - p[1]*q[0]


def norm2(p):
    return dot(p, p)


def base(g, axis):
    j, k = [i for i in range(3) if i != axis]
    length = sqroot(g[j][j])
    return {j: (length, F(0)), k: (g[j][k]/length, sqroot(g[k][k] - g[j][k]**2/g[j][j]))}


def unfold(g, axis, bit, origin, vectors, next_axis, next_bit):
    s = 3-axis-next_axis
    seam = vectors[s]
    anchor = add(origin, mul(next_bit, vectors[next_axis]))
    side = 1 if det(seam, vectors[next_axis]) > 0 else -1
    sign = -side*(1 - 2*bit)*(1 - 2*next_bit)
    left = (-seam[1], seam[0])
    alt = sqroot(g[axis][axis]*g[s][s] - g[axis][s]**2)
    across = mul(1/g[s][s], add(mul(g[axis][s], seam), mul(sign*alt, left)))
    return sub(anchor, mul(bit, across)), {s: seam, axis: across}, (anchor, add(anchor, seam))


def strips(g, target):
    rows = []
    def extend(axis, origin, vectors, gates, visited):
        for k in range(3):
            if k == axis:
                continue
            for bit in (0, 1):
                if bit == 1 and k in visited:
                    continue
                org, dirs, gate = unfold(g, axis, 1, origin, vectors, k, bit)
                next_gates = gates + [gate]
                if bit == 0:
                    # Local origin of a zero face is the selected vertex.
                    rows.append((org, next_gates))
                else:
                    extend(k, org, dirs, next_gates, visited | {k})
    extend(target, (F(0), F(0)), base(g, target), [], {target})
    return rows


def legal(p, q, gates):
    """Greedily take the first available point in each ordered seam interval."""
    v = sub(q, p)
    low = F(0)
    for a, b in gates:
        w, u = sub(b, a), sub(a, p)
        cross = det(v, w)
        if cross:
            t, r = det(u, w)/cross, det(u, v)/cross
            if not (low <= t <= 1 and 0 <= r <= 1):
                return False
            low = t
        elif det(u, w):
            return False
        elif v != (0, 0):
            i = 0 if v[0] else 1
            x, y = sorted(((a[i]-p[i])/v[i], (b[i]-p[i])/v[i]))
            low = max(low, x)
            if low > min(1, y):
                return False
        elif dot(sub(p, a), sub(p, b)) > 0:
            return False
    return True


def cross_lines(a, b):
    n, r = a
    m, s = b
    delta = det(n, m)
    if delta:
        return ((r*m[1]-s*n[1])/delta, (s*n[0]-r*m[0])/delta)
    return None


def bisector(a, b):
    return mul(2, sub(b, a)), norm2(b) - norm2(a)


def fixed_max(g, vertex=(0, 0, 0)):
    if len(vertex) != 3 or any(b not in (0, 1) for b in vertex):
        raise ValueError("a vertex must have three binary coordinates")
    signs = [1-2*b for b in vertex]
    g = tuple(tuple(signs[i]*signs[j]*g[i][j] for j in range(3)) for i in range(3))
    best, winners = F(0), set()
    def record(value, p):
        nonlocal best, winners
        p = tuple(vertex[i] + signs[i]*p[i] for i in range(3))
        if value > best:
            best, winners = value, {p}
        elif value == best:
            winners.add(p)

    counts = []
    for axis in range(3):
        j, k = [i for i in range(3) if i != axis]
        vectors = base(g, axis)
        a, b = vectors[j], vectors[k]
        corners = {(F(0), F(0)), a, b, add(a, b)}
        for u, v in product((0, 1), repeat=2):
            p = [F(0)]*3
            p[j], p[k] = F(u), F(v)
            record(norm2(add(mul(u, a), mul(v, b))), p)
        rows = strips(g, axis)
        sites = sorted({z for z, _ in rows})
        candidates = set(corners)
        edges = [(x, y) for x, y in combinations(corners, 2) if sub(y,x) in (a,b,mul(-1,a),mul(-1,b))]
        for x, y in combinations(sites, 2):
            line = bisector(x, y)
            for start, end in edges:
                w = sub(end, start)
                normal = (-w[1], w[0])
                pt = cross_lines(line, (normal, dot(start, normal)))
                if pt is not None:
                    candidates.add(pt)
        for x, y, z in combinations(sites, 3):
            pt = cross_lines(bisector(x, y), bisector(x, z))
            if pt is not None:
                candidates.add(pt)
        num = 0
        for pt in candidates:
            u = det(pt, b)/det(a, b)
            v = det(a, pt)/det(a, b)
            if not (0 <= u <= 1 and 0 <= v <= 1):
                continue
            num += 1
            valid = [norm2(sub(pt, z)) for z, gates in rows if legal(pt, z, gates)]
            if not valid:
                raise ArithmeticError("no admissible developed segment at a candidate")
            p = [F(1)]*3
            p[j], p[k] = u, v
            record(min(valid), p)
        counts.append(num)
    return {"squared_eccentricity": str(best), "farthest_edge_coordinates": [[str(a) for a in p] for p in sorted(winners)],
            "candidates_on_three_opposite_faces": counts}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gram", default="1,1,4,0,0,0", help="six comma-separated integers or fractions")
    parser.add_argument("--vertex", default="0,0,0")
    args = parser.parse_args()
    try:
        print(json.dumps(fixed_max(gram_matrix(args.gram.split(",")), tuple(map(int, args.vertex.split(",")))), indent=2))
    except ValueError as error:
        parser.error(str(error))
