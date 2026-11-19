#!/usr/bin/env python3
"""Exact arithmetic for the discrete-volume series, including its full order-one term."""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from argparse import ArgumentParser

ORIGIN = (F(0),) * 3
TETRA = [ORIGIN, (F(1, 3), 0, 0), (F(1, 3), F(1, 3), 0), (F(1, 3),) * 3]


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def cross(a, b):
    x, y, z = a
    u, v, w = b
    return y*w-z*v, z*u-x*w, x*v-y*u


def boundary_2d(indices, points, normal):
    drop = max(range(3), key=lambda k: abs(normal[k]))
    i, j = [k for k in range(3) if k != drop]
    pts = sorted((points[k][i], points[k][j], k) for k in indices)

    def chain(seq):
        hull = []
        for p in seq:
            while len(hull) >= 2:
                x, y, _ = hull[-2]
                u, v, _ = hull[-1]
                if (u-x)*(p[1]-y) - (v-y)*(p[0]-x) > 0:
                    break
                hull.pop()
            hull.append(p)
        return hull[:-1]

    return [p[2] for p in chain(pts) + chain(reversed(pts))]


def hull_volume(vertices):
    """Return the volume of a rational hull by face polygons and pyramids."""
    pts = sorted(set(tuple(map(F, p)) for p in vertices))
    ctr = tuple(sum(p[i] for p in pts) / len(pts) for i in range(3))
    face_sets = set()
    six_vol = F(0)
    for a, b, c in combinations(pts, 3):
        n = cross(sub(b, a), sub(c, a))
        if n == ORIGIN:
            continue
        dots = [dot(n, sub(p, a)) for p in pts]
        if min(dots) < 0 < max(dots):
            continue
        face = tuple(i for i, d in enumerate(dots) if d == 0)
        if face in face_sets:
            continue
        face_sets.add(face)
        poly = [sub(pts[k], ctr) for k in boundary_2d(face, pts, n)]
        for k in range(1, len(poly)-1):
            six_vol += abs(dot(poly[0], cross(poly[k], poly[k+1])))
    return six_vol / 6


def quaternion_matrices(m):
    """Rational quaternion rotations from the four maximal-component charts."""
    for pivot in range(4):
        for triple in product(range(-m, m+1), repeat=3):
            q = list(triple)
            q.insert(pivot, m)
            w, x, y, z = q
            norm = w*w + x*x + y*y + z*z
            vals = ((norm-2*(y*y+z*z), 2*(x*y-z*w), 2*(x*z+y*w)),
                    (2*(x*y+z*w), norm-2*(x*x+z*z), 2*(y*z-x*w)),
                    (2*(x*z-y*w), 2*(y*z+x*w), norm-2*(x*x+y*y)))
            yield tuple(tuple(F(t, norm) for t in row) for row in vals)


def cube_rotations():
    for perm in permutations(range(3)):
        inversions = sum(perm[i] > perm[j] for i, j in combinations(range(3), 2))
        for signs in product((-1, 1), repeat=3):
            if signs[0] * signs[1] * signs[2] != (-1) ** inversions:
                continue
            yield tuple(tuple(signs[i] if j == perm[i] else 0 for j in range(3))
                        for i in range(3))


def rotations(m):
    return {tuple(tuple(dot(row, col) for col in zip(*sym)) for row in rot)
            for rot in set(quaternion_matrices(m)) for sym in cube_rotations()}


def walks(n):
    """Yield the exact vertex tuples specified by the finite series formula."""
    scale = n**3
    steps = [tuple(F(x, scale) for x in v)
             for v in product(range(-n*n, n*n+1), repeat=3)
             if dot(v, v) <= n**4]
    for increments in product(steps, repeat=n):
        vertices = [ORIGIN]
        for step in increments:
            vertices.append(add(vertices[-1], step))
        yield tuple(vertices)


def one_point_volume(p):
    """The orthoscheme with one adjoined point, via barycentric coordinates."""
    x, y, z = p
    bary = (1-3*x, 3*(x-y), 3*(y-z), 3*z)
    return (1 + sum(max(-t, 0) for t in bary)) * F(1, 162)


def order_one():
    # The zero walk is redundant, and all six unit steps have the same placements.
    # The candidate hull with the additional segment [0,e1] has volume 1/54.
    # The possible integer initial points of any improving segment satisfy
    # 1 >= x >= y >= z >= 0 by the four barycentric constraints.
    best = F(1, 54)
    best_pose = (ORIGIN, (1, 0, 0))
    ts = [(x, y, z) for x, y, z in product(range(2), repeat=3) if z <= y <= x]
    directions = {tuple(row[0] for row in r) for r in rotations(1)}
    for t, d in product(ts, sorted(directions)):
        end = add(t, d)
        if max(one_point_volume(t), one_point_volume(end)) >= best:
            continue
        v = hull_volume(TETRA + [t, end])
        if v < best:
            best, best_pose = v, (t, d)
    return best, best_pose, len(directions)


def relative_factors(n):
    # Uniform position errors before division by the common inradius 1/15.
    trace_error = F(1, 2*n) + F(7, 4*n*n)
    pose_error = F(9, 2*n*n)
    return 1 / (1 + 15*pose_error)**3, (1 + 15*trace_error)**3


def enumerate_coefficient(n):
    """Exact reference enumeration; its runtime grows rapidly even at order two."""
    if n == 1:
        return order_one()[0]
    family = list(walks(n))
    m = n*n
    catalog = rotations(m)
    translation_indices = range(-114*m, 114*m + 1)

    def poses(path):
        for matrix in catalog:
            vertices = [tuple(dot(row, v) for row in matrix) for v in path]
            for indices in product(translation_indices, repeat=3):
                t = tuple(F(k, m) for k in indices)
                yield tuple(add(v, t) for v in vertices)

    # The identity is in the catalogue. These simultaneous identity placements
    # supply an initial feasible hull and an exact pruning bound.
    start_hull = set(TETRA)
    for path in family:
        start_hull.update(path)
    best = hull_volume(start_hull)
    # Each level chooses a pose for the next walk. Explicit frames keep the
    # reference algorithm independent of Python's call-stack depth.
    frames = [(set(TETRA), poses(family[0]))]
    while frames:
        occupied, choices = frames[-1]
        placed = next(choices, None)
        if placed is None:
            frames.pop()
            continue
        points = occupied.union(placed)
        partial = hull_volume(points)
        if partial >= best:
            continue
        if len(frames) == len(family):
            best = partial
        else:
            frames.append((points, poses(family[len(frames)])))
    return best


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--factors', type=int, help='show certified multiplicative factors for order N')
    parser.add_argument('--order', type=int, help='run the full finite enumeration (only order 1 is practical)')
    args = parser.parse_args()
    if args.order is not None:
        if args.order <= 0:
            parser.error('N must be positive')
        print('finite minimum:', enumerate_coefficient(args.order))
    elif args.factors is not None:
        if args.factors <= 0:
            parser.error('N must be positive')
        lo, hi = relative_factors(args.factors)
        print('L_N / b_N =', lo, '=', float(lo))
        print('U_N / b_N =', hi, '=', float(hi))
    else:
        assert hull_volume(TETRA) == F(1, 162)
        assert hull_volume(TETRA + [(1, 0, 0)]) == F(1, 54)
        assert len(list(walks(1))) == 7
        v, (t, d), count = order_one()
        print('distinct rational segment directions:', count)
        print('b_1 =', v)
        print('one minimizing segment starts at', t, 'with displacement', d)
