#!/usr/bin/env python3
"""Exact, finite checks for the grid, winding and cone constructions.

Run with python3 code/geometry_checks.py. Python's Fraction gives all
rational arithmetic. The test range is finite; proofs for general inputs
are in the report.
"""

from fractions import Fraction as Q
from itertools import combinations_with_replacement, permutations, product


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def component_ids(n, edges):
    neighbours = [[] for _ in range(n)]
    for x, y in edges:
        neighbours[x].append(y)
        neighbours[y].append(x)
    labels = [-1] * n
    for x in range(n):
        if labels[x] >= 0:
            continue
        labels[x] = x
        stack = [x]
        while stack:
            for y in neighbours[stack.pop()]:
                if labels[y] < 0:
                    labels[y] = x
                    stack.append(y)
    return labels


def grid_edges(a, b):
    exterior = a * b

    def vertex(x, y):
        return x + (a + 1) * y

    def face(x, y):
        if 0 <= x < a and 0 <= y < b:
            return x + a * y
        return exterior

    edges = []
    for j in range(b + 1):
        for i in range(a):
            edges.append((vertex(i, j), vertex(i + 1, j),
                          face(i, j - 1), face(i, j)))
    vertical = {}
    for j in range(b):
        for i in range(a + 1):
            vertical[i, j] = len(edges)
            edges.append((vertex(i, j), vertex(i, j + 1),
                          face(i - 1, j), face(i, j)))
    return edges, vertical


def test_grid():
    a = b = 2
    n = (a + 1) * (b + 1)
    exterior = a * b
    edges, vertical = grid_edges(a, b)
    boundary = {}
    for sides in range(1 << exterior):
        z = sum(1 << i for i, (_, _, f, g) in enumerate(edges)
                if ((sides >> f) ^ (sides >> g)) & 1)
        check(z not in boundary, "boundary injectivity")
        boundary[z] = sides
    cycles = 0
    for z in range(1 << len(edges)):
        primal = []
        dual = []
        degrees = [0] * n
        for i, (u, v, f, g) in enumerate(edges):
            if z >> i & 1:
                primal.append((u, v))
                degrees[u] += 1
                degrees[v] += 1
            else:
                dual.append((f, g))
        primal_class = component_ids(n, primal)
        dual_class = component_ids(exterior + 1, dual)
        c, faces = len(set(primal_class)), len(set(dual_class))
        check(n - len(primal) + faces == 1 + c, "Euler region formula")
        even = all(d % 2 == 0 for d in degrees)
        check(even == (z in boundary), "even chains equal boundaries")
        contained_cycles = sum(y & ~z == 0 for y in boundary)
        check(contained_cycles == 1 << (faces - 1), "cycles in drawing")
        if not even:
            continue
        sides = 0
        for j in range(b):
            parity = 0
            for i in range(a):
                parity ^= (z >> vertical[i, j]) & 1
                sides |= parity << (i + a * j)
            check(parity == (z >> vertical[a, j]) & 1, "right boundary")
        check(sides == boundary[z], "horizontal reconstruction")
        inhabited = [u for u in range(n) if degrees[u]]
        if (inhabited and all(degrees[u] == 2 for u in inhabited)
                and len({primal_class[u] for u in inhabited}) == 1):
            cycles += 1
            check(faces == 2, "Jordan region count")
            for f, g in product(range(exterior + 1), repeat=2):
                same_side = not (((sides >> f) ^ (sides >> g)) & 1)
                check(same_side == (dual_class[f] == dual_class[g]),
                      "Jordan reachability agrees with scan")
    check(cycles == 13, "simple polygon count")
    print(f"Grid: {1 << len(edges)} drawings, {len(boundary)} even chains, "
          f"{cycles} simple polygons")


def short_step(a, b):
    delta = (b - a) % 1
    if delta > Q(1, 2):
        delta -= 1
    return delta if abs(delta) < Q(1, 4) else None


def test_winding():
    n = 40
    faces = 0
    for degree in range(-4, 5):
        readings = []
        for j in range(n + 1):
            row = []
            for i in range(n + 1):
                t, s = Q(i, n), Q(j, n)
                triangle = 2 * min(t, 1 - t)
                value = degree * t + s / 3 + triangle * s / 5
                # A small deterministic sample error, periodic at the seam.
                error = Q(((i % n + 3 * j) % 3) - 1, 512)
                row.append((value + error) % 1)
            readings.append(row)
        horizontal = [[short_step(row[i], row[i + 1]) for i in range(n)]
                      for row in readings]
        vertical = [[short_step(readings[j][i], readings[j + 1][i])
                     for i in range(n + 1)] for j in range(n)]
        check(all(d is not None for path in horizontal + vertical for d in path),
              "grid has a common short branch")
        for j in range(n):
            for i in range(n):
                total = (horizontal[j][i] + vertical[j][i + 1]
                         - horizontal[j + 1][i] - vertical[j][i])
                check(total == 0, "each winding face sums to zero")
                faces += 1
        check(all(sum(row) == degree for row in horizontal),
              "every loop slice preserves degree")
        check(all(row[0] == row[-1] for row in readings), "periodic seam")
    # Force the side readings to agree in an attempted lift interpolation
    # from degree one to a constant. Somewhere short-step validity must fail.
    failed = False
    for j in range(n + 1):
        row = [(1 - Q(j, n)) * Q(i, n) for i in range(n)] + [Q(0)]
        failed |= any(short_step(a, b) is None for a, b in zip(row, row[1:]))
    check(failed, "degree-changing interpolation must break a short edge")
    print(f"Winding: {faces} exact mesh face sums across nine signed degrees")


def norm(v):
    return max(map(abs, v))


def dot(v, w):
    return sum(a * b for a, b in zip(v, w))


def annihilator(vertices, size):
    rows = [[Q(x) for x in v[:size]] for v in vertices]
    pivots = []
    for col in range(size):
        row = len(pivots)
        chosen = next((i for i in range(row, len(rows)) if rows[i][col]), None)
        if chosen is None:
            continue
        rows[row], rows[chosen] = rows[chosen], rows[row]
        scale = rows[row][col]
        rows[row] = [x / scale for x in rows[row]]
        for i in range(len(rows)):
            if i != row and rows[i][col]:
                factor = rows[i][col]
                rows[i] = [x - factor * y for x, y in zip(rows[i], rows[row])]
        pivots.append(col)
    free = next(col for col in range(size) if col not in pivots)
    coeffs = [Q(0)] * size
    coeffs[free] = Q(1)
    for row, col in enumerate(pivots):
        coeffs[col] = -rows[row][free]
    coeffs.extend([Q(0)] * (len(vertices[0]) - size))
    check(any(coeffs) and all(dot(coeffs, v) == 0 for v in vertices),
          "nonzero simplex annihilator")
    return coeffs


def polynomial_with_roots(roots):
    coeffs = [Q(1)]
    for r in roots:
        updated = [Q(0)] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            updated[i] -= r * c
            updated[i + 1] += c
        coeffs = updated
    return coeffs


def span_of_kernel(coeffs):
    # Leading coefficient is one; these independent rows span the kernel.
    rows = []
    for i, c in enumerate(coeffs[:-1]):
        v = [Q(0)] * len(coeffs)
        v[i] = Q(1)
        v[-1] = -c
        scale = norm(v)
        rows.append([x / scale for x in v])
    return rows


def cone_direction(k, simplices):
    size = k + 2
    ambient = len(simplices[0][0])
    covectors = [annihilator(face, size) for face in simplices]
    for j in range((k + 1) * len(simplices) + 1):
        u = [Q(j ** i) for i in range(size)] + [Q(0)] * (ambient - size)
        if all(dot(c, u) for c in covectors):
            scale = norm(u)
            w = [x / scale for x in u]
            bound = min([Q(1, 2)] + [abs(dot(c, w)) / (8 * sum(map(abs, c)))
                                       for c in covectors])
            return j, w, bound
    raise AssertionError("no cone direction")


def check_cone_times(simplices, w, bound, near_boundary):
    checks = 0
    for face in simplices:
        # Exercise faces, edge midpoints (including repeats), and the barycentre.
        samples = list(face)
        samples.extend([[(a + b) / 2 for a, b in zip(v, z)]
                        for v, z in combinations_with_replacement(face, 2)])
        samples.append([sum(xs) / len(face) for xs in zip(*face)])
        for p in samples:
            for s in [Q(1, 16)] + [Q(i, 8) for i in range(9)]:
                if s < Q(1, 8) and not near_boundary:
                    continue
                v = [(1 - s) * x + s * y for x, y in zip(p, w)]
                check(norm(v) >= bound, "cone lower bound")
                checks += 1
    return checks


def test_cone():
    checks = 0
    for k in range(5):
        d, count = k + 1, 3
        # Distinct simplexes exclude disjoint blocks of moment-curve values.
        # Together they force the algorithm to take the very last candidate.
        faces = [span_of_kernel(polynomial_with_roots(range(i * d, (i + 1) * d)))
                 for i in range(count)]
        j, w, bound = cone_direction(k, faces)
        check(j == d * count, "moment-curve search bound attained")
        checks += check_cone_times(faces, w, bound, near_boundary=False)
        # All first k+2 coordinates vanish in the first simplex; other
        # simplexes have repeated vertices or only a one-dimensional span.
        ambient = k + 3
        zero_projection = [Q(0)] * (ambient - 1) + [Q(1)]
        close_points = []
        for i in range(k + 1):
            v = zero_projection[:]
            v[0] = Q(i, 64)
            close_points.append(v)
        faces = [[zero_projection] * d, [close_points[-1]] * d, close_points]
        _, w, bound = cone_direction(k, faces)
        checks += check_cone_times(faces, w, bound, near_boundary=True)
    print(f"Cone: {checks} positive rational denominator checks for degrees 0–4, "
          "including sharp avoidance scans and rank-deficient simplices")


def test_triangulation():
    checks = 0
    for k in range(1, 5):
        values = {}
        for corner in product((0, 1), repeat=k):
            for order in permutations(range(k)):
                vertices = [list(corner)]
                for coordinate in order:
                    next_vertex = vertices[-1][:]
                    next_vertex[coordinate] += 1
                    vertices.append(next_vertex)
                for increasing in combinations_with_replacement((Q(0), Q(1, 2), Q(1)), k):
                    ts = list(reversed(increasing))
                    weights = [a - b for a, b in zip([Q(1)] + ts, ts + [Q(0)])]
                    x = list(corner)
                    for coordinate, t in zip(order, ts):
                        x[coordinate] += t
                    check(all(w >= 0 for w in weights) and sum(weights) == 1,
                          "simplex barycentric weights")
                    check(all(sum(w * v[i] for w, v in zip(weights, vertices)) == x[i]
                              for i in range(k)), "affine reproduction")
                    samples = [(-1) ** sum(v) * (1 + sum(i * u for i, u in enumerate(v)))
                               for v in vertices]
                    reading = sum(w * z for w, z in zip(weights, samples))
                    key = tuple(x)
                    if key in values:
                        check(reading == values[key], "interpolation across ties and faces")
                    values[key] = reading
                    checks += 1
        check(len(values) == 5 ** k, "half-grid covered by simplices")
    print(f"Triangulation: {checks} exact simplex readings in dimensions 1–4")


if __name__ == "__main__":
    test_grid()
    test_winding()
    test_cone()
    test_triangulation()
