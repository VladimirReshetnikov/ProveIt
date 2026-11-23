"""Exact rational cap construction from the Seifert-surface chapter.

cap(poly) assumes a simple cyclic polygon without zero-length edges. Its
output triangles are counterclockwise and include subdivisions of all sides.
Run this file directly for deterministic regression checks (standard library).
"""

from collections import defaultdict
from fractions import Fraction as Q
from random import Random


def det(a, b, c):
    """Signed double area of an ordered triangle."""
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def edges(vertices):
    return zip(vertices, vertices[1:] + vertices[:1])


def lies_on(point, a, b):
    return det(a, b, point) == 0 and all(
        min(x, y) <= t <= max(x, y) for t, x, y in zip(point, a, b)
    )


def add_wall_mark(triangles, point):
    """Split the unique boundary side containing the new mark in its interior."""
    for idx, tri in enumerate(triangles):
        for j in range(3):
            a, b, c = tri[j], tri[(j + 1) % 3], tri[(j + 2) % 3]
            if point != a and point != b and lies_on(point, a, b):
                triangles[idx:idx + 1] = [(a, point, c), (point, b, c)]
                return
    raise ValueError("Inconsistent trapezoid boundary")


def cap(poly):
    """Return a triangulated planar disk for a simple rational polygon."""
    p = [(Q(x), Q(y)) for x, y in poly]
    n = len(p)
    if n < 3 or len(set(p)) != n:
        raise ValueError("Expected at least three distinct vertices")
    h = next(i for i in range(n * (n - 1) // 2 + 1)
             if len({x + i * y for x, y in p}) == n)
    swept = [(x + h * y, y) for x, y in p]
    wall_x = sorted(x for x, _ in swept)
    sides = list(edges(swept))

    def height(edge, x):
        (ax, ay), (bx, by) = edge
        return ay + (by - ay) * (x - ax) / (bx - ax)

    def meets_wall(edge, x):
        a, b = edge
        return min(a[0], b[0]) <= x <= max(a[0], b[0])

    marks = {
        x: sorted({height(e, x) for e in sides if meets_wall(e, x)})
        for x in wall_x
    }
    result = []
    for left, right in zip(wall_x, wall_x[1:]):
        mid = (left + right) / 2
        active = sorted((e for e in sides if meets_wall(e, mid)),
                        key=lambda e: height(e, mid))
        if len(active) % 2:
            raise ValueError("Odd number of edge intersections in a slab")
        for lo, hi in zip(active[::2], active[1::2]):
            corners = [(left, height(lo, left)), (right, height(lo, right)),
                       (right, height(hi, right)), (left, height(hi, left))]
            corners = list(dict.fromkeys(corners))
            faces = [(corners[0], corners[j], corners[j + 1])
                     for j in range(1, len(corners) - 1)]
            for x in (left, right):
                for y in marks[x]:
                    if height(lo, x) < y < height(hi, x):
                        add_wall_mark(faces, (x, y))
            result.extend(tuple((x - h * y, y) for x, y in tri) for tri in faces)
    return result


def verify(poly, triangles):
    """Check area, boundary subdivisions, incidence orientations and dual tree."""
    signed_area2 = sum(x * v - y * u for (x, y), (u, v) in edges(poly))
    assert all(det(*t) > 0 for t in triangles)
    assert sum(det(*t) for t in triangles) == abs(signed_area2)
    incidence = defaultdict(list)
    for i, tri in enumerate(triangles):
        for a, b in edges(tri):
            incidence[tuple(sorted((a, b)))].append((i, a, b))
            assert any(lies_on(a, u, v) for u, v in edges(poly))
    dual = [set() for _ in triangles]
    boundary = set()
    for side, uses in incidence.items():
        if len(uses) == 1:
            a, b = side
            assert any(lies_on(a, u, v) and lies_on(b, u, v) for u, v in edges(poly))
            boundary.add(side)
        else:
            assert len(uses) == 2
            (i, a, b), (j, c, d) = uses
            assert a == d and b == c
            dual[i].add(j)
            dual[j].add(i)
    for u, v in edges(poly):
        parts = [(a, b) for a, b in boundary if lies_on(a, u, v) and lies_on(b, u, v)]
        axis = int(u[0] == v[0])
        intervals = sorted(tuple(sorted((a[axis], b[axis]))) for a, b in parts)
        assert intervals and intervals[0][0] == min(u[axis], v[axis])
        assert intervals[-1][1] == max(u[axis], v[axis])
        assert all(prev[1] == nxt[0] for prev, nxt in zip(intervals, intervals[1:]))
    reached, todo = {0}, [0]
    while todo:
        for j in dual[todo.pop()]:
            if j not in reached:
                reached.add(j)
                todo.append(j)
    assert len(reached) == len(triangles)
    assert sum(map(len, dual)) == 2 * (len(triangles) - 1)


def main():
    rng = Random(89762)
    cases = [
        [(0, 0), (2, 0), (0, 1)],
        [(0, 0), (2, 0), (4, 0), (4, 3), (2, 3), (0, 3)],
        [(0, 0), (6, 0), (6, 6), (4, 6), (4, 1), (2, 1), (2, 6), (0, 6)],
        [(0, 0), (7, 0), (7, 7), (6, 7), (6, 2), (5, 2), (5, 6),
         (4, 6), (4, 1), (3, 1), (3, 5), (2, 5), (2, 3), (0, 3)],
    ]
    for n in range(3, 13):
        upper = [(x, Q(rng.randint(1, 12), rng.randint(1, 5))) for x in range(n)]
        lower = [(x, -Q(rng.randint(1, 12), rng.randint(1, 5))) for x in reversed(range(n))]
        cases.append(upper + lower)
    count = 0
    for poly in cases:
        for walk in (poly, poly[::-1], [(y, x) for x, y in poly]):
            verify(walk, cap(walk))
            count += 1
    print(f"Verified boundary, area and dual tree on {count} rational polygon caps.")


if __name__ == "__main__":
    main()
