"""Verify that an explicit four-link space curve has width/length = 1/4.

Before normalization, the vertices in traversal order are
   (sqrt(15),0,0), (0,-3,4), (0,0,5), (0,3,4), (-sqrt(15),0,0).
The outer links have squared length 40 and the inner links have squared
length 10, so the length is 6 sqrt(10). Reflections in x=0 or y=0
preserve the convex hull, and reversing a normal preserves its width.
Hence we may take a normal (x,y,z) with all three coordinates nonnegative.

Put a=sqrt(15)*x, b=3*y, c=z. Its directional spread is
    max(a, b+4c, 5c) + max(a, b-4c).
Spread at most 1 is equivalent to the seven inequalities below.
On the resulting bounded polytope the squared length of the normal is
a convex quadratic, so it has a maximum at a vertex. The least width
in a unit direction is the reciprocal square root of this maximum.
"""

from fractions import Fraction
from itertools import combinations


# Each row represents i*a + j*b + k*c <= limit.
HALFSPACES = (
    (-1, 0, 0, 0),
    (0, -1, 0, 0),
    (0, 0, -1, 0),
    (2, 0, 0, 1),
    (0, 2, 0, 1),
    (1, 1, 4, 1),
    (1, 0, 5, 1),
)


def determinant(rows):
    (a, b, c), (d, e, f), (g, h, i) = rows
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def vertices(halfspaces):
    """Enumerate feasible intersections of three independent boundary planes."""
    points = set()
    for active in combinations(halfspaces, 3):
        rows = [plane[:3] for plane in active]
        denominator = determinant(rows)
        if denominator == 0:
            continue
        point = []
        for column in range(3):
            replaced = [list(row) for row in rows]
            for row, plane in zip(replaced, active):
                row[column] = plane[3]
            point.append(Fraction(determinant(replaced), denominator))
        a, b, c = point
        if all(i*a + j*b + k*c <= limit for i, j, k, limit in halfspaces):
            points.add(tuple(point))
    return sorted(points)


def squared_normal(point):
    a, b, c = point
    return a*a / 15 + b*b / 9 + c*c


def main():
    points = vertices(HALFSPACES)
    maximum = max(map(squared_normal, points))
    squared_width = 1 / maximum
    squared_length = 36 * 10
    assert len(points) == 9 and maximum == Fraction(2, 45)
    assert squared_width / squared_length == Fraction(1, 16)
    print("Vertices (a, b, c) and squared normal lengths")
    for point in points:
        print("  " + ", ".join(map(str, point)) + "    " + str(squared_normal(point)))
    print(f"Maximum squared normal length = {maximum}")
    print(f"Squared width = {squared_width}, squared length = {squared_length}")
    print("Width after normalization to unit length = 1/4")


if __name__ == "__main__":
    main()
