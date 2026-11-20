"""Exact finite checks for the irrational double pole in the manuscript."""
from collections import Counter
from fractions import Fraction as Q
from itertools import pairwise
from math import isqrt

Point = tuple[Q, Q]


def center(t: int) -> Point:
    m = 2 ** (t + 2)
    return (Q(isqrt(2 * m * m), m), Q(isqrt(3 * m * m), m))


def square(x0: Q, y0: Q, x1: Q, y1: Q) -> list[Point]:
    return [(x0, y0), (x1, y0), (x1, y1), (x0, y1)]


def boundary(vertices: list[Point]) -> Counter:
    result = Counter()
    for a, b in pairwise([*vertices, vertices[0]]):
        if a < b:
            result[a, b] += 1
        elif b < a:
            result[b, a] -= 1
    return result


def check_example() -> None:
    r = Q(1, 64)
    b = center(14)
    v = center(40)
    assert sum(abs(x - y) for x, y in zip(b, v)) <= r / 64
    assert all(1 < x - 9 * r and x + 9 * r < 2 for x in b)

    xs = [Q(1), b[0] - r, b[0] + r, Q(2)]
    ys = [Q(1), b[1] - r, b[1] + r, Q(2)]
    triangles = []
    for i, (x0, x1) in enumerate(pairwise(xs)):
        for j, (y0, y1) in enumerate(pairwise(ys)):
            if (i, j) != (1, 1):
                a, c, d, e = square(x0, y0, x1, y1)
                triangles.extend(([a, c, d], [a, d, e]))
    assert len(triangles) == 16
    outer = [(x, ys[0]) for x in xs]
    outer += [(xs[-1], y) for y in ys[1:]]
    outer += [(x, ys[-1]) for x in reversed(xs[:-1])]
    outer += [(xs[0], y) for y in reversed(ys[1:-1])]
    hole = square(xs[1], ys[1], xs[2], ys[2])
    check = Counter()
    for tri in triangles:
        check.update(boundary(tri))
    check.subtract(boundary(outer))
    check.update(boundary(hole))
    assert all(value == 0 for value in check.values())

    lifted = square(v[0] - r, v[1] - r, v[0] + r, v[1] + r)
    check = Counter()
    for i in range(4):
        j = (i + 1) % 4
        check.update(boundary([hole[i], hole[j], lifted[j]]))
        check.update(boundary([hole[i], lifted[j], lifted[i]]))
    check.subtract(boundary(hole))
    check.update(boundary(lifted))
    assert all(value == 0 for value in check.values())

    # The exact residue is twice the named centre. Each floor error is < 1/m.
    m = 2 ** 42
    for u, square_value in zip(v, [2, 3]):
        assert u * u <= square_value < (u + Q(1, m)) ** 2
    print("Verified 16-triangle filling and 8-triangle moving boundary.")
    for axis, u in zip(("real", "imaginary"), v):
        print(f"{axis} component of residue in [{2*u}, {2*u+Q(2,m)}).")


if __name__ == "__main__":
    check_example()
