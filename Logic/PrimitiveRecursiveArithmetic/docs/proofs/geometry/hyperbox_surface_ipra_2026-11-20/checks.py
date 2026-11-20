"""Reproducible checks against separate exact formulas. Run python checks.py."""

from fractions import Fraction as Q
from itertools import product
from random import Random

from hyperbox import surface_squared, vertex_maximum


def rectangle_parameter(sides, point):
    a, b = sides
    x, y = point
    if y == 0:
        return x
    if x == a:
        return a + y
    if y == b:
        return 2 * a + b - x
    assert x == 0
    return 2 * a + 2 * b - y


def paper_cuboid_vertex(sides):
    # Three-dimensional formulas in the attached cuboid report.
    a, b, c = sides
    opposite_square = (a + b) ** 2 + c * c
    delta = a * (c - b) / (2 * c)
    off_vertex_square = ((b*b + c*c) * (a*a + 2*a*c + 2*c*c)
                         / (2*c*c))
    if off_vertex_square > opposite_square:
        return off_vertex_square, (a - delta, b - delta, c)
    return opposite_square, sides


def paper_cuboid_top(sides, p):
    a, b, c = sides
    x, y, _ = p
    sites = [(-c, 0), (a+c, -a), (0, -c), (-b, b+c)]
    return min((x-u)**2 + (y-v)**2 for u, v in sites)


def prism_top(c, p):
    base = p[:-1]
    lower, upper = min(base), max(base)
    increment = min(2*c*lower, 2*c+2-2*(c+1)*upper+2*lower)
    return c*c + sum(x*x for x in base) + increment


def check():
    rng = Random(20261119)
    rectangle = (Q(5, 3), Q(7, 4))
    a, b = rectangle
    points = [(q*a, wall*b) for q in (Q(0), Q(1, 3), Q(1)) for wall in (0, 1)]
    points += [(wall*a, q*b) for q in (Q(1, 5), Q(2, 3)) for wall in (0, 1)]
    perimeter = 2 * (a + b)
    for p, q in product(points, repeat=2):
        gap = abs(rectangle_parameter(rectangle, p) - rectangle_parameter(rectangle, q))
        expected = min(gap, perimeter-gap)**2
        assert surface_squared(rectangle, p, q) == expected
    print(f"Rectangle perimeter metric: {len(points)**2} exact pairs")

    for _ in range(16):
        sides = tuple(sorted(Q(rng.randint(2, 17), rng.randint(1, 4)) for _ in range(3)))
        result = vertex_maximum(sides,arrangement=True)
        expected, witness = paper_cuboid_vertex(sides)
        assert result["squared"] == expected
        assert surface_squared(sides, (0, 0, 0), witness) == expected
        for _ in range(5):
            p = tuple(sides[i]*Q(rng.randrange(13), 12) for i in range(2)) + (sides[2],)
            assert surface_squared(sides, (0, 0, 0), p) == paper_cuboid_top(sides, p)
    print("General rational cuboids: 16 exact maxima and 80 top-face distances")

    for n in range(2, 7):
        # The origin/opposite-corner lower bound is independent of unfoldings.
        sides = tuple(Q(2*i+3, i+2) for i in range(n))
        ordered = sorted(sides)
        expected = sum(a*a for a in sides) + 2*ordered[0]*ordered[1]
        assert surface_squared(sides, (0,)*n, sides) == expected
    print("Opposite corners in dimensions 2 through 6")

    count = 0
    for n in (3, 4, 5):
        for c in (Q(1), Q(5, 4), Q(3), Q(5)):
            sides = (Q(1),)*(n-1) + (c,)
            base_points = [(Q(0),)*(n-1), (Q(1),)*(n-1),
                           ((c+1)/(2*c),)*(n-1)]
            base_points += [tuple(Q(rng.randrange(9), 8) for _ in range(n-1))
                            for _ in range(6)]
            for base in base_points:
                p = base + (c,)
                assert surface_squared(sides, (0,)*n, p) == prism_top(c, p)
                count += 1
    print(f"Cubical-base prism formula: {count} exact top-face distances")

    sides = (1, 1, 1, 5)
    result = vertex_maximum(sides,arrangement=True)
    assert result["squared"] == Q(802, 25)
    assert result["point"] == (Q(3,5),)*3 + (Q(5),)
    assert surface_squared(sides, (Q(1,2),)*3 + (0,), (Q(1,2),)*3 + (5,)) == 36
    print("4D prism: exact fixed square 802/25 and cap-center square 36")

    # Select T so its square minus one is also a rational square.
    # This allows a fully rational independent evaluation at the proposed
    # unrestricted optimizer, plus nearby symmetric and asymmetric pairs.
    count = 0
    for d, k in [(2, 8), (3, 10)]:
        t = Q(k*k+1, 2*k)
        delta = Q(1, 2*k)
        sides = (Q(1),)*d + (t,)
        optimum = (t+1)**2 + 4*(d-1)*delta**2
        p = (Q(1,2)-delta,)*d + (Q(0),)
        q = (Q(1,2)+delta,)*d + (t,)
        assert surface_squared(sides, p, q) == optimum
        for _ in range(12):
            left = tuple(x+Q(rng.randint(-2,2), 100) for x in p[:-1])+(Q(0),)
            right = tuple(x+Q(rng.randint(-2,2), 100) for x in q[:-1])+(t,)
            assert surface_squared(sides, left, right) <= optimum
            count += 1
    print(f"Long-prism diameter: two exact algebraic-form witnesses and {count} nearby pairs")

    sides = (Q(3), Q(1), Q(2))
    result = vertex_maximum(sides, (1, 0, 1))
    p = result["point"]
    assert surface_squared(sides, (3, 0, 2), p) == result["squared"]
    assert result["squared"] == paper_cuboid_vertex(tuple(sorted(sides)))[0]
    print("Unsorted axes and reflected source verified")


if __name__ == "__main__":
    check()
