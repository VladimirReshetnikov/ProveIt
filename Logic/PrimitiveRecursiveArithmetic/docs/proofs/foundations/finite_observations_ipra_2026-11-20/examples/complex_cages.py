"""Exact rational regression checks for the named-centre contour example.

Run with Python 3.10 or later. No complex floating-point operations are used.
"""
from collections import Counter
from fractions import Fraction as Q
from math import isqrt

Point = tuple[Q, Q]
Edge = tuple[Point, Point]


def sqrt2_name(n: int) -> Q:
    """Lower dyadic approximation to sqrt(2), with error at most 2^-n."""
    power = 1 << n
    return Q(isqrt(2 * power * power), power)


def square(z: Point, r: Q) -> list[Point]:
    x, y = z
    return [(x-r, y-r), (x+r, y-r), (x+r, y+r), (x-r, y+r)]


def boundary(vertices: list[Point]) -> Counter[Edge]:
    result: Counter[Edge] = Counter()
    for u, v in zip(vertices, vertices[1:] + vertices[:1]):
        if u == v:
            continue
        if u < v:
            result[u, v] += 1
        else:
            result[v, u] -= 1
    return result


def strip(lo: list[Point], hi: list[Point]) -> Counter[Edge]:
    result: Counter[Edge] = Counter()
    for k in range(len(lo)):
        j = (k+1) % len(lo)
        result.update(boundary([lo[k], lo[j], hi[j]]))
        result.subtract(boundary([lo[k], hi[k], hi[j]]))
    return result


def check_grid(c: Q, r: Q) -> int:
    """Split the rectangular domain at the four boundary lines of its hole."""
    xs = [Q(1), c-r, c+r, Q(2)]
    ys = [Q(-1, 2), -r, r, Q(1, 2)]
    chain: Counter[Edge] = Counter()
    count = 0
    for i in range(3):
        for j in range(3):
            if (i, j) == (1, 1):
                continue
            a, b = xs[i], xs[i+1]
            d, e = ys[j], ys[j+1]
            chain.update(boundary([(a,d), (b,d), (b,e)]))
            chain.update(boundary([(a,d), (b,e), (a,e)]))
            count += 2
    # Outer edges must be split at grid vertices before comparison.
    outer = [(x, ys[0]) for x in xs] + [(xs[-1], y) for y in ys[1:]]
    outer += [(x, ys[-1]) for x in reversed(xs[:-1])]
    outer += [(xs[0], y) for y in reversed(ys[1:-1])]
    target = boundary(outer)
    target.subtract(boundary(square((c,Q(0)),r)))
    assert chain == target
    return count


def mul(z: Point, w: Point) -> Point:
    x,y = z
    a,b = w
    return (x*a-y*b, x*b+y*a)


def inv(z: Point) -> Point:
    x,y = z
    norm_sq = x*x+y*y
    return (x/norm_sq, -y/norm_sq)


def main() -> None:
    r = Q(1,64)
    b = 12
    c = sqrt2_name(b)
    assert Q(1,2**b) <= r/64
    assert Q(1) < c-9*r < c+9*r < Q(2)
    cells = check_grid(c,r)
    lo = square((c,Q(0)),r)
    for n in range(b, b+31):
        p = sqrt2_name(n)
        assert p*p <= 2 < (p + Q(1, 2**n))**2
        assert abs(p-c) <= r/32
        hi = square((p,Q(0)),r)
        target = boundary(lo)
        target.subtract(boundary(hi))
        assert strip(lo,hi) == target
        # Check the exact principal-part splitting at rational proxies.
        z = (Q(3,2), Q(1,8))
        z2 = mul(z,z)
        lhs = inv((z2[0]-p*p,z2[1]))
        plus = inv((z[0]-p,z[1]))
        minus = inv((z[0]+p,z[1]))
        rhs = tuple((u-v)/(2*p) for u,v in zip(plus,minus))
        assert lhs == rhs
    # Non-axis shifts exercise both dimensions and nondegenerate panels.
    for dx in (r/64, -r/80):
        for dy in (r/96, -r/72):
            hi = square((c+dx,dy),r)
            target = boundary(lo)
            target.subtract(boundary(hi))
            assert strip(lo,hi) == target
    print(f"PASS: proxy c={c}, half-side r={r}, {cells} filling triangles")
    print("PASS: 31 square-root brackets, strips, and rational principal-part identities")
    print("PASS: four two-dimensional translations")


if __name__ == "__main__":
    main()
