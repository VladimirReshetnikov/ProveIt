#!/usr/bin/env python3
"""Exact finite sampling and octahedral degree computations. Python 3.10+."""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
from math import prod
from typing import Callable, Iterator, Sequence

Point = tuple[int, ...]               # numerator on the denominator-D l1 sphere
Vector = tuple[Fraction, ...]
Triangle = tuple[int, tuple[Point, Point, Point]]


def signed_grid(dimension: int, denominator: int) -> Iterator[Point]:
    """Yield each integer vector of l1 norm D once, including facet boundaries."""
    if dimension < 1 or denominator < 1:
        raise ValueError("dimension and denominator must be positive")

    def visit(slots: int, budget: int, prefix: Point) -> Iterator[Point]:
        if slots == 1:
            yield prefix + (budget,)
            if budget:
                yield prefix + (-budget,)
            return
        for entry in range(-budget, budget + 1):
            yield from visit(slots - 1, budget - abs(entry), prefix + (entry,))

    yield from visit(dimension, denominator, ())


def projection_field(b: Sequence[int], z: Point) -> Vector:
    """Project b to the plane perpendicular to z. Radial rescaling has no effect."""
    if len(b) != len(z):
        raise ValueError("the field and point must have the same dimension")
    square = sum(v * v for v in z)
    linear = sum(u * v for u, v in zip(b, z))
    return tuple(Fraction(u * square - linear * v, square) for u, v in zip(b, z))


def witness(dimension: int, denominator: int, tol: Fraction,
            field: Callable[[Point], Vector]) -> tuple[Point, Vector] | None:
    """Test the exact l1 norm in a single bounded traversal of the grid."""
    for z in signed_grid(dimension, denominator):
        y = field(z)
        if sum(abs(v) for v in y) <= tol:
            return z, y
    return None


def order_sign(seq: Sequence) -> int:
    inversions = sum(a > b for i, a in enumerate(seq) for b in seq[i + 1:])
    return -1 if inversions % 2 else 1


def octahedral_triangles(denominator: int) -> list[Triangle]:
    """Triangulate the eight facets of S² into 8D² coherent ordered triangles."""
    triangles = []
    for signs in product((1, -1), repeat=3):
        def vertex(i: int, j: int) -> Point:
            return tuple(s * v for s, v in zip(signs, (denominator-i-j, i, j)))

        def insert(points: tuple[Point, Point, Point]) -> None:
            # A global vertex order fixes the same prism diagonal on both
            # triangles incident to an edge. Absorb the reordering in the weight.
            triangles.append((prod(signs) * order_sign(points), tuple(sorted(points))))

        for i in range(denominator):
            for j in range(denominator - i):
                insert((vertex(i, j), vertex(i + 1, j), vertex(i, j + 1)))
                if i + j + 1 < denominator:
                    insert((vertex(i + 1, j), vertex(i + 1, j + 1), vertex(i, j + 1)))
    return triangles


def boundary(triangles: list[Triangle]) -> dict:
    count: Counter = Counter()
    for w, (a, b, c) in triangles:
        count[b, c] += w
        count[a, c] -= w
        count[a, b] += w
    return {edge: w for edge, w in count.items() if w}


def label(v: Sequence) -> int:
    """Signed 1-based maximizing axis; ties go to the lowest axis."""
    i = max(range(len(v)), key=lambda j: abs(v[j]))
    if not v[i]:
        raise ValueError("the zero vector has no signed maximizing coordinate")
    return i + 1 if v[i] > 0 else -(i + 1)


def degree(triangles: list[Triangle], labels: dict[Point, int]) -> int:
    """Coefficient of the all-positive target facet."""
    coefficient = 0
    for w, points in triangles:
        image = tuple(labels[p] for p in points)
        if sorted(image) == [1, 2, 3]:
            coefficient += w * order_sign(image)
    return coefficient


def first_bad_prism(triangles: list[Triangle], old: dict, new: dict):
    for _, (a, b, c) in triangles:
        lower = [old[a], old[b], old[c]]
        upper = [new[a], new[b], new[c]]
        for h in range(3):
            tet = lower[:h + 1] + upper[h:]
            if any(-u in tet for u in tet):
                return (a, b, c), h, tuple(tet)
    return None


def degree_demo(b: Sequence[int], denominator: int, steps: int):
    """Run the two legs z/D -> normalized projection -> -z/D on a finite cylinder."""
    if len(b) != 3 or denominator < 1 or steps < 1:
        raise ValueError("degree_demo needs three coordinates, D > 0 and steps > 0")
    triangles = octahedral_triangles(denominator)
    assert not boundary(triangles)
    pts = list(signed_grid(3, denominator))
    values = {}
    for z in pts:
        y = projection_field(b, z)
        magnitude = sum(map(abs, y))
        if magnitude == 0:
            return len(pts), len(triangles), [], z
        values[z] = tuple(v / magnitude for v in y)
    old = {z: label(z) for z in pts}
    last = degree(triangles, old)
    assert last == 1
    jumps = []
    for t in range(1, 2 * steps + 1):
        # Positive common scale steps*D is omitted from each vector.
        alpha = steps - t
        beta = min(t, 2 * steps - t) * denominator
        new = {z: label([alpha * u + beta * v for u, v in zip(z, values[z])]) for z in pts}
        current = degree(triangles, new)
        if current != last:
            collision = first_bad_prism(triangles, old, new)
            assert collision is not None
            jumps.append((t-1, t, last, current, collision))
        old, last = new, current
    assert last == -1
    return len(pts), len(triangles), jumps, None


def self_test() -> None:
    for n in (1, 2, 3, 4):
        for D in (1, 2, 3):
            pts = list(signed_grid(n, D))
            brute = {z for z in product(range(-D, D+1), repeat=n) if sum(map(abs, z)) == D}
            assert len(pts) == len(set(pts)) and set(pts) == brute
    b = (1, 2, 4)
    for D in (1, 2, 3, 5, 8):
        tris = octahedral_triangles(D)
        pts = list(signed_grid(3, D))
        assert len(tris) == 8 * D * D and len(pts) == 4 * D * D + 2
        assert not boundary(tris)
        plus = {z: label(z) for z in pts}
        minus = {z: -plus[z] for z in pts}
        assert (degree(tris, plus), degree(tris, minus)) == (1, -1)
        for z in pts:
            y = projection_field(b, z)
            assert sum(u*v for u, v in zip(z, y)) == 0
    for D, tol in ((16, Fraction(2, 5)), (64, Fraction(1, 8))):
        result = witness(3, D, tol, lambda z: projection_field(b, z))
        assert result and 0 < sum(map(abs, result[1])) <= tol
    _, _, jumps, zero = degree_demo(b, 8, 4)
    assert zero is None
    assert degree_demo(b, 7, 4)[3] == (-1, -2, -4)
    assert jumps and sum(j[3]-j[2] for j in jumps) == -2
    print("All exact-arithmetic checks passed.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--denominator", type=int, default=16)
    parser.add_argument("--tol", type=Fraction, default=Fraction(2, 5))
    parser.add_argument("--axis", type=int, nargs="+", default=(1, 2, 4))
    parser.add_argument("--degree-demo", action="store_true")
    parser.add_argument("--steps", type=int, default=8)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if args.tol < 0:
        parser.error("tolerance must be nonnegative")
    ans = witness(len(args.axis), args.denominator, args.tol,
                  lambda z: projection_field(args.axis, z))
    if ans is None:
        print("No witness at this denominator and tolerance.")
    else:
        z, y = ans
        print("l1 direction:", z, "/", args.denominator)
        print("field:", tuple(map(str, y)))
        print("l1 norm:", sum(map(abs, y)), "<=", args.tol)
    if args.degree_demo:
        try:
            points, tris, jumps, zero = degree_demo(args.axis, args.denominator, args.steps)
        except ValueError as exc:
            parser.error(str(exc))
        if zero is not None:
            print(f"Exact field zero at {zero}/{args.denominator}; normalization stops here.")
            return
        print(f"{points} vertices and {tris} triangles. Endpoint coefficients: +1, -1.")
        for t, u, a, b, collision in jumps:
            tri, tetra, labels = collision
            print(f"Layers {t}->{u}: {a}->{b}. Triangle {tri}, prism simplex {tetra}, labels {labels}.")


if __name__ == "__main__":
    main()
