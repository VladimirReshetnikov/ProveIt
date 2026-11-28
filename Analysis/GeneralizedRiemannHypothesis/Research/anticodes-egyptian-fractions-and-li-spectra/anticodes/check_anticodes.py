"""Exact checks of model sizes and geometry. Run with Python 3 (standard library)."""

from itertools import combinations, combinations_with_replacement
from math import comb, factorial
from fractions import Fraction


def l1_ball(axes, radius):
    """All integer vectors on the given axes with l1 norm at most radius."""
    if axes == 0:
        yield ()
        return
    for first in range(-radius, radius + 1):
        for rest in l1_ball(axes - 1, radius - abs(first)):
            yield (first,) + rest


def distance(x, y):
    return sum(abs(a - b) for a, b in zip(x, y))


def model_by_points(N, D):
    P, Q = (D + 1) // 2, D // 2
    h = (1,) * (P + 1) + (-1,) * (Q + 1) + (0,) * (N - D - 2)
    assert len(h) == N
    keep = {z for z in l1_ball(N, D)
            if sum(z) == P - Q and distance(z, h) <= 2 * D}
    return keep | {h}


def signed_count(N, p, q, positive_only=0, negative_only=0):
    """Coefficient of the product of the single-coordinate generating functions."""
    table = {(0, 0): 1}
    for axis in range(N):
        can_be_negative = axis >= positive_only
        can_be_positive = axis >= positive_only + negative_only or not can_be_negative
        updated = {}
        for (i, j), count in table.items():
            entries = [(i, j)]
            if can_be_positive:
                entries.extend((i + step, j) for step in range(1, p - i + 1))
            if can_be_negative:
                entries.extend((i, j + step) for step in range(1, q - j + 1))
            for key in entries:
                updated[key] = updated.get(key, 0) + count
        table = updated
    return table.get((p, q), 0)


def model_formula(N, D):
    P, Q = (D + 1) // 2, D // 2
    total = sum(signed_count(N, P - j, Q - j) for j in range(Q + 1))
    removed = signed_count(N, P, Q, positive_only=Q + 1, negative_only=P + 1)
    return 1 + total - removed


def tetrahedron(N):
    result = {tuple(int(a == i) for a in range(N)) for i in range(N)}
    for i, j in combinations(range(3), 2):
        for k in range(N):
            if k in (i, j):
                continue
            result.add(tuple(int(a == i) + int(a == j) - int(a == k)
                             for a in range(N)))
    return result


def check_geometry(points, D):
    first = next(iter(points))
    assert all(distance(x, y) <= 2 * D for x, y in combinations(points, 2))
    for offset in l1_ball(len(first), D):
        center = tuple(a + b for a, b in zip(first, offset))
        if all(distance(point, center) <= D for point in points):
            raise AssertionError(f"radius-{D} section centered at {center}")


def main():
    for D in range(2, 7):
        N = D + 2
        points = model_by_points(N, D)
        assert len(points) == model_formula(N, D)
        if D <= 4:
            check_geometry(points, D)
        print(f"D={D}, N={N}, enumerated model size {len(points)}")
    for N in range(5, 81):
        assert model_formula(N, 2) == 4 * N - 6
        assert model_formula(N, 3) == 4 * N ** 2 - 15 * N + 22
        assert len(tetrahedron(N)) == 4 * N - 6
    check_geometry(tetrahedron(6), 2)
    print("Diameters 2 and 3: polynomial counts checked at N=5,...,80.")
    for D in range(2, 11):
        r, N = D - 1, D + 3
        differences = [model_formula(N + k, D) for k in range(r + 2)]
        for _ in range(r):
            differences = [b - a for a, b in zip(differences, differences[1:])]
        P, Q = (D + 1) // 2, D // 2
        coefficient = Fraction(P * (P + 1) + Q * (Q + 1), factorial(P) * factorial(Q))
        assert differences == [factorial(r) * coefficient] * 2
    print("Leading coefficients: exact finite differences checked for D=2,...,10.")
    print("Explicit models satisfy the tested diameter and integer-center constraints.")
    # Directly enumerate nonnegative multiset sections at modest parameters.
    for N in range(3, 7):
        displacements = list(l1_ball(N, 3))
        for K in range(3, 8):
            best = 0
            for orientation in (-3, -1, 1, 3):
                total = K - orientation
                eligible = [z for z in displacements if sum(z) == orientation]
                for center in combinations_with_replacement(range(total + 1), N):
                    if sum(center) != total:
                        continue
                    count = sum(all(a + b >= 0 for a, b in zip(center, z))
                                for z in eligible)
                    best = max(best, count)
            H = N + min(N, K - 1) * comb(N, 2)
            assert best == max(comb(N + 2, 3), H)
    for N in range(4, 62):
        for K in range(3, 2 * N + 2):
            reverse = max(v + (N - 2) * comb(v, 2) + (N - 1) * min(v, K + 1 - v)
                          for v in range(1, min(N, K + 1) + 1))
            H = N + min(N, K - 1) * comb(N, 2)
            assert reverse <= H
            assert (comb(N + 2, 3) < H) == (3 * K > N + 7)
    print("Multiset sections enumerated at N=3..6 and K=3..7; orientation and crossover checks passed.")



if __name__ == "__main__":
    main()
