#!/usr/bin/env python3
"""Exact certificate for the spatial worm lower bound 3/220.

This script uses only Python's standard library.  Every calculation that
establishes the bound is integral or rational; decimals are display only.
The analytic reduction to the finitely many directions is proved in the
accompanying TeX report, not inferred from sampling.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import sqrt


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def cross(a, b):
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


VERTICES = (
    (3, 0, 0),
    (0, 3, 2),
    (-3, 0, 4),
    (0, -3, 6),
    (3, 0, 8),
)

EXPECTED_FACETS = (
    (0, 1, 2), (0, 1, 4), (0, 2, 3),
    (0, 3, 4), (1, 2, 4), (2, 3, 4),
)

EXPECTED_SQUARED_AREAS = Counter({
    Fraction(5184, 25): 1,
    Fraction(216): 2,
    Fraction(2592, 11): 6,
    Fraction(324): 1,
    Fraction(5184, 13): 2,
    Fraction(5832, 11): 2,
    Fraction(576): 1,
})


def verify():
    assert all(
        dot(sub(b, a), sub(b, a)) == 22
        for a, b in zip(VERTICES, VERTICES[1:])
    ), "The raw path must have length 4 sqrt(22)."
    scale_squared = Fraction(1, 16 * 22)

    facets = []
    normals = []
    for ids in combinations(range(len(VERTICES)), 3):
        a, b, c = (VERTICES[i] for i in ids)
        normal = cross(sub(b, a), sub(c, a))
        if dot(normal, normal) == 0:
            continue
        signs = [dot(normal, sub(v, a)) for v in VERTICES]
        if all(s >= 0 for s in signs) or all(s <= 0 for s in signs):
            assert sum(s == 0 for s in signs) == 3, "Facet must be triangular."
            facets.append(ids)
            normals.append(normal)
    assert tuple(facets) == EXPECTED_FACETS
    assert any(
        dot(normals[i], cross(normals[j], normals[k])) != 0
        for i, j, k in combinations(range(len(normals)), 3)
    ), "The projection-area function must be positive off the origin."

    values = Counter()
    minimizers = []
    target = Fraction(5184, 25)
    for i, j in combinations(range(len(normals)), 2):
        v = cross(normals[i], normals[j])
        vv = dot(v, v)
        assert vv > 0, "Every normal pair is independent in this example."
        numerator = sum(abs(dot(n, v)) for n in normals)
        area_squared = Fraction(numerator * numerator, 16 * vv)
        values[area_squared] += 1
        if area_squared == target:
            minimizers.append((i, j, v))
    assert values == EXPECTED_SQUARED_AREAS
    assert min(values) == target
    minimum_raw_area = Fraction(72, 5)
    assert minimum_raw_area**2 == target
    minimum_scaled_area = minimum_raw_area * scale_squared
    lower_bound = minimum_scaled_area / 3
    assert minimum_scaled_area == Fraction(9, 220)
    assert lower_bound == Fraction(3, 220)

    print("Exact certificate: PASS")
    print("Raw path length: 4 sqrt(22); length after scaling: 1")
    print("Scale squared:", scale_squared)
    print("Facet triples and cross-product vectors:")
    for ids, normal in zip(facets, normals):
        print(" ", ids, normal)
    print("Squared raw projection areas and multiplicities:")
    for q, count in sorted(values.items()):
        print(" ", q, count)
    print("Minimizing pairs and directions:", minimizers)
    print("Minimum raw projection area:", minimum_raw_area)
    print("Minimum unit-curve projection area:", minimum_scaled_area)
    print("Universal-cover volume lower bound:", lower_bound)
    print("Decimal lower bound (display only):", float(lower_bound))


if __name__ == "__main__":
    verify()
