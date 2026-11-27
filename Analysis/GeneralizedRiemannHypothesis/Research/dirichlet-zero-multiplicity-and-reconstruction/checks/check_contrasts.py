#!/usr/bin/env python3
"""Exact finite checks for the ramp-variance formulas. Run with Python 3.8+.

No zero table is used. These calculations check spline normalizations and
the transformation from labelled character covariances to residue classes.
They also test the finite Fourier formulas on synthetic multiplicity patterns.
"""

from fractions import Fraction as Q
from math import comb


def spline_norm(nodes, coefficients):
    """Integral of the square of the continuous piecewise-linear H_c."""
    assert len(nodes) == len(coefficients)
    assert all(a < b for a, b in zip(nodes, nodes[1:]))
    assert sum(coefficients) == sum(x * c for x, c in zip(nodes, coefficients)) == 0

    def height(x):
        return sum(c * max(x - t, 0) for t, c in zip(nodes, coefficients))

    integral = Q()
    for a, b in zip(nodes, nodes[1:]):
        left, right = height(a), height(b)
        integral += Q(b - a, 3) * (left**2 + left * right + right**2)
    return integral


def cubic_norm(nodes, coefficients):
    return sum(Q(c * d, 12) * abs(x - y)**3
               for x, c in zip(nodes, coefficients)
               for y, d in zip(nodes, coefficients))


def check_splines():
    expected = [Q(2, 3), Q(1), Q(8, 3), Q(25, 3)]
    for d, reference in enumerate(expected, start=2):
        nodes = list(range(d + 1))
        coeff = [(-1)**(d - j) * comb(d, j) for j in nodes]
        assert spline_norm(nodes, coeff) == cubic_norm(nodes, coeff) == reference
        print(f"Difference order {d}: squared spline norm = {reference}")

    nodes = [-2, 1, 3]
    coeff = [2, -5, 3]
    assert spline_norm(nodes, coeff) == cubic_norm(nodes, coeff) == 60


def check_collisions():
    # Unit group modulo 8. Its three nonidentity elements square to 1.
    # The four Fourier rows act on labelled multiplicity vectors.
    rows = [(1, 1, 1, 1), (1, 1, -1, -1), (1, -1, 1, -1), (1, -1, -1, 1)]
    n = len(rows)
    for i, a in enumerate(rows):
        for j, b in enumerate(rows):
            unit_covariance = sum(Q(x * y, n**2) for x, y in zip(a, b))
            assert unit_covariance == Q(int(i == j), n)
    print("Minimum second-difference covariance at modulus 8: (1/6) I_4")

    for m in ((0, 1, 0, 0), (2, 1, 0, 1), (2, 2, 2, 2)):
        total = sum(m)
        repeats = sum(k * (k - 1) for k in m)
        overlaps = 2 * sum(x * y for i, x in enumerate(m) for y in m[:i])
        assert total * (total - 1) == repeats + overlaps
        amplitude = sum(Q(x * y, n) for x, y in zip(rows[0], m))
        assert amplitude**2 == Q(total**2, n**2)


if __name__ == "__main__":
    check_splines()
    check_collisions()
    print("All exact checks passed.")
