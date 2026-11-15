#!/usr/bin/env python3
"""Exact constructive projective-geometry examples and finite kernel checks.

Uses Python integers only; no floating-point operations or external packages.
The exhaustive test checks the executable kernel construction on a finite
cube. It is a regression check, not a proof of the universal theorem.

Run: python3 exact_geometry.py
"""
from collections import Counter
from functools import reduce
from itertools import product
from math import gcd
import json


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1],
            u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0])


def det(u, v, w):
    return dot(u, cross(v, w))


def nonzero(u):
    return any(x != 0 for x in u)


def canonical(u):
    """Display a nonzero integer vector with gcd 1 and first entry positive."""
    if not nonzero(u):
        raise ValueError("A zero vector has no projective representative")
    divisor = reduce(gcd, u, 0)
    first = next(x for x in u if x)
    divisor *= 1 if first > 0 else -1
    return tuple(x // divisor for x in u)


def kernel(u, v, w):
    """Return (h, branch) with h nonzero and orthogonal to u,v,w.

    Preconditions: u != 0 and det(u,v,w) == 0.  The construction uses only
    integer arithmetic and a fixed number of decidable equality tests.
    """
    if not nonzero(u) or det(u, v, w) != 0:
        raise ValueError("kernel requires u != 0 and det(u,v,w) == 0")
    uv = cross(u, v)
    if nonzero(uv):
        return uv, "cross_u_v"
    uw = cross(u, w)
    if nonzero(uw):
        return uw, "cross_u_w"
    if u[0] != 0 or u[1] != 0:
        return (-u[1], u[0], 0), "coordinate_01"
    return (u[2], 0, 0), "coordinate_2"


def verify_kernel(u, v, w):
    h, branch = kernel(u, v, w)
    if not nonzero(h) or any(dot(h, p) != 0 for p in (u, v, w)):
        raise AssertionError(("kernel failure", u, v, w, h, branch))
    return h, branch


def desargues_meets(first, second):
    a, b, c = first
    A, B, C = second
    return (cross(cross(a, b), cross(A, B)),
            cross(cross(b, c), cross(B, C)),
            cross(cross(c, a), cross(C, A)))


def desargues_examples():
    first = ((1, 0, 1), (0, 1, 1), (-1, -1, 1))
    second = ((1, 0, 2), (0, 1, 3), (-1, -1, 4))
    center = (0, 0, 1)
    joins = tuple(cross(a, A) for a, A in zip(first, second))
    meets = desargues_meets(first, second)
    if not all(nonzero(v) for v in joins + meets):
        raise AssertionError("Desargues example contains an undefined object")
    if any(dot(center, line) for line in joins):
        raise AssertionError("Desargues center incidence failed")
    assert (det(*first), det(*second)) == (3, 9)
    assert meets == ((2, -1, 1), (2, 5, 1), (-4, -1, -2))
    axis, branch = verify_kernel(*meets)
    recovered_center, _ = verify_kernel(*joins)
    assert canonical(axis) == (1, 0, -2)
    assert canonical(recovered_center) == center
    example = {
        "first_triangle": first, "second_triangle": second,
        "triangle_determinants": [det(*first), det(*second)],
        "joining_lines": joins, "center": center,
        "side_meets": meets, "axis": canonical(axis),
        "axis_construction_branch": branch,
        "recovered_center": canonical(recovered_center),
        "all_incidences_checked": True}

    first_bad = ((1, 0, 0), (0, 1, 0), (1, 1, 0))
    second_bad = ((0, 0, 1), (1, 0, 1), (0, 1, 1))
    joins_bad = tuple(cross(a, A) for a, A in zip(first_bad, second_bad))
    meets_bad = desargues_meets(first_bad, second_bad)
    assert all(nonzero(v) for v in joins_bad + meets_bad)
    assert (det(*first_bad), det(*second_bad), det(*joins_bad)) == (0, 1, 2)
    axis_bad, _ = verify_kernel(*meets_bad)
    assert canonical(axis_bad) == (0, 0, 1)
    counterexample = {
        "description": "Dropping triangle nondegeneracy breaks the converse",
        "first_triangle": first_bad, "second_triangle": second_bad,
        "triangle_determinants": [det(*first_bad), det(*second_bad)],
        "joining_lines": joins_bad, "joining_lines_determinant": det(*joins_bad),
        "side_meets": meets_bad, "axis": canonical(axis_bad),
        "all_auxiliary_vectors_nonzero": True,
        "nonconcurrency_certificate": "Joining-line determinant is the nonzero integer 2"}
    return example, counterexample


def quadratic_value(q, p):
    x, y, z = p
    monomials = (x * x, y * y, z * z, x * y, x * z, y * z)
    return sum(c * m for c, m in zip(q, monomials))


def pascal_meets(points):
    a, b, c, d, e, f = points
    return (cross(cross(a, b), cross(d, e)),
            cross(cross(b, c), cross(e, f)),
            cross(cross(c, d), cross(f, a)))


def pascal_example(name, points, conic, expected_axis):
    if not all(nonzero(p) for p in points) or not nonzero(conic):
        raise AssertionError("Pascal example has invalid points or conic")
    assert all(quadratic_value(conic, p) == 0 for p in points)
    sides = tuple(cross(points[i], points[(i + 1) % 6]) for i in range(6))
    meets = pascal_meets(points)
    assert all(nonzero(v) for v in sides + meets)
    assert det(*meets) == 0
    axis, branch = verify_kernel(*meets)
    assert canonical(axis) == expected_axis
    opposite_sides = ((0, 3), (1, 4), (2, 5))
    for meeting, (i, j) in zip(meets, opposite_sides):
        assert dot(sides[i], meeting) == dot(sides[j], meeting) == 0
    return {
        "name": name, "vertices": points,
        "conic_coefficients_xx_yy_zz_xy_xz_yz": conic,
        "side_meets": meets, "axis": canonical(axis),
        "axis_construction_branch": branch,
        "points_on_conic_checked": True,
        "side_and_axis_incidences_checked": True,
        "all_auxiliary_vectors_nonzero": True}


def exhaustive_kernel_check():
    cube = tuple(product((-1, 0, 1), repeat=3))
    tested = 0
    discarded = 0
    branches = Counter()
    for u in cube:
        if not nonzero(u):
            continue
        for v in cube:
            for w in cube:
                if det(u, v, w) != 0:
                    discarded += 1
                    continue
                _, branch = verify_kernel(u, v, w)
                tested += 1
                branches[branch] += 1
    assert set(branches) == {"cross_u_v", "cross_u_w", "coordinate_01", "coordinate_2"}
    assert tested + discarded == 26 * 27 * 27
    return {
        "domain": "u != 0, and u,v,w in {-1,0,1}^3",
        "candidate_triples": tested + discarded,
        "determinant_zero_triples_checked": tested,
        "nonzero_determinant_triples_excluded": discarded,
        "branch_counts": dict(sorted(branches.items())),
        "all_four_branches_exercised": True,
        "every_output_nonzero_and_orthogonal": True,
        "limitation": "Finite execution check, not the universal mathematical proof"}


def main():
    example, counterexample = desargues_examples()
    parabola = pascal_example(
        "Six parameters t=0,1,2,3,4,5 on xz-y^2=0",
        tuple((t * t, t, 1) for t in range(6)),
        (0, -1, 0, 0, 1, 0), (1, -5, 8))
    degenerate = pascal_example(
        "Alternating vertices on the degenerate conic xy=0",
        ((1, 0, 1), (0, 1, 1), (2, 0, 1), (0, 2, 1), (3, 0, 1), (0, 3, 1)),
        (0, 0, 0, 1, 0, 0), (5, 7, -13))
    print(json.dumps({
        "arithmetic": "Exact unbounded Python integers; standard library only",
        "exhaustive_kernel_test": exhaustive_kernel_check(),
        "desargues_example": example,
        "desargues_converse_counterexample": counterexample,
        "pascal_examples": [parabola, degenerate],
        "status": "all checks passed"}, indent=2))


if __name__ == "__main__":
    main()
