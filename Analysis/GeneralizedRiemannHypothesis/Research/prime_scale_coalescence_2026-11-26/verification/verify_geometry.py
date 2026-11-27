#!/usr/bin/env python3
"""Exact diagnostics for the geometry in the coalescing-scale theorem.

All arithmetic uses fractions.Fraction. This file checks finite algebraic
identities and positivity witnesses. It neither computes zeta zeros nor
certifies the analytic theorem or the upstream RH proof.

Run: python3 verify_geometry.py
Output: geometry_checks.json beside this script, unless --output is supplied.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from math import comb
from pathlib import Path


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), F(0))


def transpose(a):
    return [list(row) for row in zip(*a)]


def matmul(a, b):
    bt = transpose(b)
    return [[dot(row, col) for col in bt] for row in a]


def determinant(a):
    b = [row[:] for row in a]
    n = len(b)
    result = F(1)
    for k in range(n):
        pivot = next((j for j in range(k, n) if b[j][k]), None)
        if pivot is None:
            return F(0)
        if pivot != k:
            b[k], b[pivot] = b[pivot], b[k]
            result = -result
        p = b[k][k]
        result *= p
        for i in range(k + 1, n):
            multiplier = b[i][k] / p
            for j in range(k + 1, n):
                b[i][j] -= multiplier * b[k][j]
    return result


def ldl(a):
    n = len(a)
    lower = [[F(i == j) for j in range(n)] for i in range(n)]
    diagonal = []
    for j in range(n):
        d = a[j][j] - sum(
            (lower[j][k] ** 2 * diagonal[k] for k in range(j)), F(0)
        )
        assert d > 0, (j, d)
        diagonal.append(d)
        for i in range(j + 1, n):
            lower[i][j] = (
                a[i][j]
                - sum(
                    (lower[i][k] * lower[j][k] * diagonal[k]
                     for k in range(j)),
                    F(0),
                )
            ) / d
    scaled = [
        [lower[i][j] * diagonal[j] for j in range(n)]
        for i in range(n)
    ]
    assert matmul(scaled, transpose(lower)) == a
    return lower, diagonal


def affine_annihilation(nodes, c):
    assert sum(c, F(0)) == 0
    assert dot(nodes, c) == 0


def cubic_bilinear(nodes, c, d):
    affine_annihilation(nodes, c)
    affine_annihilation(nodes, d)
    return sum(
        (c[i] * d[j] * abs(nodes[i] - nodes[j]) ** 3
         for i in range(len(nodes)) for j in range(len(nodes))),
        F(0),
    ) / 12


def hinge_integral(nodes, c, d):
    """Integrate the product of two piecewise-linear hinges exactly."""
    affine_annihilation(nodes, c)
    affine_annihilation(nodes, d)
    total = F(0)
    for k in range(len(nodes) - 1):
        lo, hi = nodes[k:k + 2]
        ac = sum(c[:k + 1], F(0))
        bc = -dot(c[:k + 1], nodes[:k + 1])
        ad = sum(d[:k + 1], F(0))
        bd = -dot(d[:k + 1], nodes[:k + 1])
        total += ac * ad * (hi ** 3 - lo ** 3) / 3
        total += (ac * bd + ad * bc) * (hi ** 2 - lo ** 2) / 2
        total += bc * bd * (hi - lo)
    # Both functions vanish outside [min(nodes), max(nodes)] by annihilation.
    return total


def tent_basis(nodes):
    """Columns are second divided-difference contrasts with unit hat height."""
    r = len(nodes)
    columns = []
    for k in range(r - 2):
        left = nodes[k + 1] - nodes[k]
        right = nodes[k + 2] - nodes[k + 1]
        assert left > 0 and right > 0
        c = [F(0) for _ in nodes]
        c[k] = 1 / left
        c[k + 1] = -(1 / left + 1 / right)
        c[k + 2] = 1 / right
        affine_annihilation(nodes, c)
        columns.append(c)
    return columns


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: encode(v) for k, v in value.items()}
    if isinstance(value, list):
        return [encode(v) for v in value]
    return value


def verify():
    cases = []
    pair_checks = 0
    combination_checks = 0
    for r in range(3, 9):
        # Uneven rational nodes; every gap changes with its index.
        nodes = [F(-2)]
        for j in range(1, r):
            nodes.append(nodes[-1] + F(j + 1, j + 2))
        basis = tent_basis(nodes)
        restricted = []
        for c in basis:
            row = []
            for d in basis:
                energy = cubic_bilinear(nodes, c, d)
                assert energy == hinge_integral(nodes, c, d)
                row.append(energy)
                pair_checks += 1
            restricted.append(row)
        gaps = [nodes[j + 1] - nodes[j] for j in range(r - 1)]
        expected = []
        for i in range(r - 2):
            row = []
            for j in range(r - 2):
                if i == j:
                    row.append((gaps[i] + gaps[i + 1]) / 3)
                elif abs(i - j) == 1:
                    row.append(gaps[max(i, j)] / 6)
                else:
                    row.append(F(0))
            expected.append(row)
        assert restricted == expected
        leading_minors = [
            determinant([row[:k] for row in restricted[:k]])
            for k in range(1, r - 1)
        ]
        assert all(d > 0 for d in leading_minors)
        lower, diagonal = ldl(restricted)
        for test in range(1, 8):
            coefficients = [
                F((-1) ** (test + j) * (test + 2 * j + 1), j + 2)
                for j in range(r - 2)
            ]
            c = [
                sum((coefficients[j] * basis[j][i]
                     for j in range(r - 2)), F(0))
                for i in range(r)
            ]
            energy = cubic_bilinear(nodes, c, c)
            assert energy == hinge_integral(nodes, c, c)
            assert energy > 0
            combination_checks += 1
        cases.append({
            "node_count": r,
            "nodes": nodes,
            "basis_columns": basis,
            "restricted_cubic_form": restricted,
            "leading_principal_minors": leading_minors,
            "ldl_lower": lower,
            "ldl_diagonal": diagonal,
            "tridiagonal_hat_mass_identity": True,
        })

    differences = []
    for degree in range(2, 11):
        nodes = [F(j) for j in range(degree + 1)]
        c = [F((-1) ** j * comb(degree, j))
             for j in range(degree + 1)]
        for power in range(degree):
            assert sum((c[j] * nodes[j] ** power
                        for j in range(degree + 1)), F(0)) == 0
        energy = cubic_bilinear(nodes, c, c)
        assert energy == hinge_integral(nodes, c, c)
        assert energy > 0
        norm2 = dot(c, c)
        assert norm2 == comb(2 * degree, degree)
        differences.append({
            "difference_order": degree,
            "coefficients": c,
            "cubic_energy": energy,
            "squared_euclidean_norm": norm2,
            "unit_contrast_cubic_energy": energy / norm2,
            "montgomery_variance_lower_constant": energy,
            "montgomery_variance_upper_constant": F(4, 3) * energy,
            "montgomery_unit_lower_constant": energy / norm2,
            "montgomery_unit_upper_constant": F(4, 3) * energy / norm2,
        })

    nodes = [F(-1), F(0), F(1)]
    c = [F(1), F(-2), F(1)]
    second_energy = cubic_bilinear(nodes, c, c)
    unit_energy = second_energy / dot(c, c)
    midpoint_residual = [F(-1, 2), F(1), F(-1, 2)]
    midpoint_energy = cubic_bilinear(nodes, midpoint_residual, midpoint_residual)
    assert second_energy == F(2, 3)
    assert unit_energy == F(1, 9)
    assert midpoint_energy == F(1, 6)

    return {
        "status": "PASS",
        "arithmetic": "Exact fractions.Fraction throughout",
        "scope": "Finite geometry diagnostics; no zeta-zero computation or analytic proof certification",
        "identity": "c^T (|u_i-u_j|^3) d / 12 = integral (sum c_i(t-u_i)_+)(sum d_i(t-u_i)_+) dt",
        "basis_pair_identities_checked": pair_checks,
        "nonzero_linear_combinations_checked": combination_checks,
        "rational_node_cases": cases,
        "finite_difference_cases": differences,
        "three_symmetric_nodes": {
            "nodes": nodes,
            "second_difference_cubic_energy": second_energy,
            "unit_eigenvector_cubic_constant": unit_energy,
            "midpoint_prediction_cubic_constant": midpoint_energy,
            "smallest_eigenvalue_lower_constant": unit_energy,
            "smallest_eigenvalue_upper_constant": F(4, 3) * unit_energy,
            "midpoint_prediction_lower_constant": midpoint_energy,
            "midpoint_prediction_upper_constant": F(4, 3) * midpoint_energy,
        },
        "interpretation": "Cubic constants give the lower analytic bracket; their multiples by 4/3 give the upper Montgomery bracket. The analytic theorem, not this finite script, justifies that bracket. Exact limits require an additional squared-multiplicity density hypothesis.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("geometry_checks.json"))
    args = parser.parse_args()
    result = verify()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(encode(result), indent=2) + "\n", encoding="utf-8")
    print("PASS: exact hinge/cubic identities, positivity, and finite differences")
    print(f"Basis-pair checks: {result['basis_pair_identities_checked']}")
    print(f"Nonzero combinations: {result['nonzero_linear_combinations_checked']}")
    for row in result["finite_difference_cases"]:
        print(f"Difference order {row['difference_order']}: "
              f"energy {row['cubic_energy']}, "
              f"unit energy {row['unit_contrast_cubic_energy']}")
    print("Symmetric three-node constants: 2/3, 1/9, 1/6")
    print(f"Written: {args.output}")


if __name__ == "__main__":
    main()
