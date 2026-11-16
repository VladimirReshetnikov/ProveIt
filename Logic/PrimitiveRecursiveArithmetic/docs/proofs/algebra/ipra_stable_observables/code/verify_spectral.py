"""Targeted exact checks for the rational spectral construction.

These finite computations check implementation behavior and algebraic
edge cases.  They are not a proof of the uniform arithmetic theorem.
"""

import json
from fractions import Fraction as F

from spectral import (matrix, identity, transpose, matmul, frob_sq, offdiag_sq,
                      givens, conjugate, pivot_rotation, jacobi,
                      jacobi_grid, verify_certificate, serialize)


def run_checks():
    pivot_cases = 0
    branch_counts = {"large_difference": 0, "small_difference": 0}
    for h in range(-12, 13):
        for b in range(-12, 13):
            if b == 0:
                continue
            c, s, branch = pivot_rotation(h, b)
            assert c * c + s * s == 1
            new_b = (c * c - s * s) * b - c * s * h
            assert 2 * new_b * new_b <= b * b
            if branch == "large_difference":
                assert 4 * new_b * new_b <= b * b
            branch_counts[branch] += 1
            pivot_cases += 1

    energy_cases = 0
    base = matrix([[3, 2, -1], [2, -2, 4], [-1, 4, 1]])
    for i, j in [(0, 1), (0, 2), (1, 2)]:
        b, h = base[i][j], base[i][i] - base[j][j]
        c, s, _ = pivot_rotation(h, b)
        g = givens(3, i, j, c, s)
        out = conjugate(base, g)
        new_b = (c * c - s * s) * b - c * s * h
        assert out[i][j] == new_b
        assert matmul(transpose(g), g) == identity(3)
        assert frob_sq(out) == frob_sq(base)
        assert offdiag_sq(out) == offdiag_sq(base) - 2*b*b + 2*new_b*new_b
        assert offdiag_sq(out) <= offdiag_sq(base) - b*b
        energy_cases += 1

    examples = [
        ([], F(1, 4)),
        ([[7]], F(1, 4)),
        ([[2, 0], [0, 2]], F(1, 100)),
        ([[2, 1], [1, 3]], F(1, 4)),
        ([[0, 1], [1, 0]], F(1, 4)),
        ([[100, 1], [1, -100]], F(1, 4)),
        ([[2, 1, 0], [1, 3, 0], [0, 0, -1]], F(1, 4)),
        ([[1, 0, 0], [0, 1, 0], [0, 0, 1]], F(1, 100)),
        ([[1, 1, 1], [1, 1, 1], [1, 1, 1]], F(3)),
    ]
    checked = []
    for rows, eps in examples:
        a = matrix(rows)
        result = jacobi(a, eps)
        assert verify_certificate(a, result)
        checked.append({"n": len(a), "epsilon": eps,
                        "steps": result["steps"], "fuel": result["fuel"],
                        "residual_bound_verified": result["residual_sq"] <= eps ** 2,
                        "residual_numerator_bits": result["residual_sq"].numerator.bit_length(),
                        "residual_denominator_bits": result["residual_sq"].denominator.bit_length()})

    invalid_inputs = 0
    for a, eps in [([[1, 2], [0, 1]], 1), ([[1]], 0), ([[1, 2]], 1)]:
        try:
            jacobi(a, eps)
        except ValueError:
            invalid_inputs += 1
        else:
            raise AssertionError("Invalid input was accepted")

    grid_examples = [
        ([[3, 2, -1], [2, -2, 4], [-1, 4, 1]], F(1, 16)),
        ([[1, 1, 1], [1, 1, 1], [1, 1, 1]], F(1, 32)),
        ([[4, 1, 0, 2], [1, 3, -1, 0], [0, -1, 2, 1], [2, 0, 1, 5]], F(1, 16)),
        ([[2, 0, 0, 0], [0, 2, 0, 0], [0, 0, -1, 1], [0, 0, 1, -1]], F(1, 64)),
    ]
    grid_checked = []
    for rows, eps in grid_examples:
        a = matrix(rows)
        result = jacobi_grid(a, eps)
        assert verify_certificate(a, result)
        grid_checked.append({"n": len(a), "epsilon": eps,
                             "steps": result["steps"], "fuel": result["fuel"],
                             "grid": result["grid"], "residual_bound_verified": True,
                             "largest_Q_denominator_bits": max(
                                 (x.denominator.bit_length() for row in result["Q"] for x in row),
                                 default=0)})

    return {"status": "passed", "pivot_cases": pivot_cases,
            "pivot_branch_counts": branch_counts, "energy_cases": energy_cases,
            "full_certificate_cases": checked, "invalid_input_rejections": invalid_inputs,
            "grid_certificate_cases": grid_checked,
            "qualification": "Finite exact arithmetic checks; not a uniform iPRA proof."}


if __name__ == "__main__":
    print(json.dumps(serialize(run_checks()), indent=2))
