#!/usr/bin/env python3
"""Exact finite diagnostics for the polynomial partition note.

The mathematical proofs are in gowers_interpolation.tex. These diagnostics verify the
determinants, Newton lifting bookkeeping, and one obstruction witness without
using floating-point inequalities. Finite grids are not treated as Haar measure.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import comb, prod
from pathlib import Path
import json
import random


def determinant(matrix: list[list[int]]) -> int:
    """Fraction-free elimination with exact row pivoting."""
    work = [row[:] for row in matrix]
    n = len(work)
    previous, sign = 1, 1
    for k in range(n - 1):
        if work[k][k] == 0:
            pivot = next(i for i in range(k + 1, n) if work[i][k])
            work[k], work[pivot] = work[pivot], work[k]
            sign *= -1
        pivot = work[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = work[i][j] * pivot - work[i][k] * work[k][j]
                assert numerator % previous == 0
                work[i][j] = numerator // previous
            work[i][k] = 0
        previous = pivot
    return sign * work[-1][-1]


def difference(values: list[int]) -> list[int]:
    return [b - a for a, b in zip(values, values[1:])]


def newton_coefficients(values: list[int], degree: int) -> list[int]:
    coefficients = [values[0]]
    for _ in range(degree):
        values = difference(values)
        coefficients.append(values[0])
    return coefficients


def centered(value: int, modulus: int) -> int:
    residue = value % modulus
    return residue if 2 * residue < modulus else residue - modulus


def arc_diameter_numerator(values: list[int], modulus: int) -> int:
    residues = sorted(set(value % modulus for value in values))
    if len(residues) <= 1:
        return 0
    gaps = [b - a for a, b in zip(residues, residues[1:])]
    gaps.append(modulus + residues[0] - residues[-1])
    return modulus - max(gaps)


def verify_determinants() -> dict:
    cases = []
    for degree in range(1, 9):
        for spacing in (1, 2, 3, 5, 8):
            matrix = [
                [comb(i * spacing, j) if i * spacing >= j else 0
                 for j in range(1, degree + 1)]
                for i in range(1, degree + 1)
            ]
            observed = determinant(matrix)
            expected = spacing ** (degree * (degree + 1) // 2)
            assert observed == expected
            cases.append({"degree": degree, "spacing": spacing,
                          "determinant": observed})
    return {"passed": len(cases), "cases": cases}


def verify_lifts() -> dict:
    """Exhaustively test all quadratic phases on two finite grids."""
    modulus, degree, length = 101, 2, 5
    epsilon = Fraction(1, 9)  # Strictly less than 2**(-degree-1).
    results = []
    for spacing in (1, 7):
        beta_counts: dict[tuple[int, ...], int] = {}
        lift_count = arc_count = 0
        first_nonconstant = None
        for coefficients in product(range(modulus), repeat=degree):
            raw = [sum(coefficients[j - 1] * (spacing * t) ** j
                       for j in range(1, degree + 1))
                   for t in range(length)]
            beta = tuple(c % modulus for c in
                         newton_coefficients(raw, degree)[1:])
            beta_counts[beta] = beta_counts.get(beta, 0) + 1
            y = [centered(value, modulus) for value in raw]
            if not all(Fraction(abs(value), modulus) <= epsilon for value in y):
                continue
            lift_count += 1
            c = newton_coefficients(y, degree)
            assert c[0] == 0
            assert all(2 * abs(value) < modulus for value in c[1:])
            assert tuple(value % modulus for value in c[1:]) == beta
            assert all(y[t] == sum(c[j] * comb(t, j)
                                   for j in range(min(t, degree) + 1))
                       for t in range(length))
            integers = [(raw[t] - y[t]) // modulus for t in range(length)]
            assert all(raw[t] - y[t] == modulus * integers[t]
                       for t in range(length))
            for values in (y, integers):
                for _ in range(degree + 1):
                    values = difference(values)
                assert all(value == 0 for value in values)
            if Fraction(arc_diameter_numerator(raw, modulus), modulus) <= epsilon:
                arc_count += 1
            if first_nonconstant is None and any(c[1:]):
                first_nonconstant = {
                    "coefficients_numerators": list(coefficients),
                    "centered_value_numerators": y,
                    "newton_coefficient_numerators": c,
                    "integer_lift": integers,
                }
        # Since 101 is coprime to 2*h^3, the finite transform is bijective.
        assert len(beta_counts) == modulus ** degree
        assert set(beta_counts.values()) == {1}
        results.append({"spacing": spacing, "coefficient_tuples": modulus ** degree,
                        "centered_events": lift_count, "arc_events": arc_count,
                        "finite_newton_map_bijective": True,
                        "example": first_nonconstant})
    assert results[0]["centered_events"] == results[1]["centered_events"]
    assert results[0]["arc_events"] == results[1]["arc_events"]
    return {"modulus": modulus, "degree": degree, "length": length,
            "epsilon": str(epsilon), "results": results,
            "measure_note": "These finite grids check lifting and uniformity only; "
                            "no continuous volume bound is asserted for an atomic grid."}


def obstruction_witness() -> dict:
    rng = random.Random(20261006)
    modulus, ambient_length, target_length = 1009, 80, 8
    epsilon = Fraction(1, 9)
    attempts = 0
    while True:
        attempts += 1
        coefficients = (rng.randrange(modulus), rng.randrange(1, modulus))
        progressions = []
        for spacing in range(1, (ambient_length - 1) // (target_length - 1) + 1):
            values = [(coefficients[0] * spacing * t
                       + coefficients[1] * (spacing * t) ** 2) % modulus
                      for t in range(target_length)]
            diameter = Fraction(arc_diameter_numerator(values, modulus), modulus)
            progressions.append({"spacing": spacing, "values": values,
                                 "arc_diameter": str(diameter)})
        minimum = min(Fraction(row["arc_diameter"]) for row in progressions)
        if minimum > epsilon:
            break
        assert attempts < 100
    return {"seed": 20261006, "attempts": attempts, "modulus": modulus,
            "ambient_length": ambient_length, "minimum_cell_length": target_length,
            "epsilon": str(epsilon), "coefficients_numerators": list(coefficients),
            "minimum_diameter_over_all_candidate_zero_cells": str(minimum),
            "progressions": progressions,
            "conclusion": "No partition of [0,80) into APs of at least 8 points "
                          "has quadratic phase arc diameter at most 1/9 on every cell."}


def quadratic_table() -> dict:
    rows = []
    for q in (1, 2, 4, 8, 16):
        F = (q + 1) * (44 * q + 1)
        G = q * (44 * q + 23)
        B = F + G
        assert B == 88 * q * q + 68 * q + 1
        rows.append({"q": q, "F": F, "G": G, "equal_scale_denominator": B,
                     "target_theta_lau_denominator": 2 * B,
                     "target_theta_gowers_denominator": 2 * 2048 ** q,
                     "necessary_equal_scale_denominator": 5 * q + 1})
    return {"input": "Lau arXiv:2407.01611v1, weakened to C_2=22; "
                      "numerical exponents have unspecified finite thresholds.",
            "endpoint_note": "All sufficient exponents are strict upper limits, "
                             "not attained endpoint claims.", "rows": rows}


def main() -> None:
    output = {"determinants": verify_determinants(), "lifting": verify_lifts(),
              "obstruction_witness": obstruction_witness(),
              "quadratic_comparison": quadratic_table()}
    path = Path(__file__).with_name("polynomial_results.json")
    path.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"status": "passed", "determinant_cases": 40,
                      "exhaustive_quadratic_tuples": 2 * 101 ** 2,
                      "witness_coefficients": output["obstruction_witness"]
                                                 ["coefficients_numerators"],
                      "output": str(path)}))


if __name__ == "__main__":
    main()
