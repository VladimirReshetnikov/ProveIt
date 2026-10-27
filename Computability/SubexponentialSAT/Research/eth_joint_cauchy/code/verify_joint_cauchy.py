#!/usr/bin/env python3
"""Independent exact checks for joint_cauchy.py; run normally or with -O.

Run from this directory:
    python3 verify_joint_cauchy.py --output ../results/joint_cauchy_validation.json

Tests are finite evidence for the algebraic implementation, not proofs of a
SAT running-time bound. No assertions are used, so Python -O retains checks.
"""
from __future__ import annotations

import argparse
import itertools
import json
import platform
from fractions import Fraction
from math import inf
from pathlib import Path
from time import perf_counter

from joint_cauchy import (JointCauchyKernel, Quadratic, Scalar, exact_divide,
                         residue, residue_add, residue_multiply, v2)


COUNTS: dict[str, int] = {}


def check(condition: bool, name: str, detail: str = "") -> None:
    if not condition:
        raise ArithmeticError(f"{name} failed: {detail}")
    COUNTS[name] = COUNTS.get(name, 0) + 1


def original_polynomial_entry(a: int, T: Scalar, x: int, y: int) -> Scalar:
    """Evaluate the original polynomial after cancelling its indicated factor."""
    L = 1 << a
    value: Scalar = Fraction(1)
    denominator = 1
    for q in range(-L, L):
        if q != y - x:
            value *= T - q
        if q:
            denominator *= -q
    return exact_divide(value, denominator)


def determinant(matrix: list[list[Scalar]]) -> Scalar:
    if not matrix:
        return Fraction(1)
    matrix = [row[:] for row in matrix]
    result: Scalar = Fraction(1)
    n = len(matrix)
    for column in range(n):
        pivot = next((row for row in range(column, n) if matrix[row][column] != 0), None)
        if pivot is None:
            return Fraction(0)
        if pivot != column:
            matrix[pivot], matrix[column] = matrix[column], matrix[pivot]
            result *= -1
        entry = matrix[column][column]
        result *= entry
        for row in range(column + 1, n):
            multiplier = exact_divide(matrix[row][column], entry)
            for j in range(column + 1, n):
                matrix[row][j] -= multiplier * matrix[column][j]
            matrix[row][column] = Fraction(0)
    return result


def verify_kernel() -> list[dict[str, object]]:
    cases = []
    zetas = (Fraction(0), Fraction(1), Fraction(2, 3),
             Quadratic(0, 1), Quadratic(1, 1), Quadratic(0, 2))
    for a in range(1, 5):
        for i in range(a):
            # Both signs, and a second odd residue when it fits the grid.
            nodes = sorted({-(1 << i), 1 << i,
                            *((3 << i,) if (3 << i) < (1 << a) else ())})
            for t in nodes:
                for zeta in zetas:
                    kernel = JointCauchyKernel(a, i, t, zeta)
                    target, source = kernel.feature_tables()
                    for b in range(kernel.size):
                        check(v2(kernel.row_factor(b, b)) == 0,
                              "normalized_row_diagonal_unit")
                        check(v2(source[b][b]) == 0, "normalized_source_diagonal_unit")
                        for j in range(kernel.size):
                            check(v2(source[b][j]) >= 0, "source_integrality")
                            check(v2(kernel.row_factor(b, j)) >= 0, "row_integrality")
                            check(v2(target[b][j]) >= kernel.weight(b), "target_weight")
                            if j < b:
                                check(source[b][j] == 0 and target[b][j] == 0,
                                      "triangular_support")
                    for j, k in itertools.product(range(kernel.size), repeat=2):
                        reconstructed = sum((target[b][j] * source[b][k]
                                             for b in range(kernel.size)), Fraction(0))
                        for orientation in (0, 1):
                            expected = original_polynomial_entry(
                                a, kernel.T, kernel.slot(j, orientation), kernel.slot(k, orientation))
                            check(reconstructed == expected, "exact_cauchy_reconstruction")
                        for p in (1, 2, 4, 7, 11):
                            value = (0, 0)
                            modulus = 1 << p
                            for b in range(kernel.size):
                                if kernel.weight(b) < p:
                                    product = residue_multiply(residue(target[b][j], p),
                                                               residue(source[b][k], p), modulus)
                                    value = residue_add(value, product, modulus)
                            check(value == residue(expected, p), "truncated_modular_reconstruction")
                    cases.append({"a": a, "i": i, "t": t, "zeta": str(zeta),
                                  "size": kernel.size,
                                  "weights": [kernel.weight(b) for b in range(kernel.size)]})
    return cases


def verify_smith() -> list[dict[str, object]]:
    results = []
    # All minors of each 4x4 full orientation, including non-prime-subring T.
    for i in range(3):
        for zeta in (Fraction(1), Quadratic(0, 1)):
            kernel = JointCauchyKernel(3, i, 1 << i, zeta)
            matrix = [[original_polynomial_entry(3, kernel.T, kernel.slot(j), kernel.slot(k))
                       for k in range(kernel.size)] for j in range(kernel.size)]
            cumulative = 0
            observed = []
            for size in range(1, kernel.size + 1):
                minimum = inf
                for rows in itertools.combinations(range(kernel.size), size):
                    for columns in itertools.combinations(range(kernel.size), size):
                        minor = [[matrix[j][k] for k in columns] for j in rows]
                        minimum = min(minimum, v2(determinant(minor)))
                        COUNTS["smith_minors_evaluated"] = COUNTS.get("smith_minors_evaluated", 0) + 1
                cumulative += kernel.weight(size - 1)
                check(minimum == cumulative, "smith_determinantal_divisor")
                observed.append(int(minimum))
            results.append({"a": 3, "i": i, "zeta": str(zeta),
                            "minimum_minor_valuations": observed,
                            "smith_valuations": [kernel.weight(b) for b in range(kernel.size)]})
    return results


def bits(index: int, size: int) -> tuple[int, ...]:
    return tuple((index >> j) & 1 for j in range(size))


def compositions(maximum_total: int, variables: int) -> list[tuple[int, ...]]:
    return [v for v in itertools.product(range(maximum_total + 1), repeat=variables)
            if sum(v) <= maximum_total]


def multiply_affine(polynomial: dict[tuple[int, ...], Scalar], local: Scalar,
                    coefficients: list[Scalar]) -> dict[tuple[int, ...], Scalar]:
    result: dict[tuple[int, ...], Scalar] = {}
    for powers, coefficient in polynomial.items():
        result[powers] = result.get(powers, Fraction(0)) + coefficient * local
        for b, value in enumerate(coefficients):
            changed = tuple(power + int(h == b) for h, power in enumerate(powers))
            result[changed] = result.get(changed, Fraction(0)) + coefficient * value
    return result


def verify_packet_contractions() -> list[dict[str, object]]:
    """Check the actual two-child coefficient-extraction contraction identity."""
    results = []
    for i in (0, 1):
        for zeta in (Fraction(1), Quadratic(0, 1)):
            kernel = JointCauchyKernel(2, i, 1 << i, zeta)
            d = kernel.size
            target, source = kernel.feature_tables()
            W = [[original_polynomial_entry(2, kernel.T, x, y) for y in range(kernel.L)]
                 for x in range(kernel.L)]
            # Each group contains its row orientation and the opposite column orientation.
            slots = [[kernel.slot(j, g) for j in range(d)] for g in (0, 1)]
            row_tables = ([2, -1, 3, 1], [1, 4, -2, 3])
            column_tables = ([3, 2, -1, 1], [2, -3, 1, 4])
            brute: Scalar = Fraction(0)
            for y0, y1, x0, x1 in itertools.product(range(1 << d), repeat=4):
                y_by_group = (bits(y0, d), bits(y1, d))
                x_by_group = (bits(x0, d), bits(x1, d))
                all_x = [0] * kernel.L
                for g in (0, 1):
                    for j in range(d):
                        all_x[slots[1-g][j]] = x_by_group[g][j]
                term: Scalar = (row_tables[0][y0] * row_tables[1][y1]
                                * column_tables[0][x0] * column_tables[1][x1])
                for g in (0, 1):
                    for j, ybit in enumerate(y_by_group[g]):
                        argument = sum((W[slots[g][j]][k] * all_x[k]
                                        for k in range(kernel.L)), Fraction(0))
                        term *= argument if ybit else 1 - argument
                brute += term

            all_beta = compositions(d, d)
            child_cache: dict[tuple[int, tuple[int, ...], tuple[int, ...]], Scalar] = {}
            for g in (0, 1):
                for wanted, outgoing in itertools.product(all_beta, repeat=2):
                    value: Scalar = Fraction(0)
                    for yindex, xindex in itertools.product(range(1 << d), repeat=2):
                        ybits, xbits = bits(yindex, d), bits(xindex, d)
                        polynomial: dict[tuple[int, ...], Scalar] = {(0,) * d: Fraction(1)}
                        for j, ybit in enumerate(ybits):
                            local = sum((W[slots[g][j]][slots[1-g][k]] * xbits[k]
                                         for k in range(d)), Fraction(0))
                            sign = 1 if ybit else -1
                            if not ybit:
                                local = 1 - local
                            polynomial = multiply_affine(polynomial, local,
                                                         [sign * target[b][j] for b in range(d)])
                        coefficient = polynomial.get(wanted, Fraction(0))
                        for b in range(d):
                            moment = sum((source[b][k] * xbits[k] for k in range(d)), Fraction(0))
                            coefficient *= moment ** outgoing[b]
                        value += row_tables[g][yindex] * column_tables[g][xindex] * coefficient
                    child_cache[g, wanted, outgoing] = value
            reconstructed = sum((child_cache[0, b0, b1] * child_cache[1, b1, b0]
                                 for b0, b1 in itertools.product(all_beta, repeat=2)), Fraction(0))
            check(reconstructed == brute, "exact_two_child_packet_contraction")
            for p in (1, 2, 4, 7, 11, 16):
                truncated: Scalar = Fraction(0)
                retained = 0
                for b0, b1 in itertools.product(all_beta, repeat=2):
                    weight = sum(kernel.weight(b) * (b0[b] + b1[b]) for b in range(d))
                    if weight < p:
                        truncated += child_cache[0, b0, b1] * child_cache[1, b1, b0]
                        retained += 1
                check(residue(truncated, p) == residue(brute, p),
                      "truncated_two_child_packet_contraction")
                results.append({"a": 2, "i": i, "zeta": str(zeta), "precision": p,
                                "retained_tuples": retained,
                                "total_tuples": len(all_beta)**2,
                                "residue": list(residue(brute, p))})
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "results" / "joint_cauchy_validation.json")
    args = parser.parse_args()
    started = perf_counter()
    cases = verify_kernel()
    smith = verify_smith()
    packets = verify_packet_contractions()
    result = {"status": "PASS", "python": platform.python_version(),
              "optimized_python": not __debug__, "elapsed_seconds": round(perf_counter() - started, 4),
              "scope": "Finite exact tests of the local kernel and packet recursion; not a SAT benchmark or formal proof.",
              "counts": COUNTS, "kernel_cases": cases, "smith_cases": smith,
              "packet_cases": packets}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "elapsed_seconds": result["elapsed_seconds"],
                      "kernel_cases": len(cases), "counts": COUNTS,
                      "output": str(args.output)}, sort_keys=True))


if __name__ == "__main__":
    main()

