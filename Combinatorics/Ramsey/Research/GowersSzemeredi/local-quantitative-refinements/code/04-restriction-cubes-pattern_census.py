#!/usr/bin/env python3
"""Certify small fractional floor-pattern counts by exact rational arithmetic.

Generation uses scipy.optimize.linprog only to propose certificates. Every
accepted branch is checked with fractions.Fraction. Verification uses only
the Python standard library, exhaustively checks both sides of every proposed
hyperplane split, and never uses numerical tolerances.

Examples:
    python pattern_census.py --generate pattern_census.json
    python pattern_census.py --verify pattern_census.json

An open polytope A*x < b is certified nonempty by a rational point x. It is
certified empty by rational nonnegative weights y, sum(y)=1, with A^T*y=0
and b*y <= 0. The latter identities contradict the weighted sum of all
strict inequalities. This is sufficient to prove all counts in the file.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path


def hyperplanes(k: int, affine: bool) -> list[tuple[list[int], int]]:
    dimension = k + int(affine)
    result = []
    for size in range(1, k + 1):
        for subset in combinations(range(k), size):
            normal = [0] * dimension
            for index in subset:
                normal[index + int(affine)] = 1
            if affine:
                normal[0] = 1
            for threshold in range(1, size + int(affine)):
                result.append((normal.copy(), threshold))
    return result


def constraints(dimension, planes, signature):
    matrix, rhs = [], []
    for index in range(dimension):
        row = [0] * dimension
        row[index] = 1
        matrix.append(row)
        rhs.append(1)
    for index in range(dimension):
        row = [0] * dimension
        row[index] = -1
        matrix.append(row)
        rhs.append(0)
    for (normal, threshold), side in zip(planes, signature):
        sign = 1 if side == "0" else -1
        matrix.append([sign * entry for entry in normal])
        rhs.append(sign * threshold)
    return matrix, rhs


def check_certificate(matrix, rhs, certificate):
    """Return whether the open polytope is inhabited; reject invalid data."""
    dimension = len(matrix[0])
    if set(certificate) == {"point"}:
        point = [Fraction(value) for value in certificate["point"]]
        if len(point) != dimension:
            raise ValueError("Incorrect point dimension")
        for row, bound in zip(matrix, rhs):
            if sum(coefficient * value for coefficient, value in zip(row, point)) >= bound:
                raise ValueError("Point does not satisfy all inequalities strictly")
        return True
    if set(certificate) == {"dual"}:
        weights = [Fraction(value) for value in certificate["dual"]]
        if len(weights) != len(rhs):
            raise ValueError("Incorrect dual dimension")
        if any(value < 0 for value in weights) or sum(weights) != 1:
            raise ValueError("Dual weights are not a rational probability vector")
        for index in range(dimension):
            if sum(weight * row[index] for weight, row in zip(weights, matrix)) != 0:
                raise ValueError("Dual combination of normals is nonzero")
        if sum(weight * bound for weight, bound in zip(weights, rhs)) > 0:
            raise ValueError("Dual combination does not exclude strict feasibility")
        return False
    raise ValueError("Unknown certificate type")


def propose_certificate(matrix, rhs):
    import numpy as np
    from scipy.optimize import linprog

    dimension = len(matrix[0])
    # Maximize a common strictness margin rho. All variables, including rho,
    # are unrestricted, making this LP always feasible and bounded above.
    result = linprog(
        np.r_[np.zeros(dimension), -1.0],
        A_ub=np.c_[np.array(matrix, dtype=float), np.ones(len(rhs))],
        b_ub=np.array(rhs, dtype=float),
        bounds=[(None, None)] * (dimension + 1),
        method="highs",
    )
    if not result.success:
        raise RuntimeError(f"Certificate proposal failed: {result.message}")

    def rationalize(values):
        return [str(Fraction(float(value)).limit_denominator(10**6)) for value in values]

    point = {"point": rationalize(result.x[:dimension])}
    try:
        check_certificate(matrix, rhs, point)
        return point
    except ValueError:
        pass

    dual = {"dual": rationalize(-result.ineqlin.marginals)}
    try:
        check_certificate(matrix, rhs, dual)
        return dual
    except ValueError as error:
        raise RuntimeError("Numerical proposal did not yield an exact certificate") from error


def generate_case(k, affine):
    dimension = k + int(affine)
    planes = hyperplanes(k, affine)
    active = [""]
    stages = []
    for index in range(len(planes)):
        next_active = []
        branches = {}
        for signature in active:
            for side in "01":
                child = signature + side
                matrix, rhs = constraints(dimension, planes, child)
                certificate = propose_certificate(matrix, rhs)
                branches[child] = certificate
                if check_certificate(matrix, rhs, certificate):
                    next_active.append(child)
        active = next_active
        stages.append(branches)
    return {
        "k": k,
        "affine": affine,
        "count": len(active),
        "stages": stages,
    }


def verify_case(case):
    k, affine = case["k"], case["affine"]
    if not isinstance(k, int) or k < 1 or not isinstance(affine, bool):
        raise ValueError("Incorrect case parameters")
    dimension = k + int(affine)
    planes = hyperplanes(k, affine)
    stages = case["stages"]
    if len(stages) != len(planes):
        raise ValueError("Incorrect number of hyperplane stages")
    active = [""]
    checked = 0
    for index, branches in enumerate(stages):
        expected = {signature + side for signature in active for side in "01"}
        if set(branches) != expected:
            raise ValueError(f"Stage {index} does not check exactly all necessary branches")
        next_active = []
        for child in sorted(expected):
            matrix, rhs = constraints(dimension, planes, child)
            inhabited = check_certificate(matrix, rhs, branches[child])
            checked += 1
            if inhabited:
                next_active.append(child)
        active = next_active
    if len(active) != case["count"]:
        raise ValueError("Declared chamber count does not match exact verification")
    return len(active), checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--generate", type=Path)
    group.add_argument("--verify", type=Path)
    args = parser.parse_args()
    if args.generate:
        payload = {
            "format": "fractional-floor-pattern-census-v1",
            "cases": [generate_case(k, affine) for affine in (False, True) for k in range(1, 4)],
        }
        args.generate.write_text(json.dumps(payload, indent=2) + "\n")
    else:
        payload = json.loads(args.verify.read_text())
    if payload.get("format") != "fractional-floor-pattern-census-v1":
        raise ValueError("Unknown certificate format")
    total = 0
    for case in payload["cases"]:
        count, checked = verify_case(case)
        total += checked
        symbol = "A" if case["affine"] else "F"
        print(f"{symbol}_{case['k']} = {count}; {checked} exact branch certificates checked")
    print(f"Verified {total} branch certificates using rational arithmetic only.")


if __name__ == "__main__":
    main()
