#!/usr/bin/env python3
"""Enumerate carry chambers; save rational primal/dual certificates.

SciPy supplies numerical candidate certificates.  Every accepted certificate
is checked using fractions.Fraction before it is saved.  Independently run
verify_carry_certificates.py, which has no third-party dependencies.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog


def fraction_text(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def planes(kind: str, n: int) -> list[dict]:
    out = []
    for size in range(1, n + 1):
        for mask in range(1, 1 << n):
            if mask.bit_count() != size:
                continue
            last = size - 1 if kind == "C" else size
            for level in range(1, last + 1):
                normal = [(mask >> i) & 1 for i in range(n)]
                if kind == "D":
                    normal = [1] + normal
                out.append({"mask": mask, "level": level, "normal": normal})
    return out


def constraints(dimension: int, hyperplanes: list[dict], prefix: str):
    # All rows have the form a.x + t <= b, with t unrestricted.
    rows, rhs = [], []
    for i in range(dimension):
        row = [0] * dimension
        row[i] = -1
        rows.append(row + [1])
        rhs.append(0)
        row = [0] * dimension
        row[i] = 1
        rows.append(row + [1])
        rhs.append(1)
    for bit, plane in zip(prefix, hyperplanes):
        if bit == "0":  # a.x < level
            rows.append(plane["normal"] + [1])
            rhs.append(plane["level"])
        else:  # a.x > level
            rows.append([-v for v in plane["normal"]] + [1])
            rhs.append(-plane["level"])
    return rows, rhs


def solve_exact_system(matrix, rhs, suggested):
    """RREF over Q; fix any free coordinates to suggested rational values."""
    if not matrix:
        return []
    cols = len(matrix[0])
    a = [[Fraction(v) for v in row] + [Fraction(b)]
         for row, b in zip(matrix, rhs)]
    pivot_columns = []
    pivot_row = 0
    for column in range(cols):
        found = next((i for i in range(pivot_row, len(a)) if a[i][column]), None)
        if found is None:
            continue
        a[pivot_row], a[found] = a[found], a[pivot_row]
        scale = a[pivot_row][column]
        a[pivot_row] = [v / scale for v in a[pivot_row]]
        for i in range(len(a)):
            if i != pivot_row and a[i][column]:
                scale = a[i][column]
                a[i] = [v - scale * w for v, w in zip(a[i], a[pivot_row])]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == len(a):
            break
    for row in a:
        if not any(row[:cols]) and row[-1]:
            return None
    solution = list(suggested)
    for i, column in reversed(list(enumerate(pivot_columns))):
        solution[column] = a[i][-1] - sum(
            a[i][j] * solution[j] for j in range(cols) if j != column
        )
    return solution


def checked_primal(rows, rhs, point):
    for denominator in (1000, 1000000, 1000000000):
        x = [Fraction(float(v)).limit_denominator(denominator) for v in point[:-1]]
        slack = [Fraction(b) - sum(Fraction(a) * q for a, q in zip(row[:-1], x))
                 for row, b in zip(rows, rhs)]
        margin = min(slack)
        if margin > 0:
            return {"point": [fraction_text(v) for v in x],
                    "margin": fraction_text(margin)}
    raise RuntimeError("Could not certify a numerical positive-margin witness")


def checked_dual(rows, rhs, marginal):
    numeric = [-float(v) for v in marginal]
    support = [i for i, v in enumerate(numeric) if v > 1e-8]
    dimension = len(rows[0]) - 1
    target = [Fraction(0)] * dimension + [Fraction(1)]

    def valid(values):
        if values is None or any(v < 0 for v in values):
            return False
        lhs = [sum(values[j] * rows[i][column] for j, i in enumerate(support))
               for column in range(dimension + 1)]
        value = sum(values[j] * rhs[i] for j, i in enumerate(support))
        return lhs == target and value <= 0

    for denominator in (1000, 1000000, 1000000000):
        y = [Fraction(numeric[i]).limit_denominator(denominator) for i in support]
        if not valid(y):
            matrix = [[rows[i][column] for i in support]
                      for column in range(dimension + 1)]
            y = solve_exact_system(matrix, target, y)
        if valid(y):
            bound = sum(v * rhs[i] for i, v in zip(support, y))
            return {"multipliers": [[i, fraction_text(v)]
                                    for i, v in zip(support, y) if v],
                    "upper_bound": fraction_text(bound)}
    raise RuntimeError("Could not certify a numerical nonpositive dual bound")


def classify(dimension, hyperplanes, prefix):
    rows, rhs = constraints(dimension, hyperplanes, prefix)
    objective = np.zeros(dimension + 1)
    objective[-1] = -1
    for method in ("highs-ds", "highs-ipm"):
        result = linprog(objective, A_ub=np.asarray(rows, dtype=float),
                         b_ub=np.asarray(rhs, dtype=float),
                         bounds=[(None, None)] * (dimension + 1), method=method,
                         options={"primal_feasibility_tolerance": 1e-9,
                                  "dual_feasibility_tolerance": 1e-9})
        if not result.success:
            continue
        if result.x[-1] > 1e-8:
            return True, checked_primal(rows, rhs, result.x)
        try:
            return False, checked_dual(rows, rhs, result.ineqlin.marginals)
        except RuntimeError:
            if method == "highs-ipm":
                raise
    raise RuntimeError(f"LP failed for prefix {prefix!r}")


def carry_values(kind, n, point):
    values = [Fraction(v) for v in point]
    offset, coefficients = (Fraction(0), values) if kind == "C" else (values[0], values[1:])
    pattern = []
    for mask in range(1 << n):
        value = offset + sum(coefficients[i] for i in range(n) if mask & (1 << i))
        pattern.append(value.numerator // value.denominator)
    return pattern


def enumerate_case(kind, n):
    start = time.monotonic()
    dimension = n if kind == "C" else n + 1
    hyperplanes = planes(kind, n)
    if dimension == 0:
        active = {"": {"point": [], "margin": "1"}}
    else:
        feasible, witness = classify(dimension, hyperplanes, "")
        assert feasible
        active = {"": witness}
    rejected = []
    layer_counts = [1]
    calls = 0
    for index in range(len(hyperplanes)):
        next_active = {}
        for prefix in sorted(active):
            for bit in "01":
                extension = prefix + bit
                feasible, certificate = classify(dimension, hyperplanes, extension)
                calls += 1
                if feasible:
                    next_active[extension] = certificate
                else:
                    rejected.append({"prefix": extension, **certificate})
        active = next_active
        layer_counts.append(len(active))
    leaves = []
    for prefix, witness in sorted(active.items()):
        leaves.append({"signs": prefix, **witness,
                       "carry_values": carry_values(kind, n, witness["point"])})
    unique = {tuple(leaf["carry_values"]) for leaf in leaves}
    if len(unique) != len(leaves):
        raise RuntimeError("Distinct chambers produced an identical carry pattern")
    return {
        "kind": kind, "n": n, "dimension": dimension,
        "hyperplanes": hyperplanes, "count": len(leaves),
        "layers": layer_counts, "lp_calls": calls,
        "seconds": round(time.monotonic() - start, 3),
        "pruned": rejected, "chambers": leaves,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("carry_certificates.json"))
    args = parser.parse_args()
    results = []
    for kind, n in [("C", i) for i in range(5)] + [("D", i) for i in range(4)]:
        case = enumerate_case(kind, n)
        results.append(case)
        print(f"{kind}_{n} = {case['count']}; hyperplanes={len(case['hyperplanes'])}; "
              f"LP calls={case['lp_calls']}; seconds={case['seconds']}", flush=True)
        payload = {
            "format": "carry-chamber-certificates-v1",
            "rational_encoding": "integer or numerator/denominator strings",
            "bit_order": "vertex mask bit i is coefficient i; D offset is point[0]",
            "dual_convention": "a.x+t<=b; y>=0, sum(y*a)=0, sum(y)=1, b.y<=0",
            "cases": results,
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"Saved {args.output}", flush=True)


if __name__ == "__main__":
    main()
