#!/usr/bin/env python3
"""Exact finite checks for the C^r Rvachev spectral-disk manuscript.

The program uses only Python's standard library.  It verifies finite algebraic
identities that support the article; it does not attempt to prove any
infinite-dimensional spectral theorem by sampling.
"""

from __future__ import annotations

import argparse
import json
import platform
from dataclasses import dataclass
from fractions import Fraction
from math import comb
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

F = Fraction
Matrix = List[List[Fraction]]
Poly = Dict[int, Fraction]  # coefficient of q^degree, q represents pi^2
PolyMatrix = List[List[Poly]]


def mat_vec(A: Matrix, v: Sequence[Fraction]) -> List[Fraction]:
    return [sum(a * x for a, x in zip(row, v)) for row in A]


def vec_scale(c: Fraction, v: Sequence[Fraction]) -> List[Fraction]:
    return [c * x for x in v]


def determinant3(A: Matrix) -> Fraction:
    a, b, c = A[0]
    d, e, f = A[1]
    g, h, i = A[2]
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def characteristic_coefficients(A: Matrix) -> List[Fraction]:
    """Return coefficients [1,c2,c1,c0] of det(z I-A) for a 3x3 matrix."""
    tr = sum(A[i][i] for i in range(3))
    # For 3x3: z^3 - tr(A) z^2 + 1/2((tr A)^2-tr A^2) z - det A.
    A2_trace = sum(
        sum(A[i][k] * A[k][i] for k in range(3)) for i in range(3)
    )
    c1 = (tr * tr - A2_trace) / 2
    return [F(1), -tr, c1, -determinant3(A)]


def p_add(a: Poly, b: Poly) -> Poly:
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, F(0)) + v
        if out[k] == 0:
            del out[k]
    return out


def p_mul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for i, x in a.items():
        for j, y in b.items():
            out[i + j] = out.get(i + j, F(0)) + x * y
    return {k: v for k, v in out.items() if v}


def pm_identity(n: int) -> PolyMatrix:
    return [[({0: F(1)} if i == j else {}) for j in range(n)] for i in range(n)]


def pm_mul(A: PolyMatrix, B: PolyMatrix) -> PolyMatrix:
    n, m, p = len(A), len(B), len(B[0])
    if len(A[0]) != m:
        raise ValueError("matrix dimensions do not match")
    out: PolyMatrix = [[{} for _ in range(p)] for _ in range(n)]
    for i in range(n):
        for k in range(m):
            if not A[i][k]:
                continue
            for j in range(p):
                if B[k][j]:
                    out[i][j] = p_add(out[i][j], p_mul(A[i][k], B[k][j]))
    return out


def pm_is_zero(A: PolyMatrix) -> bool:
    return all(not entry for row in A for entry in row)


def sine_jet_matrix(r: int) -> PolyMatrix:
    """Matrix for Delta(P f) for omega(x)=sin^2(pi x/2).

    q denotes pi^2.  The diagonal is zero because omega(0)=0.  For
    k=2 ell, omega^(k)(0)=(-1)^(ell+1) pi^(2 ell)/2.
    """
    n = r + 1
    M: PolyMatrix = [[{} for _ in range(n)] for _ in range(n)]
    for j in range(n):
        for m in range(j):
            k = j - m
            if k % 2:
                continue
            ell = k // 2
            deriv_coeff = F((-1) ** (ell + 1), 2)
            coeff = F(comb(j, k), 2**m) * deriv_coeff
            M[j][m] = {ell: coeff}
    return M


def descendants(k: int, n: int) -> set[int]:
    values = {k}
    for _ in range(n):
        values = {2 * q + s for q in values for s in (-1, 0, 1)}
    return values


def fraction_json(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


@dataclass
class Results:
    checks: int = 0
    matrix_entries: int = 0
    descendant_cases: int = 0
    jet_orders: int = 0
    threshold_orders: int = 0

    def check(self, condition: bool, message: str) -> None:
        self.checks += 1
        if not condition:
            raise RuntimeError(message)


def run(max_level: int, max_jet: int) -> dict:
    R = Results()

    A: Matrix = [
        [F(-1, 2), F(0), F(0)],
        [F(-1, 2), F(1), F(-1, 2)],
        [F(0), F(0), F(-1, 2)],
    ]
    R.matrix_entries = 9

    expected_char = [F(1), F(0), F(-3, 4), F(-1, 4)]
    actual_char = characteristic_coefficients(A)
    R.check(actual_char == expected_char, f"wrong characteristic polynomial: {actual_char}")

    eigenvectors = [
        (F(1), [F(0), F(1), F(0)], "constant"),
        (F(-1, 2), [F(3), F(2), F(3)], "cosine plus one third"),
        (F(-1, 2), [F(1), F(0), F(-1)], "sine direction"),
    ]
    for lam, v, name in eigenvectors:
        R.check(mat_vec(A, v) == vec_scale(lam, v), f"bad eigenvector: {name}")

    # Direct mode columns.
    expected_columns = [
        [F(-1, 2), F(-1, 2), F(0)],
        [F(0), F(1), F(0)],
        [F(0), F(-1, 2), F(-1, 2)],
    ]
    actual_columns = [[A[i][j] for i in range(3)] for j in range(3)]
    R.check(actual_columns == expected_columns, "mode-action columns do not match")

    # Descendant-frequency bound.
    for n in range(max_level + 1):
        for k in list(range(-6, -1)) + list(range(2, 7)):
            vals = descendants(k, n)
            lower = min(abs(q) for q in vals)
            R.check(lower >= 2**n + 1, f"descendant bound failed at k={k}, n={n}")
            R.descendant_cases += 1

    # Jet matrices and exact nilpotence in the sine case.
    jet_summaries = []
    for r in range(max_jet + 1):
        M = sine_jet_matrix(r)
        n = r + 1
        R.check(all(not M[i][i] for i in range(n)), f"nonzero sine diagonal at r={r}")
        # Strict triangularity implies M^(r+1)=0; verify by exact polynomial arithmetic.
        P = pm_identity(n)
        for _ in range(n):
            P = pm_mul(P, M)
        R.check(pm_is_zero(P), f"jet matrix not nilpotent at r={r}")
        # Formula can only connect j to j-2, j-4, ...
        for j in range(n):
            for m in range(n):
                if M[j][m]:
                    R.check(m <= j - 2 and (j - m) % 2 == 0,
                            f"unexpected jet entry at ({j},{m})")
        R.jet_orders += 1
        jet_summaries.append({
            "r": r,
            "dimension": n,
            "nilpotence_verified_at_power": n,
            "nonzero_entries": sum(bool(x) for row in M for x in row),
        })

    # Threshold table and scaling P -> L=P/2.
    thresholds = []
    for r in range(max_jet + 1):
        p_radius = F(1, 2**r)
        l_radius = F(1, 2 ** (r + 1))
        lead = F(1, 2)
        sub = F(1, 4)
        expected_lead_status = "boundary" if r == 0 else "isolated"
        if r == 0:
            expected_sub_status = "interior"
        elif r == 1:
            expected_sub_status = "boundary"
        else:
            expected_sub_status = "isolated"
        lead_status = "isolated" if lead > l_radius else ("boundary" if lead == l_radius else "interior")
        sub_status = "isolated" if sub > l_radius else ("boundary" if sub == l_radius else "interior")
        R.check(lead_status == expected_lead_status, f"leading threshold mismatch at r={r}")
        R.check(sub_status == expected_sub_status, f"subleading threshold mismatch at r={r}")
        R.check(l_radius == p_radius / 2, f"normalization mismatch at r={r}")
        R.threshold_orders += 1
        thresholds.append({
            "r": r,
            "P_essential_radius": fraction_json(p_radius),
            "L_essential_radius": fraction_json(l_radius),
            "leading_1_over_2": lead_status,
            "subleading_minus_1_over_4": sub_status,
        })

    return {
        "status": "pass",
        "python": platform.python_version(),
        "arithmetic": "fractions.Fraction and formal polynomials in q=pi^2",
        "parameters": {"max_level": max_level, "max_jet": max_jet},
        "counts": {
            "asserted_checks": R.checks,
            "matrix_entries": R.matrix_entries,
            "descendant_cases": R.descendant_cases,
            "jet_orders": R.jet_orders,
            "threshold_orders": R.threshold_orders,
        },
        "finite_matrix": {
            "basis": ["e_-1", "e_0", "e_1"],
            "matrix": [[fraction_json(x) for x in row] for row in A],
            "characteristic_coefficients_descending": [fraction_json(x) for x in actual_char],
            "factorization": "(z-1)(z+1/2)^2",
        },
        "jet_summaries": jet_summaries,
        "thresholds": thresholds,
        "scope_note": (
            "Finite exact checks catch algebraic and indexing errors; they do not prove "
            "the infinite-dimensional Fredholm, Calkin, compactness, or smoothness theorems."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-level", type=int, default=12)
    parser.add_argument("--max-jet", type=int, default=12)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    if args.max_level < 0 or args.max_jet < 0:
        raise SystemExit("levels must be nonnegative")

    result = run(args.max_level, args.max_jet)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "counts": result["counts"]}, indent=2))


if __name__ == "__main__":
    main()
