#!/usr/bin/env python3
"""Exact checks for article Section 8; no ProveIt repository files are needed.

Run:
    python verify_gamma_exact.py
    python verify_gamma_exact.py --output /path/to/gamma_exact_checks.json

Dependency: SymPy.  All mathematical calculations use integers and SymPy
rationals.  No floating point approximations are used.  The script checks:

* Bernoulli source entries against the differential-operator entries;
* the complementary-minor normalization for m=1,...,4 and b=m+1,...,m+5;
* the determinant of the full 2b-by-2b formal moment-prefix matrix;
* the harmonic kappa_m formula against an exact Vandermonde determinant
  derivative for m=1,...,8;
* the signs of the gap-six recurrence determinants for 4 <= b <= 40;
* deliberate corruptions of the lower-index convention and the subtracted
  constant, both of which the independent normalization check must detect.

Finite checks validate the stated cases and algebraic normalization.  They
are not proofs of eventual asymptotics or of all gap-six nonvanishing.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
import json
from pathlib import Path
import platform
import sys
import time

import sympy as sp


@lru_cache(maxsize=None)
def bernoulli(n: int) -> sp.Expr:
    # Explicit convention, although the source entries use only even indices.
    return -sp.Rational(1, 2) if n == 1 else sp.bernoulli(n)


@lru_cache(maxsize=None)
def falling(n: int, order: int) -> sp.Integer:
    return sp.prod(sp.Integer(n - j) for j in range(order))


@lru_cache(maxsize=None)
def beta(k: int) -> sp.Expr:
    return 2 * abs(bernoulli(2 * k)) / sp.factorial(2 * k)


def a_factor(r: int, m: int, *, omit_subtraction: bool = False) -> sp.Expr:
    if r < m or (r == m and not omit_subtraction):
        return sp.Integer(0)
    return falling(2 * r, 2 * m)


def b_factor(n: int, m: int) -> sp.Expr:
    return falling(2 * n - 1, 2 * m)


def d_factor(n: int, m: int) -> sp.Expr:
    return 2 * (a_factor(n, m) + b_factor(n, m))


def source_entry(j: int, k: int, a: int, b: int,
                 *, allow_zero_lower: bool = False) -> sp.Expr:
    """Inherited Bernoulli coefficient, entered directly from its formula."""
    p, q, d = 2 * a, 2 * b, 2 * j + 1
    e = d - p - q + 2 * k + 1
    if e < 0:
        return sp.Integer(0)
    result = sp.Integer(0)
    for upper, lower in ((d - q + 1, p - 2 * k),
                         (d - p + 1, q - 2 * k)):
        admissible = 2 <= lower <= upper
        if allow_zero_lower and lower == 0:
            admissible = True
        if admissible:
            result += sp.binomial(upper, lower) / sp.Integer(upper)
    return bernoulli(e) * result


def source_matrix(m: int, b: int, *, allow_zero_lower: bool = False) -> sp.Matrix:
    return sp.Matrix(b, b, lambda r, k: source_entry(
        b + r, k, b - m, b, allow_zero_lower=allow_zero_lower))


def operator_matrix(m: int, b: int) -> sp.Matrix:
    """Independent coefficient extraction from the coth differential operator."""
    def entry(r: int, col: int) -> sp.Expr:
        n, total = col + 1, r + m + 1
        if n > total:
            return sp.Integer(0)
        h_index = total - n
        h = (sp.Integer(2) if h_index == 0 else
             2 * bernoulli(2 * h_index) / sp.factorial(2 * h_index))
        return h * (a_factor(n, m) + b_factor(total, m))
    return sp.Matrix(b, b, entry)


def fundamental_array(m: int, last_n: int,
                      *, omit_subtraction: bool = False) -> list[list[sp.Expr]]:
    """Rows are indexed by n; row zero is an unused all-zero sentinel."""
    rows = [[sp.Integer(0) for _ in range(m)] for _ in range(last_n + 1)]
    for n in range(1, m + 1):
        rows[n][n - 1] = sp.Integer(1)
    for n in range(m + 1, last_n + 1):
        bn = b_factor(n, m)
        denominator = d_factor(n, m)
        for j in range(m):
            rows[n][j] = sum(
                (beta(n - r) *
                 (a_factor(r, m, omit_subtraction=omit_subtraction) + bn) *
                 rows[r][j] for r in range(1, n)), sp.Integer(0)) / denominator
    return rows


def future_matrix(rows: list[list[sp.Expr]], b: int, m: int) -> sp.Matrix:
    return sp.Matrix([rows[b + i] for i in range(1, m + 1)])


def exact_det(matrix: sp.Matrix) -> sp.Expr:
    return matrix.det(method="domain-ge")


def bridge_prefactor(m: int, b: int) -> sp.Expr:
    return ((-1) ** (b * (b - 1) // 2) *
            sp.prod(d_factor(n, m) for n in range(m + 1, b + m + 1)) /
            (sp.Integer(4) ** b * sp.factorial(b)))


def full_prefix_matrix(m: int, b: int, late: sp.Matrix) -> sp.Matrix:
    """Coordinates of D_0,...,D_(2b-1) on C_0,...,C_(b-1),Z_0,...,Z_(b-1)."""
    coordinate_blocks = sp.diag(sp.eye(b), late)
    forward = sp.Matrix(2 * b, 2 * b, lambda r, j:
        sp.binomial(2 * r, 2 * j) *
        sp.bernoulli(2 * r - 2 * j, sp.Rational(1, 2)) /
        sp.Integer(2 * j + 1) if j <= r else sp.Integer(0))
    return forward * coordinate_blocks


def harmonic_kappa(m: int) -> sp.Expr:
    even_count = m // 2
    return (-sp.Rational(m * m * (m + 3) + even_count * (2 * m + 3), 4)
            + sum((r * (sp.harmonic(m + 2 * r) - sp.harmonic(m - 2 * r))
                   for r in range(1, even_count + 1)), sp.Integer(0)))


def vandermonde_derivative(m: int) -> tuple[sp.Expr, list[sp.Expr]]:
    """Differentiate a perturbed determinant by exact column multilinearity.

    A common pi^(-2i) row factor cancels in det'(0)/det(0), so the
    Vandermonde nodes are the rational numbers 1/j^2.
    """
    nodes = [sp.Rational(1, j * j) for j in range(1, m + 1)]
    degrees = [m + int(j % 2 == 0) for j in range(1, m + 1)]
    matrix = sp.Matrix(m, m, lambda r, j: nodes[j] ** (r + 1))
    determinant = exact_det(matrix)
    derivative = sp.Integer(0)
    for j, degree in enumerate(degrees):
        perturbed = matrix.copy()
        perturbed[:, j] = sp.Matrix([
            matrix[r, j] * (sp.Rational(degree * (degree - 1), 4) -
                            (r + 1) * degree)
            for r in range(m)])
        derivative += exact_det(perturbed)
    eta_matrix = matrix.inv() * sp.diag(*range(1, m + 1)) * matrix
    return derivative / determinant, [eta_matrix[j, j] for j in range(m)]


def run_checks() -> dict:
    start = time.perf_counter()
    failures: list[str] = []
    result = {
        "description": "Standalone exact rational audit of article Section 8",
        "arithmetic": "SymPy Integer/Rational only; no numerical tolerance",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "scope_note": (
            "Finite exact identities and signs only. These computations do not "
            "prove eventual asymptotics, supply B(m), or settle all gap-six pairs."),
        "normalization_cases": [],
        "kappa_cases": [],
        "gap_six_signs": [],
        "corruption_canaries": [],
    }
    entry_count = 0
    prefix_count = 0
    eta_count = 0

    print("Checking Bernoulli entries, complementary minors, and full prefixes...", flush=True)
    for m in range(1, 5):
        rows = fundamental_array(m, 2 * m + 5)
        for b in range(m + 1, m + 6):
            late = source_matrix(m, b)
            op = operator_matrix(m, b)
            reversed_late = late[:, ::-1]
            transformed = (sp.diag(*[sp.Rational(2, sp.factorial(2 * r + 1))
                                    for r in range(b)]) * reversed_late *
                           sp.diag(*[sp.factorial(2 * n) for n in range(1, b + 1)]))
            entries_ok = transformed == op
            entry_count += b * b
            det_late = exact_det(late)
            det_future = exact_det(future_matrix(rows, b, m))
            rhs = bridge_prefactor(m, b) * det_future
            bridge_ok = det_late == rhs
            det_prefix = exact_det(full_prefix_matrix(m, b, late))
            prefix_expected = det_late / sp.factorial2(4 * b - 1)
            prefix_ok = det_prefix == prefix_expected
            prefix_count += 1
            case = {
                "m": m, "b": b, "p": 2 * (b - m), "q": 2 * b,
                "all_operator_entries_equal": entries_ok,
                "operator_entry_count": b * b,
                "det_M": str(det_late), "det_F": str(det_future),
                "bridge_prefactor": str(bridge_prefactor(m, b)),
                "bridge_residual": str(det_late - rhs),
                "bridge_equal": bridge_ok,
                "full_prefix_dimension": 2 * b,
                "full_prefix_det": str(det_prefix),
                "full_prefix_residual": str(det_prefix - prefix_expected),
                "full_prefix_equal": prefix_ok,
            }
            result["normalization_cases"].append(case)
            if not (entries_ok and bridge_ok and prefix_ok):
                failures.append(f"normalization m={m}, b={b}")

    print("Checking harmonic kappa against exact Vandermonde derivatives...", flush=True)
    for m in range(1, 9):
        derivative, eta_values = vandermonde_derivative(m)
        harmonic = harmonic_kappa(m)
        eta_formula = [sp.Integer(m) + sp.Rational(3, 4) + sp.Rational(j, 2) *
                       (sp.harmonic(m - j) - sp.harmonic(m + j))
                       for j in range(1, m + 1)]
        eta_ok = eta_values == eta_formula
        eta_count += m
        kappa_ok = derivative == harmonic
        result["kappa_cases"].append({
            "m": m, "harmonic_formula": str(harmonic),
            "determinant_derivative_ratio": str(derivative),
            "residual": str(derivative - harmonic), "equal": kappa_ok,
            "eta_values": [str(value) for value in eta_values],
            "eta_harmonic_formula_equal": eta_ok,
        })
        if not (kappa_ok and eta_ok):
            failures.append(f"kappa/eta m={m}")

    print("Checking gap-six signs with exact rationals for 4 <= b <= 40...", flush=True)
    gap_rows = fundamental_array(3, 43)
    for b in range(4, 41):
        determinant = exact_det(future_matrix(gap_rows, b, 3))
        sign = int(sp.sign(determinant))
        expected = -1 if b <= 6 else 1
        agrees = sign == expected
        result["gap_six_signs"].append({
            "b": b, "p": 2 * b - 6, "q": 2 * b,
            "det_F": str(determinant), "sign": sign,
            "nonzero": determinant != 0,
            "expected_sign_in_this_finite_range": expected,
            "agrees": agrees,
        })
        if not agrees:
            failures.append(f"gap-six sign b={b}")

    print("Checking deliberate-corruption canaries...", flush=True)
    m, b = 2, 4
    good_rows = fundamental_array(m, b + m)
    reference_rhs = bridge_prefactor(m, b) * exact_det(future_matrix(good_rows, b, m))
    wrong_source = exact_det(source_matrix(m, b, allow_zero_lower=True))
    source_canary = wrong_source != reference_rhs
    result["corruption_canaries"].append({
        "name": "include_forbidden_lower_binomial_index_zero",
        "m": m, "b": b,
        "correct_det_M": str(reference_rhs), "corrupted_det_M": str(wrong_source),
        "nonzero_residual": str(wrong_source - reference_rhs),
        "expected_failure_detected": source_canary,
    })
    wrong_rows = fundamental_array(m, b + m, omit_subtraction=True)
    wrong_rhs = bridge_prefactor(m, b) * exact_det(future_matrix(wrong_rows, b, m))
    recurrence_canary = wrong_rhs != reference_rhs
    result["corruption_canaries"].append({
        "name": "remove_the_subtraction_R_derivative_at_zero",
        "m": m, "b": b,
        "correct_det_M": str(reference_rhs), "corrupted_bridge_rhs": str(wrong_rhs),
        "nonzero_residual": str(wrong_rhs - reference_rhs),
        "expected_failure_detected": recurrence_canary,
    })
    if not (source_canary and recurrence_canary):
        failures.append("a deliberate-corruption canary was not detected")

    result["counts"] = {
        "operator_entry_equalities": entry_count,
        "complementary_minor_equalities": len(result["normalization_cases"]),
        "full_prefix_determinant_equalities": prefix_count,
        "kappa_equalities": len(result["kappa_cases"]),
        "eta_equalities": eta_count,
        "gap_six_sign_checks": len(result["gap_six_signs"]),
        "corruption_canaries": len(result["corruption_canaries"]),
    }
    result["failures"] = failures
    result["all_passed"] = not failures
    result["elapsed_seconds"] = round(time.perf_counter() - start, 6)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().with_name("gamma_exact_checks.json"))
    args = parser.parse_args()
    report = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"all_passed": report["all_passed"],
                      "counts": report["counts"],
                      "elapsed_seconds": report["elapsed_seconds"],
                      "output": str(args.output.resolve())}, indent=2))
    return 0 if report["all_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
