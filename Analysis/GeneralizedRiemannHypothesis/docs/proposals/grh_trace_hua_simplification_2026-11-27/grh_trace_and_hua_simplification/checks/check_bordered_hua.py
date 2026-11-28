#!/usr/bin/env python3
"""Exact regression checks for the bordered-Hua replacement proposal.

This script is deliberately independent of the Lean source and does not certify
the GRH theorem or the proposed Lean adapter.  The general proofs are in
bordered_hua.md.  Every calculation here uses exact SymPy arithmetic.

Usage:
    python check_bordered_hua.py --output bordered_hua_checks.json
"""

from __future__ import annotations

import argparse
import json
import random
from pathlib import Path

import sympy as sp


def exact_zero(value: sp.Expr) -> bool:
    return sp.cancel(sp.expand_complex(sp.expand(value))) == 0


def check_matrix_zero(value: sp.Matrix, label: str) -> None:
    assert all(exact_zero(x) for x in value), label


def random_complex_matrix(rng: random.Random, rows: int, cols: int) -> sp.Matrix:
    return sp.Matrix(
        rows,
        cols,
        lambda _r, _c: sp.Rational(rng.randint(-2, 2), rng.randint(1, 3))
        + sp.I * sp.Rational(rng.randint(-2, 2), rng.randint(1, 3)),
    )


def random_invertible(rng: random.Random, size: int) -> sp.Matrix:
    while True:
        candidate = random_complex_matrix(rng, size, size)
        if not exact_zero(candidate.det()):
            return candidate


def bordered_case(rng: random.Random, k: int, i: int) -> dict[str, int]:
    # H is positive definite by construction, over the rational complex numbers.
    source = random_complex_matrix(rng, i + 1, i + 1)
    H = source.H * source + sp.eye(i + 1)
    U = random_complex_matrix(rng, k, i)
    v = random_complex_matrix(rng, k, 1)
    h = sp.simplify(H[i, i])
    b = H[:i, i : i + 1]
    S = H[:i, :i] - b * b.H / h
    a = sp.simplify(h + (v.H * v)[0])
    G = sp.eye(k) - v * v.H / a
    Uc = v * b.H / h
    W = U - Uc
    C = sp.eye(i + 1)
    C[i : i + 1, :i] = -b.H / h
    V = U.row_join(v)

    check_matrix_zero(C.H * H * C - sp.diag(S, h), "block congruence")
    check_matrix_zero(V * C - W.row_join(v), "translation centre")
    assert exact_zero(C.det() - 1), "unit determinant congruence"

    detH, detS, detG = (sp.factor(M.det()) for M in (H, S, G))
    det_original = sp.factor((H + V.H * V).det())
    det_schur = sp.factor((S + W.H * G * W).det())
    assert exact_zero(det_original - a * det_schur), "bordered determinant identity"
    assert exact_zero(detH - h * detS), "Schur complement determinant"
    assert exact_zero(detG - h / a), "rank-one determinant"

    Ginv = sp.eye(k) + v * v.H / h
    check_matrix_zero(G * Ginv - sp.eye(k), "rank-one inverse")
    adapter = Ginv + W * S.inv() * W.H
    assert exact_zero(det_original - detH * adapter.det()), "existing-Hua adapter"
    return {"k": k, "i": i}


def jacobian_case(rng: random.Random, k: int, i: int) -> dict[str, int]:
    # vec(L Z R) = (R^T tensor L) vec(Z), using column-major vectorisation.
    L = random_invertible(rng, k)
    R = random_invertible(rng, i)
    T = sp.kronecker_product(R.T, L)
    real = T.applyfunc(sp.re)
    imag = T.applyfunc(sp.im)
    real_map = real.row_join(-imag).col_join(imag.row_join(real))
    determinant = real_map.det(method="domain-ge")
    normL2 = sp.simplify(L.det() * sp.conjugate(L.det()))
    normR2 = sp.simplify(R.det() * sp.conjugate(R.det()))
    assert exact_zero(determinant - normL2**i * normR2**k), "real Jacobian exponent"
    return {"k": k, "i": i, "real_dimension": 2 * k * i}


def symbolic_checks() -> dict[str, str]:
    h, a, dH = sp.symbols("h a detH", positive=True)
    k, i = sp.symbols("k i", integer=True, nonnegative=True)
    # Square-root substitution: detG=h/a, detS=detH/h.
    coefficient = a ** (-k - i) * (dH / h) ** (-k - i)
    jacobian = (h / a) ** (-i) * (dH / h) ** k
    target = dH ** (-i) * a ** (-k)
    assert sp.simplify(coefficient * jacobian / target) == 1
    # Existing-Hua adapter needs only one left multiplication, already formalised.
    adapter_coefficient = dH ** (-k - i) * (dH / h) ** k * (h / a) ** k
    assert sp.simplify(adapter_coefficient / target) == 1

    rho, theta, delta = sp.symbols("rho theta delta", positive=True)
    e = sp.symbols("e", integer=True, nonnegative=True)
    direct_majorant = (2 ** (i + 1) / delta) ** (k + i)
    direct_majorant *= rho ** (2 * i * (i + 1)) * theta ** (2 * k * e)
    source_majorant = (2 * rho**2) ** ((i + 1) * i)
    source_majorant *= (2 ** (i + 1) * theta ** (2 * e)) ** k / delta ** (k + i)
    assert sp.simplify(direct_majorant / source_majorant) == 1
    return {
        "complex_change_of_variables": "detG^(-i) detS^k",
        "bordered_integral_coefficient": "detH^(-i) a^(-k)",
        "existing_Hua_adapter_coefficient": "detH^(-i) a^(-k)",
        "source_majorant_constants": "identical",
    }


def constant_checks() -> list[dict[str, int | str]]:
    output = []
    for k in range(1, 4):
        for i in range(4):
            p = k + i
            recurrence = sp.prod(
                sp.pi**k * sp.gamma(p - k - j) / sp.gamma(p - j)
                for j in range(i)
            )
            formula = sp.pi ** (k * i) * sp.prod(
                sp.factorial(j) / sp.factorial(k + j) for j in range(i)
            )
            assert sp.simplify(recurrence - formula) == 0
            output.append({"k": k, "i": i, "C": str(formula)})
    return output


def scalar_example() -> dict[str, str]:
    x, y = sp.symbols("x y", real=True)
    u = x + sp.I * y
    H = sp.Matrix([[3, 1 + sp.I], [1 - sp.I, 2]])
    v = 1 + 2 * sp.I
    V = sp.Matrix([[u, v]])
    determinant = sp.expand((H + V.H * V).det())
    target = 14 + 2 * ((x - sp.Rational(3, 2)) ** 2 + (y - sp.Rational(1, 2)) ** 2)
    assert exact_zero(determinant - target)
    r = sp.symbols("r", real=True, nonnegative=True)
    radial_integral = sp.integrate(2 * sp.pi * r / (14 + 2 * r**2) ** 2, (r, 0, sp.oo))
    assert radial_integral == sp.pi / 28
    return {
        "H": "[[3,1+I],[1-I,2]]",
        "v": "1+2I",
        "determinant": "14 + 2*abs(u-(3+I)/2)^2",
        "integral": str(radial_integral),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    seed = 20261128
    rng = random.Random(seed)
    cases = [bordered_case(rng, k, i) for k in range(1, 4) for i in range(4) for _ in range(3)]
    jacobians = [jacobian_case(rng, k, i) for k in range(1, 4) for i in range(1, 4)]
    report = {
        "status": "PASS",
        "scope": "exact regression checks, not a Lean build or a proof by sampling",
        "sympy_version": sp.__version__,
        "seed": seed,
        "bordered_determinant_cases": len(cases),
        "dimensions": "1 <= k <= 3; 0 <= i <= 3; three trials per pair",
        "identities_per_case": [
            "block congruence", "translation centre", "unit congruence determinant",
            "bordered Schur identity", "detH=h*detS", "detG=h/a",
            "G inverse", "direct adapter to existing Hua bound",
        ],
        "real_jacobian_cases": jacobians,
        "symbolic_cancellations": symbolic_checks(),
        "Hua_constants": constant_checks(),
        "scalar_example": scalar_example(),
    }
    rendered = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
