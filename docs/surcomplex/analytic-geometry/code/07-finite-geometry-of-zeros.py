#!/usr/bin/env python3
"""Exact checks for the length-five example in surcomplex_finite_geometry.tex.

Requires Python 3.9+ and SymPy. No network access is used. This script checks
finite polynomial identities, not the general mathematical proofs.
Run: python verify_examples.py --output verification_report.txt
"""
from __future__ import annotations

import argparse
import platform
from pathlib import Path
from typing import List

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_report.txt"))
    args = parser.parse_args()
    lines: List[str] = [
        "FINITE GEOMETRY OF HAHN-COHERENT SURCOMPLEX ZEROS",
        "Exact symbolic verification report",
        f"Python: {platform.python_version()}",
        f"SymPy: {sp.__version__}",
        "Arithmetic: symbolic integers and rationals; no numerical tolerances.",
        "",
    ]
    count = 0

    def check(name: str, value: object) -> None:
        nonlocal count
        if isinstance(value, sp.MatrixBase):
            ok = all(sp.cancel(v) == 0 for v in value)
        elif isinstance(value, (bool, sp.logic.boolalg.BooleanAtom)):
            ok = bool(value)
        else:
            ok = sp.cancel(value) == 0
        if not ok:
            raise AssertionError(f"FAILED: {name}\nResidual: {value}")
        count += 1
        lines.append(f"PASS {count:02d}: {name}")

    s, u, X, Y, a, eta = sp.symbols("s u X Y a eta")
    alpha, beta = sp.symbols("alpha beta")
    I = sp.eye(5)
    e0 = I[:, 0]
    Mx = sp.Matrix([
        [0, u, 0, 0, s],
        [0, 0, u, 0, 0],
        [0, 0, 0, u, 0],
        [0, 0, 0, 0, 1],
        [1, 0, 0, 0, 0],
    ])
    My = sp.Matrix([
        [0, 0, 0, 0, u],
        [1, 0, 0, -s, 0],
        [0, 1, 0, 0, 0],
        [0, 0, 1, 0, 0],
        [0, 0, 0, u, 0],
    ])
    basis = [I, My, My**2, My**3, Mx]
    names = ["1", "y", "y^2", "y^3", "x"]
    check("Mx My = u I", Mx * My - u * I)
    check("Mx and My commute", Mx * My - My * Mx)
    check("Mx^2 - My^3 = s I", Mx**2 - My**3 - s * I)
    check("My^4 = u Mx - s My", My**4 - u * Mx + s * My)
    for j, B in enumerate(basis):
        check(f"Cyclic basis vector for {names[j]}", B * e0 - I[:, j])

    px = X**5 - s * X**3 - u**3
    py = Y**5 + s * Y**2 - u**2
    check("Characteristic polynomial of Mx", Mx.charpoly(X).as_expr() - px)
    check("Characteristic polynomial of My", My.charpoly(Y).as_expr() - py)
    J = 2 * Mx**2 + 3 * My**3
    delta = 3125 * u**6 - 108 * s**5
    check("Jacobian normal form J = 2s + 5y^3", J - 2 * s * I - 5 * My**3)
    check("Full collision determinant", J.det() - delta)
    check("Projected y discriminant includes extra u^2", sp.discriminant(py, Y) - u**2 * delta)
    check("Five-point collision determinant at u=0, s!=0", delta.subs(u, 0) + 108 * s**5)

    lam = sp.Matrix([[0, 0, 0, 1, 0]])
    W = sp.Matrix(5, 5, lambda i, j: (lam * basis[i] * basis[j] * e0)[0])
    expected_W = sp.Matrix([
        [0, 0, 0, 1, 0],
        [0, 0, 1, 0, 0],
        [0, 1, 0, 0, 0],
        [1, 0, 0, -s, 0],
        [0, 0, 0, 0, 1],
    ])
    check("Displayed residue Gram matrix", W - expected_W)
    check("Residue Gram determinant is identically one", W.det() - 1)
    check("Mx is self-adjoint for the residue form", Mx.T * W - W * Mx)
    check("My is self-adjoint for the residue form", My.T * W - W * My)
    check("Residue of the Jacobian is five", (lam * J * e0)[0] - 5)
    for name, B in zip(names, basis):
        check(f"Trace-Jacobian identity for {name}", sp.trace(B) - (lam * B * J * e0)[0])
    trace_gram = sp.Matrix(5, 5, lambda i, j: sp.trace(basis[i] * basis[j]))
    check("Trace Gram matrix is W times multiplication by J", trace_gram - W * J)
    check("Trace Gram determinant degenerates precisely at collision", trace_gram.det() - delta)
    adjJ = J.adjugate()
    for name, B in zip(names, basis):
        check(f"Simple-root residue trace formula, denominator cleared, for {name}",
              sp.trace(B * adjJ) - delta * (lam * B * e0)[0])

    sc = -sp.Rational(5, 2) * a**6
    uc = eta * a**5
    xc, yc = eta * a**3, a**2
    eta_relation = eta**2 + sp.Rational(3, 2)
    check("Explicit collision solves F1", sp.rem(xc**2 - yc**3 - sc, eta_relation, eta))
    check("Explicit collision solves F2", xc * yc - uc)
    check("Explicit collision has zero Jacobian", sp.rem(2*xc**2 + 3*yc**3, eta_relation, eta))
    check("Explicit collision is on the discriminant", sp.rem(delta.subs({s: sc, u: uc}), eta_relation, eta))
    q_collision = Y**5 - sp.Rational(5, 2)*Y**2 + sp.Rational(3, 2)
    check("Collision quintic factorization",
          q_collision - (Y-1)**2 * (2*Y**3+4*Y**2+6*Y+3)/2)
    check("Collision has exactly one repeated root", sp.gcd(q_collision, sp.diff(q_collision, Y)) - (Y-1))
    check("That repeated root has order exactly two", sp.diff(q_collision, Y, 2).subs(Y, 1) - 15)

    def exponents(d: sp.Expr, normalization: sp.Expr) -> sp.Matrix:
        return sp.Matrix([5*d-normalization, alpha+2*d-normalization, 2*beta-normalization])

    check("Two-root scale exponents",
          exponents(beta-alpha/2, 2*beta) - sp.Matrix([3*beta-5*alpha/2, 0, 0]))
    check("Three-root scale exponents",
          exponents(alpha/3, 5*alpha/3) - sp.Matrix([0, 0, 2*beta-5*alpha/3]))
    check("Five-root scale exponents",
          exponents(2*beta/5, 2*beta) - sp.Matrix([0, alpha-6*beta/5, 0]))
    check("Balanced residual quintic is squarefree", sp.discriminant(Y**5+Y**2-1, Y) - 3017)

    lines.extend([
        "",
        f"ALL {count} CHECKS PASSED.",
        "",
        "Key exact outputs:",
        f"chi_x(X) = {px}",
        f"chi_y(Y) = {py}",
        f"det(m_J) = {delta}",
        f"disc_y = {sp.factor(sp.discriminant(py, Y))}",
        "det(residue Gram matrix) = 1",
        f"det(trace Gram matrix) = {sp.factor(trace_gram.det())}",
        "Lambda(1), Lambda(y), Lambda(y^2), Lambda(y^3), Lambda(x) = 0, 0, 0, 1, 0",
        "Lambda(J) = 5",
        "balanced residual discriminant = 3017",
        "",
        "These are exact checks of the explicit finite example. They do not",
        "constitute proof-assistant verification of the general Hahn, analytic,",
        "homological, Nullstellensatz, or residue theorems in the article.",
    ])
    report = "\n".join(lines) + "\n"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(report, encoding="utf-8")
    print(report, end="")


if __name__ == "__main__":
    main()
