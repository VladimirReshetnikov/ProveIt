#!/usr/bin/env python3
"""Exact finite checks for the examples in Surcomplex Analysis.

Requires Python 3.10+ and SymPy. No floating-point or numerical tolerance is used.
These calculations do NOT machine-verify the general theorems of the article.
Run: python verify_examples.py --output verification_report.txt
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc


def trunc(expr: sp.Expr, variable: sp.Symbol, order: int) -> sp.Expr:
    """Return the exact expansion through powers strictly below 'order'."""
    return sp.expand(sp.series(expr, variable, 0, order).removeO())


def require_zero(expr: sp.Expr, description: str, lines: list[str]) -> None:
    value = sp.simplify(expr)
    if value != 0:
        raise AssertionError(f"{description}: nonzero remainder {value}")
    lines.append(f"PASS: {description}")


def run_checks() -> str:
    lines = [
        "Surcomplex Analysis: exact finite verification report",
        f"Python {sys.version.split()[0]}; SymPy {sp.__version__}",
        "All checks use symbolic exact arithmetic.",
        "They verify example expansions, not general Hahn-support theorems.",
        "",
    ]
    s, t, u, tau = sp.symbols("s t u tau")

    # Root splitting for sin(z)^2 - t with s = sqrt(t).
    arcsin_series = trunc(sp.asin(s), s, 10)
    quoted_root = s + s**3 / 6 + 3*s**5 / 40 + 5*s**7 / 112
    require_zero(trunc(arcsin_series - quoted_root, s, 9),
                 "quoted arcsin(s) coefficients through s^7", lines)
    require_zero(trunc(sp.sin(arcsin_series)**2 - s**2, s, 12),
                 "sin(arcsin(s) truncated through s^9)^2 - s^2 = O(s^12)", lines)
    square = trunc(arcsin_series**2, s, 10)
    quoted_square = s**2 + s**4/3 + 8*s**6/45 + 4*s**8/35
    require_zero(square - quoted_square,
                 "prepared polynomial coefficients through t^4, where t=s^2", lines)
    lines.append(f"arcsin(s) = {arcsin_series} + O(s^10)")
    lines.append(f"arcsin(s)^2 = {square} + O(s^10)")
    lines.append("")

    # Infinite residues cancel; all comparisons are formal exact series.
    residue_sum = (sp.exp(s) - sp.exp(-s)) / (2*s)
    expected = sum(s**(2*n)/sp.factorial(2*n+1) for n in range(7))
    require_zero(trunc(residue_sum, s, 14) - expected,
                 "moving-pole residue sum equals sum t^n/(2n+1)! through t^6", lines)
    for n in range(7):
        coefficient_residue = sp.residue(sp.exp(u) / u**(2*n+2), u, 0)
        require_zero(coefficient_residue - 1/sp.factorial(2*n+1),
                     f"coefficientwise contour residue at t^{n}", lines)
    lines.append("")

    # General simple-root formula: f(c)=0, f'(c)=a.
    a = sp.symbols("a", nonzero=True)
    f2, g0, g1 = sp.symbols("f2 g0 g1")
    b1 = -g0/a
    b2 = g0*g1/a**2 - f2*g0**2/(2*a**3)
    h = b1*tau + b2*tau**2
    error = a*h + f2*h**2/2 + tau*(g0+g1*h)
    require_zero(trunc(error, tau, 3),
                 "general second-order lifted simple-root formula, modulo tau^3", lines)
    lines.append("")

    # A genuinely nontrivial finite preparation recursion:
    # H(u,t)=u^2+t*(1+u+u^3)+t^2*(u^4-u).
    # P=u^2+A (deg_u A<2), Q=1+B; both A,B start at t.
    m, order = 2, 6
    E: dict[int, sp.Expr] = {1: 1+u+u**3, 2: u**4-u}
    A: dict[int, sp.Expr] = {}
    B: dict[int, sp.Expr] = {}
    for n in range(1, order+1):
        hn = sp.expand(E.get(n, sp.S.Zero)
                       - sum(A[j]*B[n-j] for j in range(1,n)))
        poly = sp.Poly(hn, u)
        A[n] = sp.expand(sum(poly.nth(j)*u**j for j in range(m)))
        B[n] = sp.cancel((hn-A[n])/u**m)
        if sp.Poly(A[n],u).degree() >= m:
            raise AssertionError("Preparation remainder has excessive u-degree")
    P = u**m + sum(A[n]*t**n for n in A)
    Q = 1 + sum(B[n]*t**n for n in B)
    H = u**m + sum(E[n]*t**n for n in E)
    require_zero(trunc(P*Q-H, t, order+1),
                 "preparation recursion for polynomial test family through t^6", lines)
    lines.append("Test family H=u^2+t*(1+u+u^3)+t^2*(u^4-u)")
    lines.append(f"Prepared P through t^6: {sp.collect(sp.expand(P),t)}")
    lines.append(f"Unit Q through t^6: {sp.collect(sp.expand(Q),t)}")
    lines.extend(["", "RESULT: all exact finite checks passed."])
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Also write the report to this UTF-8 text file")
    args = parser.parse_args()
    report = run_checks()
    print(report, end="")
    if args.output is not None:
        args.output.write_text(report, encoding="utf-8")


if __name__ == "__main__":
    main()
