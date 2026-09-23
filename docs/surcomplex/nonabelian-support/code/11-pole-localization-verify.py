#!/usr/bin/env python3
"""Exact finite checks for Pole Localization and Omnific Interpolation.

Requires Python 3.9+ and SymPy. Run: python verify.py
These checks are not a verification of infinite Hahn support arguments,
ordinary Weierstrass existence, sheaf cohomology, or publication priority.
"""
from __future__ import annotations

import argparse
import json
import platform
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Dict, List

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install with: python -m pip install sympy") from exc

RESULTS: List[Dict[str, Any]] = []


def check(name: str, condition: bool, category: str) -> None:
    """Record a check and fail immediately on a false exact identity."""
    passed = bool(condition)
    RESULTS.append({"name": name, "category": category, "passed": passed})
    if not passed:
        raise AssertionError("Exact check failed: " + name)


def is_zero(expression: Any) -> bool:
    if isinstance(expression, sp.MatrixBase):
        return all(sp.simplify(item) == 0 for item in expression)
    return sp.simplify(expression) == 0


def matrix_checks() -> None:
    f, s, a = sp.symbols("f s a", nonzero=True)
    T = sp.Matrix([[f, 0], [s, 1 / f]])
    G = sp.Matrix([[1, a], [0, 1]])
    disk = sp.Matrix([[f, a * f], [s, 1 / f + a * s]])
    check("rank_two_frame_product", is_zero(T * G - disk), "matrix")
    check("rank_two_determinant", disk.det() == 1, "matrix")
    check("rank_two_inverse", is_zero(T.inv() - sp.Matrix([[1/f, 0], [-s, f]])), "matrix")
    column = sp.Matrix([f, s])
    row = sp.Matrix([[-s, f]])
    check("extension_row_annihilates_column", is_zero(row * column), "matrix")
    check("local_second_column_maps_to_one", is_zero(row * disk[:, 1] - sp.ones(1, 1)), "matrix")
    check("local_lifts_differ_by_cocycle", is_zero(disk[:, 1] - T[:, 1] - a * column), "matrix")
    d1 = sp.Matrix([[f, s]])
    d2 = sp.Matrix([-s, f])
    check("koszul_differentials_compose_to_zero", is_zero(d1 * d2), "matrix")

    # a=t/(z-n), b=t^(1/n), c=t*phi. No fractional-power simplifications needed.
    a, b, c = sp.symbols("a b c")
    e12, e23, e13 = (sp.zeros(3) for _ in range(3))
    e12[0, 1] = e23[1, 2] = e13[0, 2] = 1
    G3 = sp.eye(3) + a * e12 + b * e23
    H = sp.eye(3) + b * e23
    C = sp.eye(3) + (c - a) * e12
    L = sp.eye(3) - c * e12
    R = H.inv() * C
    Q = sp.eye(3) - a * b * e13
    P = sp.eye(3) + a * e12 - a * b * e13
    check("rank_three_polar_factor", is_zero(G3 * H.inv() - P), "matrix")
    check("rank_three_reduction_LGR", is_zero(L * G3 * R - Q), "matrix")
    for label, matrix in (("G", G3), ("H", H), ("C", C), ("L", L), ("R", R), ("Q", Q)):
        check("rank_three_det_" + label, sp.simplify(matrix.det()) == 1, "matrix")
    T3 = sp.Matrix([[f, 0, 0], [0, 1, 0], [s, 0, 1/f]])
    B0 = T3 * L
    Bn = T3 * Q * R.inv()
    check("original_rank_three_frame_equation", is_zero(B0 * G3 - Bn), "matrix")
    check("original_rank_three_frame_determinant", is_zero(Bn.det() - 1), "matrix")


def symmetric_power(matrix: sp.MatrixBase, degree: int) -> sp.Matrix:
    """Sym^degree on basis e1^(degree-j)*e2^j, with images as columns."""
    if matrix.shape != (2, 2) or degree < 0:
        raise ValueError("Expected a 2x2 matrix and a nonnegative degree.")
    x, y = sp.symbols("X Y")
    a, b, c, d = list(matrix)
    columns = []
    for j in range(degree + 1):
        poly = sp.Poly(sp.expand((a*x+c*y)**(degree-j) * (b*x+d*y)**j), x, y)
        columns.append(sp.Matrix([poly.coeff_monomial(x**(degree-i)*y**i)
                                  for i in range(degree+1)]))
    return sp.Matrix.hstack(*columns)


def representation_checks() -> None:
    a = sp.symbols("a")
    M, N = sp.Matrix([[2, 1], [1, 1]]), sp.Matrix([[1, 3], [0, 1]])
    for degree in range(1, 7):
        rM, rN = symmetric_power(M, degree), symmetric_power(N, degree)
        check("sym_%d_homomorphism" % degree,
              is_zero(symmetric_power(M*N, degree) - rM*rN), "representation")
        check("sym_%d_determinant" % degree, rM.det() == 1, "representation")
        check("sym_%d_inverse" % degree,
              is_zero(symmetric_power(M.inv(), degree)*rM - sp.eye(degree+1)), "representation")
        U = symmetric_power(sp.Matrix([[1, a], [0, 1]]), degree)
        D = U.diff(a).subs(a, 0)
        expD = sp.zeros(degree+1)
        for k in range(degree+1):
            expD += a**k * D**k / sp.factorial(k)
        check("sym_%d_nilpotent_exponential" % degree, is_zero(U-expD), "representation")
        check("sym_%d_exact_nilpotency" % degree,
              D**(degree+1) == sp.zeros(degree+1) and D**degree != sp.zeros(degree+1),
              "representation")
        C = sp.diag(*[1/sp.factorial(j) for j in range(degree+1)])
        J = sp.zeros(degree+1)
        for j in range(degree):
            J[j, j+1] = 1
        check("sym_%d_Jordan_conjugacy" % degree, is_zero(C.inv()*D*C-J), "representation")


def principal_part(expression: Any, z: sp.Symbol, point: int) -> Any:
    u = sp.symbols("u")
    laurent = sp.series(expression.subs(z, u+point), u, 0, 1).removeO().expand()
    negative = sp.Add(*(term for term in sp.Add.make_args(laurent)
                        if term.as_powers_dict().get(u, sp.Integer(0)) < 0))
    return sp.simplify(negative.subs(u, z-point))


def pole_checks() -> None:
    z = sp.symbols("z")
    configurations = [([-1, 0, 2], [1, 1, 1]), ([-2, 0, 3], [1, 2, 3])]
    for number, (nodes, orders) in enumerate(configurations, 1):
        f = sp.prod((z-node)**order for node, order in zip(nodes, orders))
        Fs, ps = [], []
        for j, (node, order) in enumerate(zip(nodes, orders)):
            u = z-node
            p = sp.Rational(j+2, j+1) * (1+u/7+u*u/11) / u**order
            q = principal_part(-1/(f*f*p), z, node)
            F = sp.cancel(f*q)
            ps.append(p)
            Fs.append(F)
            prefix = "poles_%d_node_%d_" % (number, j)
            check(prefix+"F_entire_polynomial", sp.denom(F).is_number, "pole_cancellation")
            check(prefix+"fp_regular", is_zero(principal_part(f*p, z, node)), "pole_cancellation")
            check(prefix+"diagonal_cancellation", is_zero(principal_part(1/f+p*F, z, node)), "pole_cancellation")
            check(prefix+"diagonal_value_nonzero", sp.simplify(F.subs(z, node)) != 0, "pole_cancellation")
        for i, node in enumerate(nodes):
            for j, F in enumerate(Fs):
                if i != j:
                    prefix = "poles_%d_cross_%d_%d_" % (number, i, j)
                    check(prefix+"vanishing", is_zero(F.subs(z, node)), "pole_cancellation")
                    check(prefix+"pole_cancelled", is_zero(principal_part(ps[i]*F, z, node)), "pole_cancellation")


def cardinal_checks() -> None:
    z = sp.symbols("z")
    nodes = [0]
    for k in range(1, 5):
        nodes.extend([k, -k])
    f = sp.sin(sp.pi*z)
    ell1 = f / (sp.pi*z)
    for i, node in enumerate(nodes):
        ell = sp.sin(sp.pi*(z-node))/(sp.pi*(z-node))
        check("cardinal_formula_%d" % i,
              is_zero(ell - f/(f.diff(z).subs(z,node)*(z-node))), "cardinal")
        for j, other in enumerate(nodes):
            value = sp.limit(ell, z, other) if other == node else ell.subs(z, other)
            check("cardinal_value_%d_%d" % (i,j), value == int(i == j), "cardinal")
        if node:
            derivative = sp.simplify(ell1.diff(z).subs(z, node))
            expected = sp.Integer(-1)**node / node
            leading = sp.Integer(-1)**(node+1) * node
            check("root_derivative_%d" % i, is_zero(derivative-expected), "cardinal")
            check("root_leading_balance_%d" % i, is_zero(derivative*leading+1), "cardinal")


def profile_checks() -> None:
    """Only finite sanity checks; not proofs of infinite well-ordering."""
    profile = [sp.Rational(1,n) for n in range(1,65)]
    check("finite_profile_decreases", all(x>y for x,y in zip(profile,profile[1:])), "finite_support_sanity")
    reversed_sign = [-x for x in profile]
    check("finite_negative_profile_increases", all(x<y for x,y in zip(reversed_sign,reversed_sign[1:])), "finite_support_sanity")
    for n in (1,2,5,17,64):
        translated = [profile[n-1]-x for x in profile]
        check("translated_support_%d" % n, all(x<y for x,y in zip(translated,translated[1:])), "finite_support_sanity")
    alpha, delta = sp.Rational(3,2), sp.Rational(3,4)
    check("rank_three_balanced_budget", max(delta,alpha-delta) == sp.Rational(3,4), "finite_support_sanity")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification_results.json"))
    args = parser.parse_args()
    failure = None
    try:
        matrix_checks()
        representation_checks()
        pole_checks()
        cardinal_checks()
        profile_checks()
    except Exception as exc:
        failure = "%s: %s" % (type(exc).__name__, exc)
    report = {
        "status": "PASS" if failure is None else "FAIL",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "checks_run": len(RESULTS),
        "checks_passed": sum(int(item["passed"]) for item in RESULTS),
        "categories": dict(Counter(item["category"] for item in RESULTS)),
        "limitation": "Exact finite checks only; not an infinite-support proof or Lean verification.",
        "failure": failure,
        "checks": RESULTS,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("%s: %d/%d exact finite checks; SymPy %s" %
          (report["status"], report["checks_passed"], report["checks_run"], sp.__version__))
    if failure:
        print(failure, file=sys.stderr)
    print("Report:", args.output.resolve())
    return int(failure is not None)


if __name__ == "__main__":
    raise SystemExit(main())
