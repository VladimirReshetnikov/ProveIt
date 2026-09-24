#!/usr/bin/env python3
"""Exact finite checks for the worked examples in the accompanying article.

Requires Python 3.10+ and SymPy. Run:
    python verify_examples.py

These checks concern symbolic formulas and finite Taylor coefficients. They do
not implement arbitrary Hahn fields or formally verify the general theorems.
"""
from __future__ import annotations

import sys
from pathlib import Path

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc


def main() -> None:
    A, B, lam = sp.symbols("A B lambda")
    q = A * B
    eye = sp.eye(4)
    zero = sp.zeros(4)
    mx = sp.Matrix([[0, 0, 0, 0], [1, 0, 0, q],
                    [0, A, 0, 0], [0, 0, 1, 0]])
    my = sp.Matrix([[0, 0, 0, 0], [0, 0, B, 0],
                    [1, 0, 0, q], [0, 1, 0, 0]])
    gram = sp.Matrix([[0, 0, 0, 1], [0, 0, 1, 0],
                      [0, 1, 0, 0], [1, 0, 0, q]])
    residue_row = sp.Matrix([[0, 0, 0, 1]])
    unit_vector = sp.Matrix([1, 0, 0, 0])
    report: list[str] = [
        "EXACT SYMBOLIC VERIFICATION REPORT",
        "Article: Infinitesimal Analytic Geometry over the Surcomplex Numbers",
        f"Python: {sys.version.split()[0]}",
        f"SymPy: {sp.__version__}",
        "",
    ]
    checks = 0

    def check(name: str, expression: object, expected: object = 0) -> None:
        nonlocal checks
        difference = expression - expected
        if isinstance(difference, sp.MatrixBase):
            valid = all(sp.simplify(entry) == 0 for entry in difference)
        else:
            valid = sp.simplify(difference) == 0
        if not valid:
            raise AssertionError(f"Failed: {name}; difference={difference}")
        checks += 1
        report.append(f"PASS: {name}")

    check("coordinate matrices commute", mx * my - my * mx, zero)
    check("x^2 = A y", mx**2, A * my)
    check("y^2 = B x", my**2, B * mx)
    check("x characteristic polynomial", mx.charpoly(lam).as_expr(), lam * (lam**3 - A**2 * B))
    check("y characteristic polynomial", my.charpoly(lam).as_expr(), lam * (lam**3 - A * B**2))
    check("residue Gram determinant", gram.det(), 1)
    check("x self-adjoint for residue pairing", mx.T * gram, gram * mx)
    check("y self-adjoint for residue pairing", my.T * gram, gram * my)
    mxy = mx * my
    jacobian = 4 * mxy - q * eye
    check("residue of Jacobian equals length", (residue_row * jacobian * unit_vector)[0], 4)
    check("trace of xy", sp.trace(mxy), 3 * q)
    check("origin idempotent", (eye - mxy / q)**2, eye - mxy / q)
    check("residue weight at the origin", (residue_row * (eye - mxy / q) * unit_vector)[0], -1 / q)

    def residue_monomial(p: int, r: int) -> sp.Expr:
        """Residue of x**p*y**r from the coefficient-extraction formula."""
        k_num = 2 * p + r - 3
        ell_num = p + 2 * r - 3
        if k_num < 0 or ell_num < 0 or k_num % 3 or ell_num % 3:
            return sp.Integer(0)
        return A ** (k_num // 3) * B ** (ell_num // 3)

    # Exact comparison for 121 monomials; these are consistency checks, not
    # an inference from finitely many cases to a general identity.
    for p in range(11):
        for r in range(11):
            operator = mx**p * my**r
            check(f"residue of x^{p} y^{r}",
                  (residue_row * operator * unit_vector)[0], residue_monomial(p, r))
            check(f"trace--Jacobian for x^{p} y^{r}", sp.trace(operator),
                  4 * residue_monomial(p + 1, r + 1) - q * residue_monomial(p, r))

    x, y, t = sp.symbols("x y t")
    # The coefficient of t in the radius-free example's total residue comes
    # only from k=1, ell=0 and the coefficient 1/(1-x-y) of t in E_1.
    geometric_degree_four = sum((x + y)**j for j in range(5))
    coefficient = sp.expand(geometric_degree_four).coeff(x, 3).coeff(y, 1)
    check("radius-free example: coefficient of t in Res_F(1)", -coefficient, -4)
    # Scalar boundary case for the strict factor-two stability threshold.
    c = sp.symbols("c", nonzero=True)
    check("scalar sharpness example after perturbation", (x**2 - c**2) + c**2, x**2)
    check("unperturbed scalar discriminant", sp.discriminant(x**2 - c**2, x), 4 * c**2)
    check("perturbed scalar discriminant", sp.discriminant(x**2, x), 0)

    report.extend(["", f"All {checks} exact checks passed.",
                   "The general support, flatness, residue, and Nullstellensatz proofs",
                   "are mathematical arguments in the article, not machine-checked proofs."])
    output = Path(__file__).with_name("verification_report.txt")
    output.write_text("\n".join(report) + "\n", encoding="utf-8")
    print(f"All {checks} exact checks passed. Report: {output}")
    print(f"Gram determinant: {sp.factor(gram.det())}")
    print(f"Characteristic polynomial of M_x: {sp.factor(mx.charpoly(lam).as_expr())}")


if __name__ == "__main__":
    main()
