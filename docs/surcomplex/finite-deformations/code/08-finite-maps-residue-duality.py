#!/usr/bin/env python3
"""Exact finite checks for the examples in surcomplex_finite_maps.tex.

Requires Python 3.9+ and SymPy. These checks verify polynomial identities and
finite series coefficients, not the general Hahn-support or analytic theorems.
"""
from __future__ import annotations

import platform
import sys
from pathlib import Path

try:
    import sympy as s
except ImportError as exc:
    raise SystemExit("SymPy is required: python -m pip install sympy") from exc


def main() -> None:
    tau, sigma, q, x, y, X = s.symbols("tau sigma q x y X")
    mx = s.Matrix([[0, sigma, 0, 0], [1, 0, 0, tau**2],
                   [0, tau, 0, sigma], [0, 0, 1, 0]])
    my = s.Matrix([[0, 0, 0, tau*sigma], [0, 0, tau, 0],
                   [1, 0, 0, tau**2], [0, 1, 0, 0]])
    eye = s.eye(4)
    zero = s.zeros(4)
    checks: list[str] = []

    def check(name: str, condition: bool) -> None:
        if not condition:
            raise AssertionError(name)
        checks.append("PASS: " + name)

    check("multiplication matrices commute", mx*my == my*mx)
    check("F1(Mx, My) = 0", mx**2-tau*my-sigma*eye == zero)
    check("F2(Mx, My) = 0", my**2-tau*mx == zero)
    p = X**4-tau**3*X-sigma*tau**2
    check("characteristic polynomial of My", s.expand(my.charpoly(X).as_expr()-p) == 0)
    mj = 4*mx*my-tau**2*eye
    delta = -27*tau**8-256*sigma**3*tau**2
    check("Jacobian multiplication determinant", s.expand(mj.det()-delta) == 0)
    disc = s.discriminant(p, X)
    check("quartic discriminant", s.expand(disc-tau**4*delta) == 0)

    basis_ops = [eye, mx, my, mx*my]
    unit = s.Matrix([1, 0, 0, 0])
    residue_row = s.Matrix([[0, 0, 0, 1]])
    gram = s.Matrix(4, 4, lambda i,j: (residue_row*basis_ops[i]*basis_ops[j]*unit)[0])
    expected_gram = s.Matrix([[0,0,0,1], [0,0,1,0],
                              [0,1,0,0], [1,0,0,tau**2]])
    check("residue Gram matrix", gram == expected_gram)
    check("integral residue Gram determinant is 1", s.expand(gram.det()) == 1)
    for k, op in enumerate(basis_ops):
        check(f"trace--Jacobian identity on basis vector {k}",
              s.expand((residue_row*op*mj*unit)[0]-s.trace(op)) == 0)
    check("residue of J is 4", (residue_row*mj*unit)[0] == 4)
    check("trace of multiplication by x is zero", s.trace(mx) == 0)
    check("trace of multiplication by y is zero", s.trace(my) == 0)
    check("trace of multiplication by xy is 3 tau^2", s.trace(mx*my) == 3*tau**2)

    # Solve u + 1 = q*u^4 to a fixed order using exact coefficient recursion.
    order = 8
    u = -s.Integer(1)
    u_coeff = []
    for k in range(1, order + 1):
        ck = s.expand(u**4).coeff(q, k-1)
        u += ck*q**k
        u_coeff.append(ck)
    check("small-root defining equation through q^8",
          s.series(u+1-q*u**4, q, 0, order+1).removeO() == 0)
    u_square = s.series(u**2, q, 0, 5).removeO()
    check("first four small-root coefficients", u_coeff[:4] == [1,-4,22,-140])
    check("first terms for x on the small branch",
          u_square == 1-2*q+9*q**2-52*q**3+340*q**4)

    # At sigma=0, the nonzero branches satisfy v^3=1 with y=tau*v.
    v = s.symbols("v")
    branch_j = 4*(tau*v**2)*(tau*v)-tau**2
    check("Jacobian on nonzero sigma=0 branches",
          s.rem(branch_j-3*tau**2, v**3-1, v) == 0)
    check("infinite simple residues cancel for G=1",
          s.simplify(-tau**-2+3/(3*tau**2)) == 0)
    check("simple residues give 1 for G=xy", s.simplify(3*tau**2/(3*tau**2)) == 1)

    # Multiplicity-five leading complete intersection.
    gb = s.groebner([x**2-y**3, x*y], x, y, order="lex")
    standard = [s.Integer(1), x, y, y**2, y**3]
    check("multiplicity-five leading Groebner basis",
          list(gb.polys) == [s.Poly(x**2-y**3, x,y), s.Poly(x*y,x,y), s.Poly(y**4,x,y)])
    jac_five = 2*x**2+3*y**3
    check("Jacobian normal form in the multiplicity-five example",
          gb.reduce(jac_five)[1] == 5*y**3)
    check("all degree-four monomials vanish in the leading algebra",
          all(gb.reduce(x**k*y**(4-k))[1] == 0 for k in range(5)))

    report = [
        "Exact verification report", "=========================",
        f"Python: {platform.python_version()}", f"SymPy: {s.__version__}", "",
        *checks, "", f"Total checks: {len(checks)}; all passed.", "",
        "Small-branch expansion u(q) =", str(u), "",
        "Expansion u(q)^2 through q^4 =", str(u_square), "",
        "Jacobian multiplication determinant =", str(s.factor(mj.det())), "",
        "Residue Gram matrix =", str(gram), "",
        "Scope: exact finite symbolic identities and finite Taylor coefficients.",
        "Not checked: arbitrary Hahn supports, analytic domain arguments, or",
        "formal verification of the general theorems in a proof assistant."
    ]
    text = "\n".join(report) + "\n"
    Path(__file__).with_name("verification_report.txt").write_text(text, encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
