#!/usr/bin/env python3
"""Exact finite certificates accompanying the compact-curve Hahn article.

Requires Python 3.10+ and SymPy. These checks verify finite algebraic examples,
not the infinite-support or sheaf-theoretic theorems. No numerical tolerances.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp

checks: list[dict[str, object]] = []

def check(name: str, value: object, expected: object = 0) -> None:
    difference = sp.simplify(value - expected)
    passed = difference == 0
    checks.append({"name": name, "passed": bool(passed)})
    if not passed:
        raise AssertionError(f"{name}: residual {difference}")

def check_matrix(name: str, value: sp.Matrix, expected: sp.Matrix) -> None:
    difference = value - expected
    for i in range(difference.rows):
        for j in range(difference.cols):
            check(f"{name}[{i},{j}]", difference[i, j])


def main() -> None:
    q, t, u, s = sp.symbols("q t u s")
    # Root-free Newton sums versus the logarithmic generating function.
    for m in (2, 3):
        c = sp.symbols(f"c1:{m + 1}")
        rev = 1 + sum(c[j - 1] * q**j for j in range(1, m + 1))
        series = sp.series(sp.log(rev), q, 0, 10).removeO().expand()
        p: dict[int, sp.Expr] = {}
        for k in range(1, 10):
            if k <= m:
                p[k] = -sum(c[j-1]*p[k-j] for j in range(1, k)) - k*c[k-1]
            else:
                p[k] = -sum(c[j-1]*p[k-j] for j in range(1, m+1))
            p[k] = sp.expand(p[k])
            check(f"Newton/log degree {m}, power {k}", series.coeff(q, k), -p[k]/k)

    # Genus-two curve y^2 = 1+x^5, local pair of roots +/-sqrt(s).
    inv_y = sp.series((1 + u**5)**sp.Rational(-1, 2), u, 0, 43).removeO()
    abel = []
    for j in (0, 1):
        coeffs = sp.expand(u**j * inv_y)
        val = sp.expand(sum(coeffs.coeff(u, 2*r-1)*s**r/sp.Integer(r)
                            for r in range(1, 20)))
        abel.append(val)
    check("genus2 A(dx/y), s^3", abel[0].coeff(s, 3), -sp.Rational(1, 6))
    check("genus2 A(dx/y), s^8", abel[0].coeff(s, 8), -sp.Rational(5, 128))
    check("genus2 A(x dx/y), s", abel[1].coeff(s, 1), 1)
    check("genus2 A(x dx/y), s^6", abel[1].coeff(s, 6), sp.Rational(1, 16))
    check("genus2 A(x dx/y), s^11", abel[1].coeff(s, 11), sp.Rational(35, 1408))

    # Universal two-term finite model: d=h=diag(0,1,1), one harmonic
    # coordinate in each degree. This is an algebraic test, not a curve model.
    d = sp.diag(0, 1, 1)
    h = d
    i = sp.Matrix([1, 0, 0])
    p = i.T
    a = sp.Matrix([[0, 1, 2], [3, 1, 0], [1, -1, 2]])
    b = sp.Matrix([[1, 0, -1], [0, 2, 1], [1, 0, 0]])
    delta = t*a + t**2*b
    D = d + delta
    T = (sp.eye(3) + h*delta).inv()
    B = p*delta*T*i
    I0 = T*i
    P1 = p*(sp.eye(3) + delta*h).inv()
    H = T*h
    check_matrix("transferred differential", D*I0, i*B)
    check_matrix("degree-zero contraction", H*D, sp.eye(3)-I0*p)
    check_matrix("degree-one contraction", D*H, sp.eye(3)-i*P1)
    check_matrix("projection is chain map", P1*D, B*p)
    schur = D[:1, :1] - D[:1, 1:] * D[1:, 1:].inv() * D[1:, :1]
    check_matrix("Schur complement", B, schur)
    truncated = sum(((-1)**n * p*delta*(h*delta)**n*i for n in range(5)),
                    sp.zeros(1, 1))
    for k in range(1, 6):
        check(f"Neumann coefficient t^{k}",
              sp.series(B[0], t, 0, 6).removeO().coeff(t, k),
              sp.expand(truncated[0]).coeff(t, k))

    result = {
        "description": "Exact finite checks; not a proof assistant or novelty test.",
        "sympy_version": sp.__version__,
        "total": len(checks),
        "passed": sum(x["passed"] for x in checks),
        "checks": checks,
        "hyperelliptic_abel_polynomials": [str(x) for x in abel],
        "finite_obstruction_matrix": str(sp.factor(B[0])),
    }
    out = Path(__file__).with_name("verification_results.json")
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"{result['passed']}/{result['total']} checks passed; wrote {out.name}")
    print("Finite obstruction B(t) =", result["finite_obstruction_matrix"])

if __name__ == "__main__":
    main()
