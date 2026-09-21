#!/usr/bin/env python3
"""Exact finite checks for the accompanying article, not a general Hahn engine.
Run: python verify_examples.py. Requires SymPy (tested with 1.14.0).
"""
from __future__ import annotations
import json
import platform
from pathlib import Path
import sympy as sp

checks: list[dict[str, object]] = []
def check(name: str, result: bool) -> None:
    checks.append({"name": name, "passed": bool(result)})

def equal(a: sp.Expr, b: sp.Expr) -> bool:
    return sp.cancel(a - b) == 0

def run() -> dict[str, object]:
    t, u, x, y, A, B = sp.symbols("t u x y A B")
    q = A * B
    mx = sp.Matrix([[0, 0, 0, 0], [1, 0, 0, q],
                    [0, A, 0, 0], [0, 0, 1, 0]])
    my = sp.Matrix([[0, 0, 0, 0], [0, 0, B, 0],
                    [1, 0, 0, q], [0, 1, 0, 0]])
    zero = sp.zeros(4)
    check("multiplication matrices commute", mx*my - my*mx == zero)
    check("first defining relation", mx**2 - A*my == zero)
    check("second defining relation", my**2 - B*mx == zero)
    lam = sp.Symbol("lambda")
    check("characteristic polynomial x", equal(mx.charpoly(lam).as_expr(),lam*(lam**3-A**2*B)))
    check("characteristic polynomial y", equal(my.charpoly(lam).as_expr(),lam*(lam**3-A*B**2)))
    gram = sp.Matrix([[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,q]])
    check("residue Gram determinant", gram.det() == 1)
    check("adjointness x", mx.T*gram == gram*mx)
    check("adjointness y", my.T*gram == gram*my)
    f = sp.Matrix([x**2-A*y, y**2-B*x])
    transform = sp.Matrix([[x**2+A*y, A**2], [B**2,y**2+B*x]])
    check("separating denominator x", equal((transform*f)[0], x**4-A**2*B*x))
    check("separating denominator y", equal((transform*f)[1], y**4-A*B**2*y))
    determinant = sp.expand(transform.det())
    check("transformation determinant", equal(determinant, x**2*y**2+B*x**3+A*y**3+A*B*x*y-A**2*B**2))
    jac = 4*x*y-A*B
    gb = sp.groebner(list(f), x, y)
    check("determinant modulo ideal", equal(gb.reduce(determinant-A*B*jac)[1],0))
    def residue(p: int, r: int) -> sp.Expr:
        a, b = 2*p+r-3, p+2*r-3
        return A**(a//3)*B**(b//3) if a >= 0 and b >= 0 and a%3 == 0 and b%3 == 0 else sp.S.Zero
    def separating_residue(p: int, r: int) -> sp.Expr:
        result = sp.S.Zero
        for (i,j), coefficient in sp.Poly(x**p*y**r*determinant,x,y).terms():
            # x^-4 y^-4 sum_k (A^2 B)^k x^-3k sum_l (A B^2)^l y^-3l
            if i>=3 and j>=3 and (i-3)%3 == 0 and (j-3)%3 == 0:
                result += coefficient*(A**2*B)**((i-3)//3)*(A*B**2)**((j-3)//3)
        return sp.expand(result)
    for p in range(11):
        for r in range(11):
            multiplication = mx**p * my**r
            check(f"trace-residue-{p}-{r}", equal(sp.trace(multiplication),
                4*residue(p+1,r+1)-A*B*residue(p,r)))
            check(f"torus-residue-{p}-{r}", equal(separating_residue(p,r), residue(p,r)))
    for p,r,want in [(0,0,0),(1,0,0),(0,1,0),(1,1,1)]:
        check(f"basic-residue-{p}-{r}",equal(residue(p,r),sp.sympify(want)))
    check("infinite local weights cancel", equal(-1/q+3/(3*q),0))
    check("Jacobian residue length", equal(4*residue(1,1)-q*residue(0,0),4))
    # Radius-free germ H(t^2): coefficient m is sum n^k for n+2k=m.
    coefficients = [sum(n**((m-n)//2) for n in range(1,m+1) if (m-n)%2==0) for m in range(1,17)]
    direct = sp.series(sum(t**n/(1-n*t**2) for n in range(1,17)),t,0,17).removeO()
    for m,c in enumerate(coefficients,1):
        check(f"radius-free-coefficient-{m}", direct.coeff(t,m)==c)
    check("radius-free-displayed-prefix",coefficients[:8]==[1,1,2,3,5,9,16,31])
    # Finite formal precision examples; no implicit numerical limit.
    for n in range(1,21):
        check(f"geometric-remainder-{n}",equal(1/(1-t)-sum(t**j for j in range(n)),t**n/(1-t)))
    e = sp.series(sp.exp(t+t**2),t,0,9).removeO()
    check("local exp displayed coefficients",all(e.coeff(t,j)==c for j,c in enumerate([1,1,sp.Rational(3,2),sp.Rational(7,6),sp.Rational(25,24)])))
    for j in range(1,9):
        check(f"formal-exp-log-coefficient-{j}", sp.series(sp.log(e),t,0,9).removeO().coeff(t,j)==(1 if j in (1,2) else 0))
    factorial_series = sum(sp.factorial(n)*t**n for n in range(13))
    residual = sp.expand(t**2*sp.diff(factorial_series,t)+(t-1)*factorial_series+1)
    for n in range(13):
        check(f"factorial-ode-{n}",residual.coeff(t,n)==0)
    # Rank-two rational leading monomials use exact integer tuples.
    def valuation(expr: sp.Expr) -> tuple[int,...]:
        num,den=map(lambda z: sp.Poly(z,u,t),sp.fraction(sp.cancel(expr)))
        a=min(num.monoms()); b=min(den.monoms())
        return tuple(i-j for i,j in zip(a,b))
    check("rank leading term",valuation(u+t**100)==(0,100))
    check("rank-crossing cancellation",valuation((1/(1-t)+u)-1/(1-t))==(1,0))
    check("positive-rank tiny quotient",valuation(u/t**100)==(1,-100))
    # Circle t^s contains pole t^a exactly when a>s; lex tuples model a omega+b.
    poles=[(0,sp.Rational(1)),(1,sp.Rational(0))]
    counts=[sum(int(bool(a>s)) for a in poles) for s in [(0,sp.Rational(1,2)),(0,sp.Rational(2)),(2,sp.Rational(0))]]
    check("three normalized contour periods",counts==[2,1,0])
    report={"python":platform.python_version(),"sympy":sp.__version__,"tests":len(checks),
      "passed":sum(bool(c["passed"]) for c in checks),"failures":[c for c in checks if not c["passed"]],
      "radius_free_coefficients_1_to_16":coefficients,
      "scope":"Finite exact identities and illustrative arithmetic; no general Hahn, analytic-germ, or transseries implementation."}
    return report

if __name__ == "__main__":
    output=run()
    print(json.dumps(output,indent=2))
    if output["failures"]:
        raise SystemExit(1)
