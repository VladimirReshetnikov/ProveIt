#!/usr/bin/env python3
"""Exact finite checks accompanying Beyond-All-Orders Extension Complexity.

These checks verify identities and finite examples, NOT algebraic independence
of surreal monomials, minimum nonnegative rank, or the main infinite families.
Run with Python 3.10+ and SymPy 1.12+: python code/verify.py
"""
from __future__ import annotations
import itertools
import json
import math
import platform
from pathlib import Path
import sympy as sp

RESULTS: list[dict[str, object]] = []

def check(name: str, condition: object, detail: str = "") -> None:
    ok = bool(condition)
    RESULTS.append({"name": name, "passed": ok, "detail": detail})
    if not ok:
        raise AssertionError(name + (": " + detail if detail else ""))

def phi(t: sp.Expr) -> sp.Matrix:
    return sp.Matrix([(1-t*t)/(1+t*t), 2*t/(1+t*t)])

def det3(a: sp.Matrix, b: sp.Matrix, c: sp.Matrix) -> sp.Expr:
    return sp.det(sp.Matrix([[1, a[0], a[1]],
                             [1, b[0], b[1]],
                             [1, c[0], c[1]]]))

def zero(expr: sp.Expr) -> bool:
    return sp.cancel(expr) == 0

def slack(points: list[sp.Matrix]) -> sp.Matrix:
    n = len(points)
    return sp.Matrix(n, n, lambda i, j: sp.cancel(
        det3(points[i], points[(i+1) % n], points[j])))

def main() -> None:
    a, b, c, s = sp.symbols("a b c s", real=True)
    p = phi(s)
    check("circle identity", zero(p.dot(p)-1))
    check("rational inverse", zero(p[1]/(1+p[0])-s))
    check("first-coordinate difference", zero(
        p[0]-phi(a)[0]+2*(s-a)*(s+a)/((1+s*s)*(1+a*a))))
    check("second-coordinate difference", zero(
        p[1]-phi(a)[1]-2*(s-a)*(1-a*s)/((1+s*s)*(1+a*a))))
    check("orientation determinant", zero(det3(phi(a), phi(b), phi(c))
        -4*(b-a)*(c-a)*(c-b)/((1+a*a)*(1+b*b)*(1+c*c))))

    # Increasing finite parameters run around the circle counterclockwise;
    # the closing edge crosses the point excluded by the rational chart.
    params = [sp.Rational(k, 2) for k in range(-4, 4)]
    points = [phi(t) for t in params]
    S = slack(points)
    n = len(points)
    check("rational cyclic octagon slack nonnegativity", all(x >= 0 for x in S))
    check("rational cyclic octagon exact zero pattern", all(
        (S[i,j] == 0) == (j in (i, (i+1) % n))
        for i in range(n) for j in range(n)))
    check("rational cyclic octagon ordinary slack rank", S.rank() == 3)
    check("all increasing triples counterclockwise", all(
        det3(points[i], points[j], points[k]) > 0
        for i, j, k in itertools.combinations(range(n), 3)))

    delta = sp.Rational(1, 10**6)
    changed = [phi(t+delta*(i+1)) for i, t in enumerate(params)]
    SS = slack(changed)
    check("perturbed rational octagon stays on circle", all(z.dot(z) == 1 for z in changed))
    check("perturbed rational octagon zero pattern", all(
        (SS[i,j] == 0) == (j in (i, (i+1) % n))
        for i in range(n) for j in range(n)))
    check("perturbed rational octagon positive nonincident slacks", all(
        SS[i,j] > 0 for i in range(n) for j in range(n)
        if j not in (i, (i+1) % n)))
    check("perturbed rational octagon ordinary slack rank", SS.rank() == 3)

    # Reflection relation: y=x-lambda*u lies between x and its reflection.
    x1, x2, u1, u2, theta = sp.symbols("x1 x2 u1 u2 theta", real=True)
    x, u = sp.Matrix([x1, x2]), sp.Matrix([u1, u2])
    refl = x - 2*x.dot(u)/u.dot(u)*u
    lam = 2*theta*x.dot(u)/u.dot(u)
    check("reflection interpolation", all(zero(t) for t in
          (x-lam*u - ((1-theta)*x+theta*refl))))
    check("reflection preserves Euclidean norm", zero(refl.dot(refl)-x.dot(x)))

    # Arbitrarily scaled, exact nonnegative factors; no optimization solver.
    T = sp.Matrix([[2, 0, 3], [1, 4, 0], [0, 2, 6]])
    U = sp.Matrix([[1, 2, 0, 4], [3, 0, 5, 1], [2, 4, 1, 0]])
    scales = [sp.Rational(10**20), sp.Rational(1, 10**25), sp.Rational(7, 3)]
    T = T * sp.diag(*scales)
    U = sp.diag(*[1/q for q in scales]) * U
    S0 = T*U
    maxima = [max(T[:,j]) for j in range(T.cols)]
    Tn = T*sp.diag(*[1/q for q in maxima])
    Un = sp.diag(*maxima)*U
    check("normalization preserves product", Tn*Un == S0)
    check("normalized first factor lies in [0,1]", all(0 <= t <= 1 for t in Tn))
    check("each normalized column reaches one", all(max(Tn[:,j]) == 1 for j in range(Tn.cols)))
    check("normalized second factor bounded by an original row", all(
        all(Un[l,j] <= S0[next(i for i in range(Tn.rows) if Tn[i,l] == 1),j]
            for j in range(Un.cols)) for l in range(Un.rows)))

    # Formal independent exponent basis, not a numerical radical comparison.
    monomials = [e for e in itertools.product(range(4), repeat=6) if sum(e) <= 3]
    check("finite exponent signatures are distinct", len(monomials) == len(set(monomials)),
          f"{len(monomials)} monomials of total degree at most 3 in six formal generators")

    # Exact combinatorial index check for the regular polygon doubling proof.
    for m in range(2, 13):
        N = 2**m
        indices = {0}
        for k in range(m):
            t = 2**k
            indices |= {2*t-1-j for j in tuple(indices)}
            check(f"reflection index doubling m={m}, stage={k+1}", indices == set(range(2*t)))
        check(f"reflection count m={m}", len(indices) == N)

    bounds = []
    for m in [8, 10, 12, 16, 20, 24]:
        N = 2**m
        root = math.isqrt(N)
        lower = root if root*root == N else root+1
        upper_root = math.isqrt(576*N)
        upper = min(N, upper_root + int(upper_root*upper_root < 576*N))
        bounds.append({"m": m, "n": N, "regular_lower": m,
                       "regular_upper": 2*m, "constructed_lower": lower,
                       "constructed_upper": upper,
                       "ratio_lower_exact": str(sp.Rational(lower, 2*m))})
        check(f"bounds are consistent m={m}", lower <= upper and m <= 2*m <= N)

    payload = {"python": platform.python_version(), "sympy": sp.__version__,
               "checks": len(RESULTS), "passed": sum(r["passed"] for r in RESULTS),
               "scope": "Exact symbolic identities and finite examples only. No computation of minimum nonnegative rank; no Lean verification.",
               "results": RESULTS, "bound_table": bounds}
    out = Path(__file__).resolve().parents[1]/"data"/"verification.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2)+"\n", encoding="utf-8")
    print(f"{payload['passed']}/{payload['checks']} exact finite checks passed.")
    print(f"Python {payload['python']}; SymPy {payload['sympy']}")
    print(out)

if __name__ == "__main__":
    main()
