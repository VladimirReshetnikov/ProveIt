#!/usr/bin/env python3
"""Exact finite checks accompanying Surcomplex_Gamma_Zeta_and_RH.tex.

These checks are not a proof of RH, a computation of infinite surreals,
or a proof-assistant verification of the article's general theorems.
The JSON report records individual finite algebraic checks and versions.
"""
from __future__ import annotations

import argparse
import json
import platform
from pathlib import Path
from typing import Any

import sympy as sp


def run_checks() -> dict[str, Any]:
    results: list[dict[str, Any]] = []

    def check(name: str, residual: sp.Expr | bool) -> None:
        if isinstance(residual, bool):
            ok = residual
            remainder = "0" if ok else "condition is false"
        else:
            reduced = sp.expand(residual)
            ok = reduced == 0
            remainder = str(reduced)
        results.append({"name": name, "passed": bool(ok), "residual": remainder})

    r = sp.Symbol("r")
    a, b, c = sp.symbols("a b c")
    expected = [sp.Rational(1, 12), -sp.Rational(1, 360),
                sp.Rational(1, 1260), -sp.Rational(1, 1680),
                sp.Rational(1, 1188), -sp.Rational(691, 360360)]
    coefficients = [sp.bernoulli(2*k)/(2*k*(2*k-1)) for k in range(1, 7)]
    for k, (actual, want) in enumerate(zip(coefficients, expected), start=1):
        check(f"Stirling coefficient B_{2*k}/({2*k}*{2*k-1})", actual-want)

    # S_6(z+1)-S_6(z)-log(z), using r=1/z. The first untested
    # asymptotic coefficient is intentionally nonzero at degree 14.
    shift_defect = (1/r+sp.Rational(1, 2))*sp.log(1+r)-1
    for k, ck in enumerate(coefficients, start=1):
        power = 2*k-1
        shift_defect += ck*((r/(1+r))**power-r**power)
    defect_poly = sp.series(shift_defect, r, 0, 15).removeO().expand()
    for k in range(14):
        check(f"Six-term Stirling recurrence, coefficient r^{k}",
              defect_poly.coeff(r, k))
    check("First omitted recurrence coefficient is 1/12, not zero",
          defect_poly.coeff(r, 14)-sp.Rational(1, 12))

    def q_coefficient(n: int, x: sp.Expr, y: sp.Expr) -> sp.Expr:
        return ((-1)**(n+1) * (sp.bernoulli(n+1, x)-sp.bernoulli(n+1, y))
                / (n*(n+1)))

    for n in range(1, 11):
        qab = q_coefficient(n, a, b)
        check(f"Ratio cocycle coefficient {n}",
              qab+q_coefficient(n, b, c)-q_coefficient(n, a, c))
        check(f"Ratio R_1,0 logarithm coefficient {n}",
              q_coefficient(n, sp.Integer(1), sp.Integer(0)))
        # Coefficient of r^n in Q(r/(1+r))-Q(r).
        lhs = sum(q_coefficient(j, a, b)*(-1)**(n-j)*sp.binomial(n-1, n-j)
                  for j in range(1, n+1)) - qab
        rhs = sp.Rational((-1)**(n+1), n)*(a**n-b**n-(a-b))
        check(f"Symbolic normalized ratio shift coefficient {n}", lhs-rhs)

    half_log = sum(q_coefficient(n, sp.Rational(1, 2), sp.Integer(0))*r**n
                   for n in range(1, 6))
    half_ratio = sp.series(sp.exp(half_log), r, 0, 4).removeO()
    half_want = 1-r/8+r**2/128+5*r**3/1024
    check("Normalized half-shift Gamma ratio through cubic order", half_ratio-half_want)

    for k in range(1, 25, 2):
        check(f"Bernoulli B_{k}(1/2) vanishes", sp.bernoulli(k, sp.Rational(1, 2)))
    for n in range(1, 25):
        term = (sp.Rational((-1)**(n+1), n*(n+1))
                * sp.bernoulli(n+1, sp.Rational(1, 2))*sp.I**(-n))
        check(f"Shifted Stirling real correction of inverse degree {n}", sp.re(term))

    q = sp.Symbol("q", positive=True)
    check("Reflection relative deficit is exactly q/(1+q)",
          sp.cancel((1-1/(1+q))-q/(1+q)))
    correction = sp.series(-sp.log(1+q)/2, q, 0, 5).removeO()
    check("Flat log-modulus correction through fourth exponential order",
          correction-(-q/2+q**2/4-q**3/6+q**4/8))

    for n in range(1, 101):
        mobius_sum = sum(sp.mobius(d) for d in sp.divisors(n))
        check(f"Dirichlet inverse: (mu*1)({n})", mobius_sum-(1 if n == 1 else 0))
        # Log n is represented exactly by its prime-log coefficient vector.
        lhs: dict[int, int] = {}
        for d in sp.divisors(n):
            factors = sp.factorint(d)
            if len(factors) == 1:
                prime = int(next(iter(factors)))
                lhs[prime] = lhs.get(prime, 0)+1
        rhs = {int(p): int(e) for p, e in sp.factorint(n).items()}
        check(f"Dirichlet logarithm: (Lambda*1)({n})=log({n})", lhs == rhs)

    u = sp.Symbol("u")
    root_series = sp.series((-1+sp.sqrt(1-4*u))/2, u, 0, 8).removeO()
    root_residual = sp.series(root_series+root_series**2+u, u, 0, 8).removeO()
    check("Simple real-symmetric implicit root, seven coefficients", root_residual)
    check("Multiple-root nonreal splitting: (i*q)^2+q^2", (sp.I*q)**2+q**2)
    for sigma in [sp.Rational(3, 5), sp.Rational(7, 10), sp.Rational(4, 5),
                  sp.Rational(9, 10)]:
        ingham = 3*(1-sigma)/(2-sigma)
        check(f"Ingham exponent below 1 at sigma={sigma}", bool(ingham < 1))

    passed = sum(result["passed"] for result in results)
    return {
        "scope": "Finite exact algebraic checks only; no proof of RH or general Hahn theorems.",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "total": len(results), "passed": passed,
        "all_passed": passed == len(results),
        "formal_proof_assistant_checked": False,
        "tests": results,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification-rerun.json"),
                        help="JSON report path; default does not overwrite shipped verification.json")
    args = parser.parse_args()
    report = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(f"{report['passed']}/{report['total']} exact finite checks passed.")
    print(f"Report: {args.output.resolve()}")
    return 0 if report["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
