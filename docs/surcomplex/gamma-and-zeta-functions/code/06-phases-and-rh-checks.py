#!/usr/bin/env python3
"""Finite exact algebra checks for the accompanying article.

These checks do not implement the surreal field, prove Hahn summability,
verify the Riemann hypothesis, or validate any external research paper.
Default: print JSON only. Use --output PATH to write a separate result file.
"""
from __future__ import annotations

import argparse
import json
import platform
from collections import Counter
from pathlib import Path
from typing import Any

import sympy as sp


def run_checks() -> dict[str, Any]:
    checks: list[dict[str, Any]] = []

    def record(name: str, category: str, condition: Any) -> None:
        passed = bool(condition)
        checks.append({"name": name, "category": category, "passed": passed})
        if not passed:
            raise AssertionError(f"Failed: {name}")

    q, A, s, u, z = sp.symbols("q A s u z")
    # Gamma shift: L(A+1)-L(A)-log(A), using q=1/A.
    for J in range(1, 7):
        defect = (1/q + sp.Rational(1, 2))*sp.log(1+q)-1
        defect += sum(
            sp.bernoulli(2*k)/(2*k*(2*k-1))*q**(2*k-1)
            *((1+q)**(1-2*k)-1) for k in range(1, J+1)
        )
        truncated = sp.series(defect, q, 0, 2*J+2).removeO().expand()
        record(f"Stirling shift J={J}", "Stirling", truncated == 0)

    # Hurwitz shift for positive ordinary integer parameters.
    for sigma in range(2, 7):
        J = 3
        Z = q**(sigma-1)/sp.Integer(sigma-1) + q**sigma/2
        Z += sum(sp.bernoulli(2*k)/sp.factorial(2*k)
                 *sp.rf(sigma, 2*k-1)*q**(sigma+2*k-1)
                 for k in range(1, J+1))
        defect = Z-Z.subs(q, q/(1+q))-q**sigma
        truncated = sp.series(defect, q, 0, sigma+2*J+2).removeO().expand()
        record(f"Hurwitz shift s={sigma}", "Hurwitz", truncated == 0)

    # Terminating Hurwitz values, including m=0 and the B_1 convention.
    for m in range(13):
        Z = -A**(m+1)/sp.Integer(m+1) + A**m/2
        Z += sum(sp.bernoulli(2*k)/sp.factorial(2*k)
                 *sp.rf(-m, 2*k-1)*A**(m-2*k+1)
                 for k in range(1, m+2))
        target = -sp.bernoulli(m+1, A)/sp.Integer(m+1)
        record(f"Hurwitz Bernoulli value m={m}", "Hurwitz",
               sp.expand(Z-target) == 0)
        record(f"Hurwitz polynomial shift m={m}", "Hurwitz",
               sp.expand(Z-Z.subs(A, A+1)-A**m) == 0)

    for k in range(1, 17):
        derivative = sp.diff(sp.rf(s, 2*k-1), s).subs(s, 0)
        actual = sp.bernoulli(2*k)/sp.factorial(2*k)*derivative
        target = sp.bernoulli(2*k)/(2*k*(2*k-1))
        record(f"Hurwitz-to-Stirling coefficient k={k}", "Bridge",
               sp.simplify(actual-target) == 0)
    leading = sp.diff(A**(1-s)/(s-1)+A**(-s)/2, s).subs(s, 0)
    target = (A-sp.Rational(1, 2))*sp.log(A)-A
    record("Hurwitz derivative leading terms", "Bridge",
           sp.simplify(leading-target) == 0)

    # Root expansion, with ordinary symbolic Taylor coefficients.
    f1, f2, h0, h1 = sp.symbols("f1 f2 h0 h1", nonzero=True)
    a1 = -h0/f1
    a2 = h0*h1/f1**2-f2*h0**2/(2*f1**3)
    displacement = a1*u+a2*u**2
    residual = sp.expand(f1*displacement+f2*displacement**2/2
                         +u*(h0+h1*displacement))
    for k in (1, 2):
        record(f"Implicit root coefficient order {k}", "Root deformation",
               sp.simplify(residual.coeff(u, k)) == 0)
    for m in range(2, 13):
        p = z**m+1
        record(f"Simple splitting polynomial degree {m}", "Root deformation",
               sp.gcd(p, sp.diff(p, z)) == 1)

    # Truncated multiplicative-index algebra. This is NOT Hahn evaluation.
    N = 100
    ones = {n: sp.Integer(1) for n in range(1, N+1)}
    mu = {n: sp.mobius(n) for n in range(1, N+1)}
    for n in range(1, N+1):
        coefficient = sum(mu[d] for d in sp.divisors(n))
        record(f"Mobius inverse coefficient n={n}", "Dirichlet",
               coefficient == (1 if n == 1 else 0))

    def multiply(a: dict[int, Any], b: dict[int, Any]) -> dict[int, Any]:
        out: dict[int, Any] = {}
        for m, am in a.items():
            for n, bn in b.items():
                if m*n <= N:
                    out[m*n] = out.get(m*n, 0)+am*bn
        return out

    euler: dict[int, Any] = {1: sp.Integer(1)}
    reciprocal: dict[int, Any] = {1: sp.Integer(1)}
    for p in sp.primerange(2, N+1):
        factor: dict[int, Any] = {1: sp.Integer(1)}
        power = p
        while power <= N:
            factor[power] = sp.Integer(1)
            power *= p
        euler = multiply(euler, factor)
        reciprocal = multiply(reciprocal, {1: 1, p: -1})
    record("Euler product coefficients through 100", "Dirichlet",
           all(euler.get(n, 0) == ones[n] for n in range(1, N+1)))
    record("Reciprocal Euler coefficients through 100", "Dirichlet",
           all(reciprocal.get(n, 0) == mu[n] for n in range(1, N+1)))

    # Check the additive logarithmic identity using prime-exponent vectors.
    for n in range(1, 51):
        actual: Counter[int] = Counter()
        for d in sp.divisors(n):
            factors = sp.factorint(d)
            if len(factors) == 1:
                actual[next(iter(factors))] += 1
        target = Counter({int(p): int(e) for p, e in sp.factorint(n).items()})
        record(f"von Mangoldt divisor identity n={n}", "Dirichlet",
               actual == target)

    x, y, T, a = sp.symbols("x y T a", real=True)
    w = x+sp.I*y
    cp, cm = sp.Rational(1, 2)+sp.I*T, sp.Rational(1, 2)-sp.I*T
    upper = (w-cp)**2-a**2
    reflected = (1-w-cm)**2-a**2
    conjugate = (sp.conjugate(w)-cm)**2-a**2
    record("Quartet reflection symmetry", "Global countermodel",
           sp.expand(upper-reflected) == 0)
    record("Quartet conjugation symmetry", "Global countermodel",
           sp.expand(sp.conjugate(upper)-conjugate) == 0)

    counts = Counter(item["category"] for item in checks)
    C0 = sp.Rational(3, 2)-sp.cot(1/sp.sqrt(2))/sp.sqrt(2)
    return {
        "status": "all finite checks passed",
        "check_count": len(checks),
        "category_counts": dict(counts),
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "numeric_constant_C0": str(sp.N(C0, 30)),
        "formal_proof_assistant_checked": False,
        "proves_RH": False,
        "checks_Hahn_summability": False,
        "validates_external_papers": False,
        "checks": checks,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Optional JSON output path; default prints only.")
    args = parser.parse_args()
    result = run_checks()
    text = json.dumps(result, indent=2)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text+"\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
