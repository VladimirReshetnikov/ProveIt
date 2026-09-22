#!/usr/bin/env python3
"""Exact finite algebra supporting Gamma Functions over the Surreals.

These checks are NOT a proof assistant verification of the surreal theorems.
They use rational arithmetic and finite formal power-series truncations.
No floating-point number is used to stand for an infinite surreal number.

Requires Python >= 3.9 and SymPy >= 1.10.
Run: python code/verify.py --output data/verification.json
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Any
import platform
import sys

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc


class CheckSuite:
    def __init__(self) -> None:
        self.checks: List[Dict[str, Any]] = []

    def equal(self, name: str, actual: Any, expected: Any) -> None:
        difference = sp.expand(actual - expected)
        passed = difference == 0 or sp.simplify(difference) == 0
        self.checks.append({"name": name, "passed": bool(passed)})
        if not passed:
            self.checks[-1]["difference"] = str(difference)

    def condition(self, name: str, condition: bool) -> None:
        self.checks.append({"name": name, "passed": bool(condition)})


def bernoulli_coefficient(j: int) -> sp.Rational:
    if j < 1:
        raise ValueError("The Stirling index must be positive.")
    return sp.bernoulli(2 * j) / (2 * j * (2 * j - 1))


def log_trunc(t: sp.Symbol, scale: sp.Rational, degree: int) -> sp.Expr:
    return sp.Add(*(sp.Rational((-1) ** (k + 1), k) * scale ** k * t ** k
                    for k in range(1, degree + 1)))


def shifted_correction(t: sp.Symbol, shift: sp.Rational,
                       terms: int, degree: int) -> sp.Expr:
    """R_J(t/(1+shift*t)) through a prescribed degree."""
    result = sp.S.Zero
    for j in range(1, terms + 1):
        k = 2 * j - 1
        for r in range(degree - k + 1):
            result += (bernoulli_coefficient(j) * (-1) ** r
                       * sp.binomial(k + r - 1, r) * shift ** r * t ** (k + r))
    return result


def truncate(expr: sp.Expr, t: sp.Symbol, degree: int) -> sp.Expr:
    poly = sp.Poly(sp.expand(expr), t)
    return sp.Add(*(coefficient * t ** power[0]
                    for power, coefficient in poly.terms() if power[0] <= degree))


Sparse = Dict[Fraction, Fraction]


def clean(x: Sparse) -> Sparse:
    return {e: c for e, c in x.items() if c}


def add(x: Sparse, y: Sparse) -> Sparse:
    result = dict(x)
    for e, c in y.items():
        result[e] = result.get(e, Fraction(0)) + c
    return clean(result)


def scale(x: Sparse, n: Fraction) -> Sparse:
    return clean({e: n * c for e, c in x.items()})


def pp(x: Sparse) -> Sparse:
    return {e: c for e, c in x.items() if e > 0}


def leading_monomial_exponent(x: Sparse) -> Fraction:
    if not x:
        raise ValueError("Zero has no leading monomial in this test model.")
    return max(x)


def run_checks() -> Dict[str, Any]:
    suite = CheckSuite()
    t, u = sp.symbols("t u")
    expected = [sp.Rational(1, 12), sp.Rational(-1, 360),
                sp.Rational(1, 1260), sp.Rational(-1, 1680),
                sp.Rational(1, 1188), sp.Rational(-691, 360360)]
    for j, coefficient in enumerate(expected, start=1):
        suite.equal(f"Stirling coefficient b_{j}", bernoulli_coefficient(j), coefficient)
    for j in range(1, 17):
        suite.condition(f"Bernoulli alternating sign {j}",
                        bool((-1) ** (j + 1) * bernoulli_coefficient(j) > 0))

    # Shift recurrence. Omitted b_{J+1} first affects degree 2J+2.
    for terms in (1, 2, 4, 8, 12):
        degree = 2 * terms + 1
        elementary = sp.expand((1 / t + sp.Rational(1, 2))
                               * log_trunc(t, sp.S.One, degree + 1) - 1)
        correction = (shifted_correction(t, sp.S.One, terms, degree)
                      - shifted_correction(t, sp.S.Zero, terms, degree))
        defect = truncate(elementary + correction, t, degree)
        suite.equal(f"Shift identity: {terms} Bernoulli terms, through t^{degree}",
                    defect, sp.S.Zero)

    # Finite Gauss formulas. First omitted term has degree 2J+1.
    for n in (2, 3, 4, 5, 7):
        terms, degree = 6, 12
        defect = sp.S.Zero
        for k in range(n):
            shift = sp.Rational(k, n)
            defect += ((1 / t + shift - sp.Rational(1, 2))
                       * log_trunc(t, shift, degree + 1) - shift)
            defect += shifted_correction(t, shift, terms, degree)
        defect -= sp.Add(*(bernoulli_coefficient(j) * (t / n) ** (2 * j - 1)
                           for j in range(1, terms + 1)))
        suite.equal(f"Gauss n={n}: through t^{degree}", truncate(defect, t, degree), 0)

    phi = truncate((1 + u) * log_trunc(u, sp.S.One, 10) - u, u, 9)
    phi_expected = sp.Add(*(sp.Rational((-1) ** k, k * (k - 1)) * u ** k
                           for k in range(2, 10)))
    suite.equal("Tangent kernel Phi through u^9", phi, phi_expected)
    psi = u - log_trunc(u, sp.S.One, 9)
    psi_expected = sp.Add(*(sp.Rational((-1) ** k, k) * u ** k
                           for k in range(2, 10)))
    suite.equal("Tangent kernel Psi through u^9", psi, psi_expected)
    for k in range(1, 18):
        bracket = sp.Add(*((-1) ** r * sp.binomial(k + r - 1, r) * u ** r
                           for r in range(6))) - 1 + k * u
        suite.equal(f"Remainder bracket constant k={k}", bracket.coeff(u, 0), 0)
        suite.equal(f"Remainder bracket linear k={k}", bracket.coeff(u, 1), 0)
        suite.equal(f"Remainder bracket quadratic k={k}", bracket.coeff(u, 2),
                    sp.Rational(k * (k + 1), 2))

    # Direct verification of the elementary tangent-gap decomposition.
    x, q, lx, lq = sp.symbols("x q lx lq", nonzero=True)
    elementary_gap = ((q * x - sp.Rational(1, 2)) * (lx + lq) - q * x
                      - ((x - sp.Rational(1, 2)) * lx - x)
                      - (lx - 1 / (2 * x)) * x * (q - 1))
    target = x * (q * lq - q + 1) + (q - 1 - lq) / 2
    suite.equal("Exact elementary tangent-gap identity", elementary_gap, target)

    # Normal-form bookkeeping on finite rational-exponent supports only.
    # A term exponent e denotes the monomial omega^e; it is not a float.
    F = Fraction
    examples = [
        {F(1): F(1), F(0): F(17), F(-1): F(1)},
        {F(2): F(3), F(1, 2): F(-2), F(0): F(-5), F(-3): F(7)},
        {F(1, 5): F(2, 3), F(1, 8): F(5), F(-1, 4): F(-3)},
    ]
    finite_shifts = [{F(0): F(-12), F(-1): F(7)}, {F(-2): F(-5, 3)}]
    for index, example in enumerate(examples, 1):
        for shift_index, shift in enumerate(finite_shifts, 1):
            translated = add(example, shift)
            suite.condition(f"pp finite translation {index}.{shift_index}",
                            pp(translated) == pp(example))
            suite.condition(f"M finite translation {index}.{shift_index}",
                            leading_monomial_exponent(translated)
                            == leading_monomial_exponent(example))
        for n in (2, 3, 7):
            scaled = scale(example, F(n))
            suite.condition(f"pp homogeneity {index}, n={n}", pp(scaled) == scale(pp(example), F(n)))
            suite.condition(f"M positive scaling {index}, n={n}",
                            leading_monomial_exponent(scaled) == leading_monomial_exponent(example))
            gauss_pp = {}
            for k in range(n):
                gauss_pp = add(gauss_pp, pp(add(example, {F(0): F(k, n)})))
            suite.condition(f"Gauss gauge bookkeeping {index}, n={n}", gauss_pp == pp(scaled))

    w, lam = sp.symbols("w lambda")
    suite.equal("Scalar derivative of lambda*w*exp(-w)",
                sp.diff(lam * w * sp.exp(-w), w), lam * (1 - w) * sp.exp(-w))
    for n in (1, 2, 3, 5):
        coefficient = sp.diff(sp.log(x), x, n)
        suite.equal(f"Leading polygamma derivative sign coefficient n={n}",
                    coefficient, (-1) ** (n - 1) * sp.factorial(n - 1) / x ** n)

    all_passed = all(item["passed"] for item in suite.checks)
    return {
        "article": "Gamma Functions over the Surreals",
        "scope": "Exact finite algebra checks; not proof-assistant verification of the surreal theorems.",
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "check_count": len(suite.checks),
        "passed_count": sum(item["passed"] for item in suite.checks),
        "all_passed": all_passed,
        "checks": suite.checks,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("data/verification.json"))
    args = parser.parse_args()
    result = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"{result['passed_count']}/{result['check_count']} checks passed.")
    print(f"Record written to {args.output}.")
    for check in result["checks"]:
        if not check["passed"]:
            print(f"FAILED: {check['name']}: {check.get('difference', '')}", file=sys.stderr)
    return 0 if result["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
