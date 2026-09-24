#!/usr/bin/env python3
"""Optional exact symbolic checks. Requires SymPy; the main verifier does not."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp
from verify import minimal_polynomial


def zero(expression: sp.Expr, context: str) -> None:
    if sp.cancel(expression) != 0:
        raise AssertionError(f"Symbolic check failed: {context}")


def main() -> None:
    z, u, d = sp.symbols("z u d")
    zu = u / (1 + u**2)
    root = (1 - u**2) / (1 + u**2)
    checks = []
    for q in range(2, 15):
        A = sp.zeros(q)
        for i in range(q - 1):
            A[i, i + 1] = A[i + 1, i] = 1
        one = sp.ones(q, 1)
        resolvent = sp.cancel((one.T * (sp.eye(q) - z * A).inv() * one)[0] / 2)
        formula = (sp.Rational(q, 2) / (1 - 2 * zu)
                   - u * (1 - u**q) / ((1 - 2 * zu) * (1 - u) * (1 + u**(q + 1))))
        zero(resolvent.subs(z, zu) - formula, f"row resolvent q={q}")
        positive_length_gf = sp.cancel(resolvent - sp.Rational(q, 2))
        coefficients = minimal_polynomial(q)
        degree = len(coefficients) - 1
        expected = sum(coefficient * z**(degree - i)
                       for i, coefficient in enumerate(coefficients))
        denominator = sp.denom(positive_length_gf)
        zero(denominator / denominator.subs(z, 0) - expected,
             f"reduced recurrence denominator q={q}")
        checks.append({"q": q, "positive_length_generating_function": str(positive_length_gf),
                       "normalized_denominator": str(sp.expand(expected))})
    K = (1 + u) * (1 + u**2) / (1 - u)**3
    H = (1 + u)**2 / (1 - u)**2
    zero(K * (1 + u**2) * sp.diff(zu, u) - H, "residue kernel")
    baseline_gf = zu / (1 - 2 * zu)**2 + d / (2 * (1 - 2 * zu)) - u / ((1 - 2 * zu) * (1 - u))
    diagonal_gf = (d + 1 - 2 * d * zu - root) / (2 * (1 - 2 * zu)**2)
    zero(baseline_gf - diagonal_gf, "baseline diagonal generating function")
    h_gf = root / (2 * (1 - 2 * zu)**2)
    zero(h_gf - (1 + 2 * zu)**2 / (2 * root**3), "central-binomial extraction")
    report = {"status": "all checks passed", "sympy_version": sp.__version__,
              "row_checks": checks, "scalar_rational_identity_checks": 3,
              "warning": "These are exact finite symbolic checks, not a formalized universal proof."}
    directory = Path(__file__).resolve().parent / "verification"
    directory.mkdir(exist_ok=True)
    (directory / "symbolic_results.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
