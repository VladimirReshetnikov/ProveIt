#!/usr/bin/env python3
"""Regenerate the exact inverse-logarithmic pole coefficients.

Optional dependency: sympy. Run with ordinary Python (not Python -O).
The computation is formal symbolic algebra, not a proof of the analytic
remainder. The analytic remainder is established in article.tex.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp


def logarithm_truncated(poly: sp.Expr, z: sp.Symbol, order: int) -> sp.Expr:
    """Return log(1 + z*poly) through degree order in z."""
    result = sp.Integer(0)
    for k in range(1, order + 1):
        power = sp.Poly(sp.expand(poly ** k), z)
        for (degree,), coeff in power.terms():
            if degree + k <= order:
                result += sp.Rational((-1) ** (k + 1), k) * coeff * z ** (degree + k)
    return sp.expand(result)


def coefficients(order: int = 6) -> tuple[sp.Symbol, sp.Symbol, list[sp.Expr], sp.Expr]:
    """Solve epsilon + log(1+z*epsilon) + log(1+z*(epsilon+c)) = 0."""
    if order < 1:
        raise ValueError("order must be positive")
    z, c = sp.symbols("z c")
    epsilon = sp.Integer(0)
    values: list[sp.Expr] = []
    for k in range(1, order + 1):
        residual = epsilon + logarithm_truncated(epsilon, z, k)
        residual += logarithm_truncated(epsilon + c, z, k)
        value = sp.factor(-sp.expand(residual).coeff(z, k))
        values.append(value)
        epsilon += value * z ** k
    residual = epsilon + logarithm_truncated(epsilon, z, order)
    residual += logarithm_truncated(epsilon + c, z, order)
    assert sp.expand(residual) == 0
    return z, c, values, epsilon


def main() -> None:
    _, c, values, _ = coefficients(6)
    expected = [
        -c,
        c * (c + 4) / 2,
        -c * (c*c + 6*c + 12) / 3,
        c * (3*c + 8) * (c*c + 6*c + 12) / 12,
        -c * (3*c**4 + 35*c**3 + 155*c*c + 330*c + 240) / 15,
        c * (10*c**5 + 149*c**4 + 855*c**3 + 2540*c*c + 3840*c + 1920) / 60,
    ]
    assert all(sp.simplify(a - b) == 0 for a, b in zip(values, expected))
    data = {
        "status": "symbolic residual vanishes through z^6",
        "definition": "c=log(2), z=1/(2*W(sqrt(j/2)))",
        "coefficients": {str(k): str(a) for k, a in enumerate(values, 1)},
        "note": "Convergence and the pole-location error are proved in the article.",
    }
    path = Path(__file__).with_name("expansion_coefficients.json")
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
