#!/usr/bin/env python3
"""Reproduce the elementary specializations in article Section 4.

Requires Python 3.10+, SymPy, and mpmath.  No project modules or network
access are used.  Run from any directory:

    python code/check_specializations.py

The default output is results/specialization_checks.json next to code/.
Exact checks start with elementary exponential/logarithm kernels.  The
ordinary, unsubtracted Mellin integral at C=4 is evaluated independently
of all multiple-polylogarithm reductions.  Its decimal residual is a
numerical diagnostic, not an interval-certified accuracy estimate.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp
import sympy as sp


def symbolic_checks() -> dict:
    t, u = sp.symbols("t u", positive=True)
    ell = sp.Symbol("L", real=True)
    z = sp.Symbol("z", real=True)
    Q = sp.Rational
    checks: list[dict] = []

    def equal(name: str, actual: sp.Expr, expected: sp.Expr) -> None:
        difference = sp.simplify(sp.expand(actual - expected))
        if difference != 0:
            raise AssertionError(f"{name}: nonzero exact difference {difference}")
        checks.append({"name": name, "exact_value": str(sp.simplify(actual)),
                       "passed": True})

    # Independent elementary definitions: Li_1(e^-t), Li_-1(e^-t),
    # and Li_-2(e^-t), with the last two differentiated before expansion.
    bose = 1 / (sp.exp(t) - 1)
    li1 = -sp.log(1 - sp.exp(-t))
    li1_local = sp.series(li1, t, 0, 6).removeO().subs(sp.log(t), ell)
    li_minus1 = sp.series(-sp.diff(bose, t), t, 0, 3).removeO()
    li_minus2 = sp.series(sp.diff(bose, t, 2), t, 0, 3).removeO()
    kernel_f = sp.expand(li1_local**2 * li_minus1)
    kernel_u = sp.expand(li1_local**2 * li_minus2)

    f_expected = {-2: ell**2, -1: -ell,
                  0: -ell**2 / 12 + ell / 12 + Q(1, 4)}
    u_expected = {-3: 2 * ell**2, -2: -2 * ell,
                  -1: ell / 6 + Q(1, 2), 0: -Q(1, 12),
                  1: -ell**2 / 120 - ell / 720 + Q(1, 288),
                  2: ell / 120 + Q(1, 1440)}
    for power, expected in f_expected.items():
        equal(f"F kernel coefficient t^{power}",
              kernel_f.coeff(t, power), expected)
    for power, expected in u_expected.items():
        equal(f"U kernel coefficient t^{power}",
              kernel_u.coeff(t, power), expected)

    def local_laurent(log_poly: sp.Expr, centre: int) -> sp.Expr:
        """Polar and constant terms at a nonpositive spectral integer."""
        poly = sp.Poly(log_poly, ell)
        model = sum((-1)**r * sp.factorial(r) * coefficient / u**(r + 1)
                    for (r,), coefficient in poly.terms())
        degree = poly.degree()
        reciprocal_gamma = sp.series(1 / sp.gamma(centre + u),
                                     u, 0, degree + 2).removeO()
        return sp.series(reciprocal_gamma * model, u, 0, 1).removeO()

    gamma = sp.EulerGamma
    equal("F Laurent polynomial at C=0",
          local_laurent(kernel_f.coeff(t, 0), 0),
          -1 / (6 * u**2) - (2 * gamma + 1) / (12 * u)
          + Q(1, 4) - (gamma**2 + gamma) / 12 + sp.zeta(2) / 12)
    equal("U regular value at C=0",
          local_laurent(kernel_u.coeff(t, 0), 0), -Q(1, 12))
    equal("U Laurent polynomial at C=-1",
          local_laurent(kernel_u.coeff(t, 1), -1),
          1 / (60 * u**2) + (gamma / 60 - Q(13, 720)) / u
          + gamma**2 / 120 - 13 * gamma / 720
          - sp.pi**2 / 720 - Q(1, 480))
    equal("U Laurent polynomial at C=-2",
          local_laurent(kernel_u.coeff(t, 2), -2),
          -1 / (60 * u) + Q(19, 720) - gamma / 60)

    for centre, order, leading in [(3, 3, 2), (2, 2, 2), (1, 2, -Q(1, 6))]:
        coefficient = sp.expand(kernel_u.coeff(t, -centre)).coeff(ell, order - 1)
        equal(f"U leading pole coefficient at C={centre}, order {order}",
              (-1)**(order - 1) * sp.factorial(order - 1)
              * coefficient / sp.gamma(centre), sp.sympify(leading))

    # The all-integer formula for the negative-axis pole pattern is proved
    # analytically in the article; the two first cases also agree exactly.
    equal("U residue at C=-2 matches Bernoulli formula",
          -sp.Rational(1, 60), sp.bernoulli(4) / 2)
    equal("U double-pole coefficient at C=-1 matches Bernoulli formula",
          sp.Rational(1, 60), -sp.bernoulli(4) / 2)

    elementary_f = z * sp.log(1 - z)**2 / (1 - z)**2
    log2 = sp.log(2)
    derivative = elementary_f
    for j, expected in enumerate([-log2**2 / 4, -log2 / 4,
                                  (log2**2 - log2 - 1) / 8]):
        equal(f"F({-j};-1)", derivative.subs(z, -1), expected)
        derivative = sp.simplify(z * sp.diff(derivative, z))
    primitive = (sp.log(1 - z)**2 + 2 * sp.log(1 - z) + 2) / (1 - z) - 2
    equal("F normalized primitive derivative", sp.diff(primitive, z),
          sp.log(1 - z)**2 / (1 - z)**2)
    equal("F normalized primitive at z=0", primitive.subs(z, 0), sp.S.Zero)
    equal("F(1;-1)", primitive.subs(z, -1), log2**2 / 2 + log2 - 1)

    return {"scope": "Finite exact checks of the printed elementary specializations",
            "log_symbol": "L = log(t), on t > 0",
            "assertion_count": len(checks), "all_passed": True,
            "checks": checks}


def mellin_diagnostic(dps: int) -> dict:
    with mp.workdps(dps):
        def integrand(t):
            q = mp.exp(-t)
            denominator = -mp.expm1(-t)
            logarithm = -mp.log(denominator)
            return t**3 * logarithm**2 * q * (1 + q) / denominator**3

        integral = mp.quad(integrand, [0, 1, mp.inf]) / mp.gamma(4)
        closed = mp.pi**4 / 24 + 7 * mp.pi**2 / 12 - 15 * mp.zeta(3) / 2
        residual = abs(integral - closed)
        threshold = mp.power(10, -(dps - 10))
        if residual >= threshold:
            raise AssertionError(f"C=4 quadrature diagnostic residual {residual}")
        return {
            "working_decimal_digits": dps,
            "method": "Ordinary unsubtracted Mellin quadrature on [0,1] and [1,infinity)",
            "integrand_before_division_by_Gamma4":
                "t^3*(-log(1-exp(-t)))^2*exp(-t)*(1+exp(-t))/(1-exp(-t))^3",
            "closed_form": "pi^4/24 + 7*pi^2/12 - 15*zeta(3)/2",
            "quadrature": mp.nstr(integral, dps),
            "closed_form_decimal": mp.nstr(closed, dps),
            "absolute_residual": mp.nstr(residual, dps),
            "diagnostic_threshold": mp.nstr(threshold, 8),
            "passed": True,
            "scope": "Floating-point diagnostic only; no interval-certified error bound",
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=60)
    parser.add_argument("--output", type=Path, default=
                        Path(__file__).resolve().parents[1]
                        / "results" / "specialization_checks.json")
    args = parser.parse_args()
    if args.dps < 30:
        parser.error("--dps must be at least 30")
    result = {
        "schema": "proveit.mixed-specializations.v1",
        "dependencies": {"sympy": sp.__version__, "mpmath": mp.__version__},
        "symbolic": symbolic_checks(),
        "C4_mellin_diagnostic": mellin_diagnostic(args.dps),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"symbolic_assertions": result["symbolic"]["assertion_count"],
                      "all_passed": True,
                      "C4_absolute_residual": result["C4_mellin_diagnostic"]["absolute_residual"],
                      "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
