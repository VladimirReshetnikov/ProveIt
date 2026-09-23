#!/usr/bin/env python3
"""Supplementary exact checks for Curve Rigidity over Omnific Integers.

These computations check finite algebraic identities and finite-support
sanity cases. They do NOT formally verify the Hahn or geometric theorems.
Run: python verification.py [--output verification_report.json]
Requires Python 3.9+ and SymPy 1.14.0.
"""
from __future__ import annotations

import argparse
import json
import random
import sys
from fractions import Fraction
from pathlib import Path
from typing import Dict, Tuple

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("Install the dependency with: python -m pip install sympy==1.14.0") from exc

Exponent = Tuple[int, int]
Sparse = Dict[Exponent, Fraction]
ZERO: Exponent = (0, 0)


def clean(f: Sparse) -> Sparse:
    return {e: c for e, c in f.items() if c}


def add(f: Sparse, g: Sparse) -> Sparse:
    result = dict(f)
    for e, c in g.items():
        result[e] = result.get(e, Fraction(0)) + c
    return clean(result)


def multiply(f: Sparse, g: Sparse) -> Sparse:
    result: Sparse = {}
    for e, c in f.items():
        for d, b in g.items():
            power = (e[0] + d[0], e[1] + d[1])
            result[power] = result.get(power, Fraction(0)) + c * b
    return clean(result)


def derive(f: Sparse, weights: Tuple[Fraction, Fraction]) -> Sparse:
    return clean({e: c * (weights[0] * e[0] + weights[1] * e[1])
                  for e, c in f.items()})


def random_series(rng: random.Random, side: str) -> Sparse:
    result: Sparse = {}
    for _ in range(rng.randint(1, 12)):
        e = (rng.randint(-12, 12), rng.randint(-12, 12))
        if side == "B" and e > ZERO:
            e = (-e[0], -e[1])
        if side == "V" and e < ZERO:
            e = (-e[0], -e[1])
        result[e] = result.get(e, Fraction(0)) + Fraction(
            rng.choice([-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]),
            rng.randint(1, 7),
        )
    return clean(result)


def run_checks() -> dict:
    checks = []

    def require(name: str, condition: bool, **details: object) -> None:
        if not condition:
            raise AssertionError("Check failed: " + name)
        checks.append({"name": name, "passed": True, **details})

    x, y, a, b, r, u, dx, dy, z = sp.symbols("x y a b r u dx dy z")
    P = x**3 + a*x + b
    delta0 = 4*a**3 + 27*b**2
    cert = ((27*b - 18*a*x)*P
            + (6*a*x*x - 9*b*x + 4*a*a)*sp.diff(P, x))
    require("cubic_bezout_certificate", sp.expand(cert - delta0) == 0)
    require("cubic_polynomial_discriminant_sign",
            sp.expand(sp.discriminant(P, x) + delta0) == 0,
            note="Polynomial discriminant = -Delta0; elliptic discriminant = -16 Delta0.")
    X = u*u - 2*r
    Y = u*(u*u - 3*r)
    require("singular_weierstrass_parametrization",
            sp.expand(Y*Y - (X**3 - 3*r*r*X + 2*r**3)) == 0)
    require("singular_cubic_factorization",
            sp.expand((x-r)**2*(x+2*r) - (x**3 - 3*r*r*x + 2*r**3)) == 0)
    require("nonconstant_coefficient_counterexample",
            sp.expand((u**3)**2 - ((u**2)**3 + u**2 - u**2)) == 0)

    polys = [x*x + 1, x**3 - x + 1, x**5 - x + 1,
             x**4 + x + 1, (x-1)*(x+2)*(x-3)]
    certificate_count = 0
    for index, poly in enumerate(polys, start=1):
        poly = sp.expand(poly)
        deriv = sp.diff(poly, x)
        U, W, gcd = sp.gcdex(poly, deriv, x)
        require("squarefree_polynomial_%d" % index, gcd == 1,
                polynomial=str(poly))
        for m in range(2, 9):
            F = y**m - poly
            G = m*y**(m-1)*dy - deriv*dx
            H = U*y*dx + m*W*dy
            identity = dx - y**(m-1)*H + U*dx*F + W*G
            require("differential_ideal_certificate_%d_m%d" % (index, m),
                    sp.expand(identity) == 0)
            certificate_count += 1
    require("integer_degree_threshold_2_to_99",
            all((m-1)*d >= m for m in range(2, 100) for d in range(2, 100)),
            note="Only a finite sanity check; the paper proves the inequality for all m,d.")

    root = sp.series(sp.sqrt(1-z**4+z**6), z, 0, 20).removeO()
    scaled = sp.expand(z**(-3)*root)
    expected = {-3: sp.Integer(1), 1: -sp.Rational(1, 2),
                3: sp.Rational(1, 2), 5: -sp.Rational(1, 8),
                7: sp.Rational(1, 4), 9: -sp.Rational(3, 16)}
    require("displayed_elliptic_root_coefficients",
            all(scaled.coeff(z, power) == coefficient
                for power, coefficient in expected.items()),
            coefficients={str(e): str(c) for e, c in expected.items()})
    residual = sp.Poly(sp.expand(root**2 - (1-z**4+z**6)), z)
    first_residual_degree = min(monomial[0] for monomial, coeff in residual.terms() if coeff)
    require("finite_binomial_remainder_order", first_residual_degree >= 20,
            first_nonzero_degree=first_residual_degree,
            note="This is a formal finite truncation check, not a numerical approximation.")

    rng = random.Random(20260923)
    trials = 400
    detected = 0
    for trial in range(trials):
        side = "B" if trial % 2 == 0 else "V"
        f = random_series(rng, side)
        g = random_series(rng, side)
        weights = (Fraction(rng.randint(-5, 5)), Fraction(rng.randint(-5, 5)))
        Df, Dg = derive(f, weights), derive(g, weights)
        assert derive(multiply(f, g), weights) == add(multiply(Df, g), multiply(f, Dg))
        assert set(Df).issubset(f)
        if Df:
            assert min(Df) >= min(f)
        assert ZERO not in Df
        if side == "B":
            assert all(e < ZERO for e in Df)
        else:
            assert all(e > ZERO for e in Df)
        nonzero_exponents = [e for e in f if e != ZERO]
        if nonzero_exponents:
            e = min(nonzero_exponents)
            index = 0 if e[0] else 1
            w = [Fraction(0), Fraction(0)]
            w[index] = Fraction(1, e[index])
            Ddetect = derive(f, (w[0], w[1]))
            assert Ddetect[e] == f[e]
            detected += 1
    require("finite_support_Euler_laws", True, trials=trials,
            detected_nonconstant_cases=detected,
            exponent_group="Z^2, lexicographic order",
            checks_per_trial=["Leibniz", "support containment", "valuation monotonicity",
                              "zero constant term", "strict one-sided image", "detection when nonconstant"])
    return {
        "title": "Supplementary checks: Curve Rigidity over Omnific Integers",
        "repository_commit": "89bec380b218c0a5bb865f53a86f5abf7f8fb5ad",
        "python_version": sys.version.split()[0],
        "sympy_version": sp.__version__,
        "all_passed": True,
        "recorded_checks": len(checks),
        "differential_ideal_certificates": certificate_count,
        "random_finite_support_trials": trials,
        "formal_verification": False,
        "limitations": [
            "No Lean build or proof-assistant verification was performed.",
            "Finite checks do not verify arbitrary Hahn supports, valuation ranks, or algebraic geometry.",
            "Novelty and literature priority are not established by this program.",
        ],
        "checks": checks,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().with_name("verification_report.json"))
    args = parser.parse_args()
    report = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("PASS: %d recorded checks, including %d differential certificates and %d finite-support trials."
          % (report["recorded_checks"], report["differential_ideal_certificates"],
             report["random_finite_support_trials"]))
    print("Report:", args.output)
    print("These are supplementary computations, not formal verification of the theorems.")


if __name__ == "__main__":
    main()
