#!/usr/bin/env python3
"""Independent exact algebra and high-precision collision diagnostics.

The theorem is analytic.  These finite checks and ordinary quadratures
are reproducible diagnostics, not interval proofs or arithmetic relations.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp
import sympy as sp


HERE = Path(__file__).resolve().parents[1] / "results"


def exact_checks():
    u, R, L = sp.symbols("u R L")
    counts = {}
    # Coefficient of degree zero in the holomorphic contact is the
    # compact polynomial-in-ratio formula stated in the article.
    zero_tests = 0
    for r in range(13):
        lhs = sum(sp.binomial(r, j) * (R - 1) ** j / j
                  for j in range(1, r + 1))
        rhs = sum((R ** j - 1) / j for j in range(1, r + 1))
        assert sp.expand(lhs - rhs) == 0
        zero_tests += 1
    counts["zero_order_ratio_polynomials"] = zero_tests

    # Every apparent pole u=-j in a finite lower term is canceled by
    # the rising factorial; the only critical pole is explicitly removed.
    polynomial_tests = 0
    for r in range(1, 11):
        P = sp.rf(1 + u, r)
        for j in range(1, r + 1):
            rem = sp.rem(sp.Poly(P, u), sp.Poly(u + j, u)).as_expr()
            assert rem == 0
            polynomial_tests += 1
    counts["rising_factorial_divisibility"] = polynomial_tests

    # Independently differentiate the finite upper/lower primitive.
    x, a, b = sp.symbols("x a b", positive=True)
    primitive_tests = 0
    for r in range(6):
        for k in range(r + 1):
            # A nonresonant positive integer spectral order makes this
            # an exact rational identity; u=2 avoids every critical pole.
            exponent = sp.Integer(2)
            primitive = -(-1) ** r * sp.rf(1 + exponent, r) * sum(
                sp.binomial(k, j) * (b - a) ** j
                * (x + a) ** (k - j - r - exponent)
                / (r + exponent + j - k)
                for j in range(k + 1)
            )
            target = (-1) ** r * sp.rf(1 + exponent, r) * (
                x + a) ** (-r - 1 - exponent) * (x + b) ** k
            assert sp.factor(sp.diff(primitive, x) - target) == 0
            primitive_tests += 1
    counts["finite_mixed_primitives"] = primitive_tests

    # Contact jets through spectral degree 4, argument degree 5,
    # checked both by a Taylor expansion and by finite polynomial division.
    jet_tests = 0
    contact_table = []
    for r in range(6):
        P = (-1) ** r * sp.rf(1 + u, r) / sp.factorial(r)
        logpart = sum((-L) ** (h + 1) * u ** h / sp.factorial(h + 1)
                      for h in range(5))
        exptrunc = sum((-L) ** h * u ** h / sp.factorial(h)
                       for h in range(5))
        direct = P * (logpart + exptrunc * sum(
            sp.binomial(r, j) * (R - 1) ** j / (u + j)
            for j in range(1, r + 1)))
        direct = sp.series(direct, u, 0, 5).removeO().expand()
        divided = P * logpart + exptrunc * sum(
            sp.binomial(r, j) * (R - 1) ** j * sp.cancel(P / (u + j))
            for j in range(1, r + 1))
        for m in range(5):
            val = sp.expand((-1) ** m * sp.factorial(m)
                            * direct.coeff(u, m))
            other = sp.expand((-1) ** m * sp.factorial(m)
                              * sp.expand(divided).coeff(u, m))
            assert sp.simplify(val - other) == 0
            contact_table.append({"r": r, "m": m, "kappa": str(val)})
            jet_tests += 1
    counts["spectral_contact_jets"] = jet_tests

    return {"passed": True, "counts": counts,
            "total": sum(counts.values()), "contact_table": contact_table}


def D(a, b):
    if a == b:
        return 1 / a
    return mp.log(a / b) / (a - b)


def B10(a, b):
    # Integral of -1/((y+a)^2(y+b)); derivative in the first shift.
    if a == b:
        return -1 / (2 * a ** 2)
    return ((a - b) / a - mp.log(a / b)) / (a - b) ** 2


def B11(a, b):
    # Positive, mixed shift derivative of the elementary beta kernel.
    if a == b:
        return 1 / (3 * a ** 3)
    return ((a - b) * (1 / a + 1 / b) - 2 * mp.log(a / b)) / (a - b) ** 3


def split_points(eps):
    return sorted(set([mp.mpf(0), eps, 10 * eps, 100 * eps,
                       mp.mpf("0.01"), mp.mpf("0.1"), mp.mpf(1)]))


def ordinary_integral(r, t, a, b, eps):
    def f(x):
        pa = mp.digamma(x + a * eps) if r == 0 else mp.polygamma(r, x + a * eps)
        pb = mp.digamma(x + b * eps) if t == 0 else mp.polygamma(t, x + b * eps)
        return pa * pb
    return mp.quad(f, split_points(eps))


def diagnostics():
    mp.mp.dps = 65
    output = {"working_digits": mp.mp.dps, "beta_checks": [], "collisions": []}
    for a, b in [(mp.mpf(1), mp.mpf(1)),
                 (mp.mpf(2), mp.mpf(1)),
                 (mp.mpf(2) / 3, mp.mpf(7) / 5)]:
        beta_integrals = [
            ("B00", D(a, b), lambda y: 1 / ((y + a) * (y + b))),
            ("B10", B10(a, b), lambda y: -1 / ((y + a) ** 2 * (y + b))),
            ("B11", B11(a, b), lambda y: 1 / ((y + a) ** 2 * (y + b) ** 2)),
        ]
        for name, closed, integrand in beta_integrals:
            direct = mp.quad(integrand, [0, 1, mp.inf])
            error = abs(closed - direct)
            assert error < mp.mpf("1e-60")
            output["beta_checks"].append({"name": name, "lambda": str(a),
                                          "mu": str(b), "absolute_error": mp.nstr(error, 6)})

        z2, z3 = mp.zeta(2), mp.zeta(3)
        fp00 = 2 * mp.stieltjes(1) - 2 * z2
        fp11 = 2 * z3 + 4 * mp.diff(mp.zeta, 3)
        target00 = fp00 - mp.euler * mp.log(a * b)
        target10 = z2 * (b / a + mp.log(b / a))
        target11 = fp11 + 2 * z3 * (mp.log(a * b) + 2 - b / a - a / b)
        cases = [
            (0, 0, target00, lambda e: D(a, b) / e - 2 * mp.euler * mp.log(e)),
            (1, 0, target10, lambda e: B10(a, b) / e ** 2 - mp.euler / (a * e)),
            (1, 1, target11, lambda e: B11(a, b) / e ** 3
             + z2 * (1 / a + 1 / b) / e + 4 * z3 * mp.log(e)),
        ]
        for r, t, target, divergent in cases:
            rows = []
            for eps in [mp.mpf("1e-5"), mp.mpf("1e-6"), mp.mpf("1e-7")]:
                value = ordinary_integral(r, t, a, b, eps)
                normalized = value - divergent(eps)
                error = normalized - target
                rows.append({"epsilon": str(eps), "normalized": mp.nstr(normalized, 45),
                             "target_constant": mp.nstr(target, 45),
                             "residual": mp.nstr(error, 12)})
            # Ordinary O(epsilon log epsilon) or better convergence.
            # This assertion diagnoses a missing constant or leading subtraction.
            errors = [abs(mp.mpf(row["residual"])) for row in rows]
            assert errors[-1] < mp.mpf("5e-4")
            assert errors[-1] < errors[0] / 20
            output["collisions"].append({"r": r, "t": t,
                                         "lambda": str(a), "mu": str(b), "rows": rows})
    output["passed"] = True
    return output


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--exact-only", action="store_true")
    args = parser.parse_args()
    result = {"exact": exact_checks()}
    if not args.exact_only:
        result["numerical"] = diagnostics()
    target = HERE / ("collision_exact_checks.json" if args.exact_only else "collision_checks.json")
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"file": str(target), "exact_checks": result["exact"]["total"],
                      "numerical_passed": result.get("numerical", {}).get("passed")}, indent=2))


if __name__ == "__main__":
    main()
