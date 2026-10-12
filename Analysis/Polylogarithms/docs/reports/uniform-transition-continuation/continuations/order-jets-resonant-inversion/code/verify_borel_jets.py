#!/usr/bin/env python3
"""Reproduce exact and numerical checks for the Borel/order-jet section.

Dependencies: Python 3, mpmath, sympy.
Run: python verify_borel_jets.py --output borel_verification.json

The symbolic checks are exact finite algebra. The numerical checks compare
two distinct integrals: a logistic-density order derivative and the real
principal-value Laplace integral of a meromorphic csc kernel. They are
high-precision numerical evidence, not interval certificates or proofs.

All positive poles are paired symmetrically. The formula used for each
pair cancels its 1/t singularity analytically, rather than by subtracting
two numerically divergent quantities. Near the origin the kernel is
evaluated from its convergent Taylor series. The default pole truncation
at p=30.5 produces discrepancies of about 1e-53 for x=4.

Direct finite-difference order differentiation of polylog at an integer
is deliberately avoided: the analytic integral supplies a stable reference.
"""

import argparse
import json
import math
from pathlib import Path

import mpmath as mp
import sympy as sp


def symbolic_checks():
    s, p = sp.symbols("s p")
    factorial_checks = 0
    for n in range(7):
        for k in range(n // 2 + 1, 9):
            falling = sp.prod(s - j for j in range(2 * k))
            actual = sp.diff(falling, s).subs(s, n)
            expected = (-1) ** (n + 1) * sp.factorial(n) * sp.factorial(2 * k - n - 1)
            assert sp.simplify(actual - expected) == 0
            factorial_checks += 1

    cs = [sp.Integer(1)] + [
        2 * (1 - sp.Integer(2) ** (1 - 2 * k)) * sp.zeta(2 * k)
        for k in range(1, 9)
    ]
    csc_series = sp.series(sp.pi * p / sp.sin(sp.pi * p), p, 0, 18).removeO()
    assert sp.expand(csc_series - sum(cs[k] * p ** (2 * k) for k in range(9))) == 0

    residue_checks = 0
    for n in range(5):
        truncation = sum(cs[k] * p ** (2 * k) for k in range(n // 2 + 1))
        kernel = (-1) ** (n + 1) * (sp.pi * p / sp.sin(sp.pi * p) - truncation) / p ** (n + 1)
        for m in range(1, 7):
            actual = sp.limit((p - m) * kernel, p, m)
            expected = sp.Integer(-1) ** (n + m + 1) / sp.Integer(m) ** n
            assert sp.simplify(actual - expected) == 0
            residue_checks += 1

    eps = sp.symbols("eps")
    es = sp.symbols("E0:7")
    ejet = sum(es[j] * eps ** j / sp.factorial(j) for j in range(7))
    product = sp.series(sp.sin(sp.pi * eps) * ejet, eps, 0, 8).removeO()
    for r in range(1, 8):
        actual = sp.expand(product).coeff(eps, r) * sp.factorial(r)
        expected = sum(
            sp.binomial(r, 2 * j + 1) * (-1) ** j * sp.pi ** (2 * j + 1) * es[r - 2 * j - 1]
            for j in range((r - 1) // 2 + 1)
        )
        assert sp.simplify(actual - expected) == 0

    # Independent composition check of the first two inverse sectors.
    z, v, w = sp.symbols("z v w", nonzero=True)
    for n in range(1, 7):
        sigma = (-1) ** n
        a = sigma / v
        b = -sigma / (sp.Integer(2) ** n * v) - 1 / v**2 - w / (2 * v**3)
        delta = a * z + b * z**2
        p_difference = v * delta + w * delta**2 / 2
        right = sigma * (z * sp.exp(-delta) - z**2 * sp.exp(-2 * delta) / sp.Integer(2)**n)
        assert sp.series(p_difference - right, z, 0, 3).removeO().expand() == 0

    return {
        "factorial_tail_checks": factorial_checks,
        "exact_csc_coefficients_checked": 9,
        "exact_residues_checked": residue_checks,
        "triangular_jet_orders_checked": 7,
        "inverse_composition_orders_checked": 6,
        "all_passed": True,
    }


class JetKernel:
    def __init__(self, dps):
        self.series_terms = max(100, dps + 20)
        self.cs = [mp.mpf(1)] + [2 * mp.altzeta(2 * k) for k in range(1, self.series_terms)]

    def truncation(self, n, p):
        return sum(self.cs[k] * p ** (2 * k) for k in range(n // 2 + 1))

    def kernel(self, n, p):
        if abs(p) < mp.mpf("0.3"):
            return (-1) ** (n + 1) * sum(
                self.cs[k] * p ** (2 * k - n - 1)
                for k in range(n // 2 + 1, self.series_terms)
            )
        return (-1) ** (n + 1) * (mp.pi * p / mp.sin(mp.pi * p) - self.truncation(n, p)) / p ** (n + 1)

    def finite_logarithmic_part(self, n, x):
        return sum(
            self.cs[k] * x ** (n - 2 * k) / mp.factorial(n - 2 * k)
            * (mp.log(x) - mp.digamma(n + 1 - 2 * k))
            for k in range(n // 2 + 1)
        )

    def principal_value_integral(self, n, x, poles):
        half = mp.mpf("0.5")
        total = mp.quad(
            lambda p: mp.exp(-x * p) * self.kernel(n, p),
            [0, mp.mpf("0.3"), half],
        )
        for m in range(1, poles + 1):
            center = mp.mpf(m)

            def pair(t):
                # p=center +/- t. The singular csc contributions combine
                # through expm1(u-v), maintaining precision at t=0.
                u = -x * t - n * mp.log1p(t / center)
                v = x * t - n * mp.log1p(-t / center)
                if t == 0:
                    singular_pair = -2 * mp.exp(-x * center) * center ** (-n) * (x + n / center)
                else:
                    singular_pair = (
                        mp.pi * mp.exp(-x * center) * center ** (-n)
                        * mp.exp(v) * mp.expm1(u - v) / mp.sin(mp.pi * t)
                    )
                plus = mp.exp(-x * (center + t)) * self.truncation(n, center + t) / (center + t) ** (n + 1)
                minus = mp.exp(-x * (center - t)) * self.truncation(n, center - t) / (center - t) ** (n + 1)
                return (-1) ** (n + 1) * ((-1) ** m * singular_pair - plus - minus)

            total += mp.quad(pair, [0, half])
        return total


def logistic_jet_reference(n, x):
    def rho(t):
        return 1 / (4 * mp.cosh(t / 2) ** 2)

    def integrand(t):
        return t ** n * (mp.log(t) - mp.digamma(n + 1)) * (rho(t - x) + (-1) ** n * rho(t + x))

    return mp.quad(integrand, [0, 1, x, x + 6, mp.inf]) / mp.factorial(n)


def numerical_checks(dps, poles):
    mp.mp.dps = dps
    kernel = JetKernel(dps)
    x = mp.mpf(4)
    # The tolerance is below the retained decimal precision and above the
    # default finite pole-tail size. It is a testing tolerance, not a bound.
    target_digits = max(12, min(dps - 15, int(4 * (poles + 0.5) / math.log(10)) - 7))
    tolerance = mp.mpf(10) ** (-target_digits)
    records = []
    for n in range(4):
        reference = logistic_jet_reference(n, x)
        finite = kernel.finite_logarithmic_part(n, x)
        pv = kernel.principal_value_integral(n, x, poles)
        actual = finite + pv
        difference = abs(actual - reference)
        assert difference < tolerance, (n, difference, tolerance)
        records.append({
            "N": n,
            "x": str(x),
            "logistic_order_jet": mp.nstr(reference, dps),
            "finite_log_part_plus_pv": mp.nstr(actual, dps),
            "absolute_difference": mp.nstr(difference, 12),
        })
    return {
        "working_decimal_precision": dps,
        "positive_poles_included": poles,
        "integration_upper_endpoint": str(poles + 0.5),
        "testing_tolerance": mp.nstr(tolerance, 6),
        "certified_interval_bounds": False,
        "checks": records,
        "all_passed": True,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=60)
    parser.add_argument("--poles", type=int, default=30)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.dps < 30 or args.poles < 15:
        parser.error("Use at least 30 decimal digits and 15 poles.")
    report = {
        "symbolic": symbolic_checks(),
        "numerical": numerical_checks(args.dps, args.poles),
    }
    rendered = json.dumps(report, indent=2)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)


if __name__ == "__main__":
    main()
