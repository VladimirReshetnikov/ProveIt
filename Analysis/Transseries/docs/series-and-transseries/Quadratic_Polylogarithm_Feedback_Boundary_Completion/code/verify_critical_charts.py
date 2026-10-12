#!/usr/bin/env python3
"""Independent high-precision checks of the critical feedback inverse charts.

The reference values solve the polylogarithmic equation directly.  The
asymptotic formulas are used only as starting values, not as reference
evaluators.  Exact symbolic checks verify the marginal-order logarithmic
polynomials and the first two transfer corrections.
"""

from pathlib import Path
import json
import argparse

import mpmath as mp
import sympy as sp


mp.mp.dps = 180
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent.parent / "data")
args = parser.parse_args()
ROOT = args.output_dir
ROOT.mkdir(parents=True, exist_ok=True)


def text(value):
    return mp.nstr(value, 45)


def kfun(s, x):
    return mp.zeta(s - 1) * x + x * x / 2 - (
        mp.zeta(s) - mp.polylog(s, mp.exp(-x))
    )


def solve(s, delta, guess):
    a = mp.zeta(s - 1)

    def equation(x):
        return kfun(s, x) - (a + x) * delta + delta * delta / 2

    value = mp.findroot(
        equation,
        (guess * mp.mpf("0.9"), guess * mp.mpf("1.1")),
        solver="secant",
        tol=mp.mpf("1e-145"),
        maxsteps=60,
        verify=False,
    )
    residual = abs(equation(value)) / delta
    assert abs(mp.im(value)) < mp.mpf("1e-130")
    assert residual < mp.mpf("1e-110"), (s, delta, residual)
    return mp.re(value), residual


rows = []
for s_str in ("2.5", "3", "3.5", "4"):
    s = mp.mpf(s_str)
    a = mp.zeta(s - 1)
    for exponent in (8, 16, 32):
        delta = mp.power(10, -exponent)
        extras = {}
        if s < 3:
            alpha = s - 1
            beta = 2 - alpha
            c = mp.gamma(1 - s)
            b = (1 + mp.zeta(s - 2)) / 2
            q = (a * delta / c) ** (1 / alpha)
            z = q**beta
            leading = q
            correction = q * (1 - b * z / (alpha * c))
            second = q * (
                1
                - b * z / (alpha * c)
                + (5 - alpha) * b * b * z * z / (2 * alpha**2 * c**2)
                + q / (alpha * a)
            )
            expected = -b / (alpha * c)
            normalize = lambda x: (x / q - 1) / z
        elif s == 3:
            lam = -mp.lambertw(-4 * a * delta * mp.exp(-5), -1) / 2
            q = mp.sqrt(2 * a * delta / lam)
            leading = q
            correction = q + q * q * (lam / a - mp.mpf(1) / 6) / (2 * lam - 1)
            second = correction
            expected = 1 / (2 * a)
            normalize = lambda x: (x - q) / (q * q)
            extras["Lambert_Lambda"] = text(lam)
            ell = mp.log(1 / delta)
            kval = mp.log(ell) + 5 - mp.log(4 * a)
            log0 = 2 * mp.sqrt(a * delta / ell)
            log1 = log0 * (1 - kval / (2 * ell))
            log2 = log0 * (
                1 - kval / (2 * ell)
                + (3 * kval * kval / 8 - kval / 2) / (ell * ell)
            )
            extras["core_logarithmic_relative_errors"] = [
                text(abs(value / q - 1)) for value in (log0, log1, log2)
            ]
        elif s < 4:
            mu = s - 3
            b = (1 + mp.zeta(s - 2)) / 2
            c = mp.gamma(1 - s)
            q = mp.sqrt(a * delta / b)
            z = q**mu
            leading = q
            correction = q * (1 - c * z / (2 * b))
            second = q * (
                1 - c * z / (2 * b)
                + (1 / (2 * a) + mp.zeta(s - 3) / (12 * b)) * q
                + (2 * mu + 3) * (c / b)**2 * z * z / 8
            )
            expected = -c / (2 * b)
            normalize = lambda x: (x / q - 1) / z
        else:
            b = (1 + mp.zeta(s - 2)) / 2
            q = mp.sqrt(a * delta / b)
            ellq = mp.log(1 / q)
            leading = q
            correction = q + q * q * (
                ellq / (12 * b) + 1 / (2 * a) + mp.mpf(11) / (72 * b)
            )
            second = correction
            expected = 1 / (2 * a) + mp.mpf(11) / (72 * b)
            normalize = lambda x: (x - q) / (q * q) - ellq / (12 * b)

        actual, residual = solve(s, delta, q)
        errors = [abs(value / actual - 1) for value in (leading, correction, second)]
        assert errors[1] < errors[0]
        assert errors[2] <= errors[1]
        if exponent == 32 and s != 3:
            assert abs(normalize(actual) - expected) < mp.mpf("1e-7")
        if s == 3:
            extras["corrected_error_over_tau_cubed_Lambda"] = text(
                (actual - correction) / (q**3 * lam)
            )
            extras["expected_error_ratio_limit"] = text(-1 / (8 * a * a))
        rows.append({
            "s": s_str,
            "delta": text(delta),
            "reference_x": text(actual),
            "scaled_equation_residual": text(residual),
            "relative_errors_leading_first_second": list(map(text, errors)),
            "normalized_first_correction": text(normalize(actual)),
            "expected_normalized_limit": text(expected),
            **extras,
        })


u, kval, psi, psi1 = sp.symbols("u K psi psi1")
polynomials = [sp.Integer(1)]
for j in (1, 2, 3, 4):
    expression = (1 + u)**(-sp.Rational(3, 2)) * (kval + sp.log(1 + u))**j
    coefficient = sp.expand(sp.series(expression, u, 0, j).removeO()).coeff(u, j - 1)
    polynomials.append(sp.expand(-coefficient / (2 * j)))
assert sp.expand(polynomials[1] + kval / 2) == 0
assert sp.expand(polynomials[2] - 3 * kval**2 / 8 + kval / 2) == 0


def differential_product(poly, start, count):
    value = poly
    for ell in range(count):
        value = sp.diff(value, kval) - (start + sp.Rational(1, 2) + ell) * value
    return sp.expand(value)


multipliers = [sp.Integer(1), -psi, (psi**2 - psi1) / 2]
transferred = []
for n in range(3):
    value = sum(
        multipliers[n - j] * differential_product(polynomials[j], j, n - j)
        for j in range(n + 1)
    )
    transferred.append(sp.expand(value))
assert sp.expand(transferred[1] - (psi - kval) / 2) == 0
assert sp.expand(
    transferred[2] - (3 * (kval - psi)**2 / 8 - (kval - psi) / 2 - 3 * psi1 / 8)
) == 0

output = {
    "precision_decimal_digits": mp.mp.dps,
    "reference_method": "Direct mpmath polylogarithm evaluation and secant inversion",
    "numeric_cases": rows,
    "core_log_polynomials": [str(poly) for poly in polynomials],
    "transferred_log_polynomials_through_second_order": list(map(str, transferred)),
    "symbolic_assertions": "passed",
}
(ROOT / "critical_chart_checks.json").write_text(json.dumps(output, indent=2) + "\n")
print(json.dumps({
    "numeric_cases": len(rows),
    "symbolic_assertions": "passed",
    "max_scaled_residual": text(max(mp.mpf(row["scaled_equation_residual"]) for row in rows)),
    "output": str(ROOT / "critical_chart_checks.json"),
}, indent=2))
