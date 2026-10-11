#!/usr/bin/env python3
"""Independent exact and numerical checks of the spectral-polynomial examples.

The theorems are proved in derivative_polynomial_spectral.tex.  These checks
verify the two displayed local computations and compare a finite part, computed
from an independently regularized integrand, with its zeta-derivative value.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp
import sympy as sy


def run_checks() -> dict:
    v, n, gamma = sy.symbols("v n gamma")
    h = sy.symbols("h0:5")
    x = sy.symbols("H1:6")
    zeta = {k: sy.Symbol(f"z{k}") for k in range(2, 7)}
    psi = -1 / v + sum(h[k] * v**k for k in range(5))
    substitutions = {
        h[0]: x[0] - gamma,
        h[1]: x[1] + zeta[2],
        h[2]: x[2] - zeta[3],
        h[3]: x[3] + zeta[4],
        h[4]: x[4] - zeta[5],
    }

    trigamma_square = sy.expand(sy.diff(psi, v) ** 2)
    mixed = sy.expand(psi * sy.diff(psi, v) ** 2)
    expected_square = {4: 1, 3: 0, 2: 2 * h[1], 1: 4 * h[2]}
    expected_mixed = {
        5: -1,
        4: h[0],
        3: -h[1],
        2: 2 * h[0] * h[1] - 3 * h[2],
        1: 4 * h[0] * h[2] + h[1] ** 2 - 5 * h[3],
    }
    for polynomial, expected in (
        (trigamma_square, expected_square),
        (mixed, expected_mixed),
    ):
        for pole, coefficient in expected.items():
            assert sy.expand(polynomial.coeff(v, -pole) - coefficient) == 0

    residue = sy.expand(mixed.coeff(v, -1).subs(substitutions))
    forward = residue.subs(
        {x[k]: x[k] + n ** (-k - 1) for k in range(4)}, simultaneous=True
    )
    difference = sy.expand(forward - residue)
    expected_difference = (
        4 * (x[2] - zeta[3]) / n
        + 2 * (x[1] + zeta[2]) / n**2
        + 4 * (x[0] - gamma) / n**3
    )
    assert sy.expand(difference - expected_difference) == 0
    # The frozen residue is zero using zeta(2)^2 = (5/2) zeta(4).
    frozen = residue.subs({x[k]: zeta[k + 1] for k in range(1, 4)})
    assert sy.expand(frozen).subs(zeta[2] ** 2, sy.Rational(5, 2) * zeta[4]) == 0

    sixth_polynomial = sy.expand(psi**2 * sy.diff(psi, v) ** 2)
    sixth_residue = (
        4 * h[0] ** 2 * h[2]
        + 2 * h[0] * h[1] ** 2
        - 10 * h[0] * h[3]
        - 6 * h[1] * h[2]
        + 6 * h[4]
    )
    assert sy.expand(sixth_polynomial.coeff(v, -1) - sixth_residue) == 0
    sixth_e1 = sy.diff(sixth_residue.subs(substitutions), x[0])
    sixth_tail_decomposition = (
        8 * (x[0] - gamma) * (x[2] - zeta[3])
        + 2 * (x[1] - zeta[2]) * (x[1] + 3 * zeta[2])
        - 10 * (x[3] - zeta[4])
    )
    assert sy.expand(sixth_e1 - sixth_tail_decomposition).subs(
        zeta[2] ** 2, sy.Rational(5, 2) * zeta[4]
    ) == 0

    mp.mp.dps = 65
    z2, z3 = mp.zeta(2), mp.zeta(3)
    regular_coefficients = [
        (-1) ** k * (k + 1) * mp.zeta(k + 2) for k in range(14)
    ]

    def regular_integrand(t):
        if t < mp.mpf("1e-8"):
            # Remove the three singular terms algebraically.  A local power
            # series avoids cancellation inside arbitrary-precision quadrature.
            a = regular_coefficients
            return 2 * sum(a[k] * t ** (k - 2) for k in range(2, len(a))) + sum(
                a[k] * a[j] * t ** (k + j)
                for k in range(len(a))
                for j in range(len(a))
            )
        return mp.polygamma(1, t) ** 2 - t**-4 - 2 * z2 * t**-2 + 4 * z3 / t

    finite_part = mp.quad(
        regular_integrand, [0, mp.mpf("0.001"), mp.mpf("0.1"), 1]
    ) - mp.mpf(1) / 3 - 2 * z2
    spectral_value = 2 * z3 + 4 * mp.diff(mp.zeta, 3)
    error = abs(finite_part - spectral_value)
    assert error < mp.mpf("1e-40")
    return {
        "status": "passed",
        "exact_principal_coefficients_checked": len(expected_square)
        + len(expected_mixed),
        "mixed_residue_difference": str(difference),
        "mixed_frozen_residue_checked": True,
        "sixth_coordinate_residue_and_tail_decomposition_checked": True,
        "trigamma_square_finite_part": mp.nstr(finite_part, 55),
        "trigamma_square_spectral_value": mp.nstr(spectral_value, 55),
        "absolute_difference": mp.nstr(error, 8),
        "working_decimal_digits": mp.mp.dps,
        "numerical_method": "independent quadrature after local Laurent subtraction",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    report = run_checks()
    rendered = json.dumps(report, indent=2) + "\n"
    if arguments.output:
        arguments.output.write_text(rendered)
    print(rendered, end="")
