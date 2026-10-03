#!/usr/bin/env python3
"""Check the conditional A254789 inverse expansion.

Uses only SymPy and mpmath, already present in the research environment.
Tests the smooth truncated forward model, not the exact A254789 sequence.
The gamma value in numerical checks is illustrative, not certified.
"""

import json
from pathlib import Path

import mpmath as mp
import sympy as sp


def symbolic_check():
    t, s, A, B, D, E, p, q = sp.symbols("t s A B D E p q")
    u = -A / s
    v = -q / s
    w = -B / s + A**2 / (3 * s**2) - A**2 / (2 * s**3)
    r = -D / s + A * (p + q / 3) / s**2 - A * q / s**3
    k = (-E / s + p * q / s**2 - (A * B + q**2 / 2) / s**3
         + A**3 / (3 * s**4) - A**3 / (2 * s**5))
    delta = u / t + v + w * t + r * t**2 + k * t**3
    rho = sp.expand(delta * t**3)

    # Enough Taylor terms to retain all coefficients through t^3, with x=t^-3.
    residual = (
        s * delta + delta**2 * t**3 / 2 - delta**3 * t**6 / 6
        + A / t * (1 + rho / 3 - rho**2 / 9)
        + q + p * rho
        + B * t * (1 - rho / 3) + D * t**2 + E * t**3
    )
    residual = sp.expand(residual)
    for j in range(-1, 4):
        assert sp.simplify(residual.coeff(t, j)) == 0, j

    z = sp.symbols("z")
    c1 = 53 * z**2 / 90
    c2 = z * (2809 * z**3 + 20325) / 16200
    c3 = (2084278 * z**6 + 43365690 * z**3 + 21487275) / 61236000
    assert sp.simplify(c2 - c1**2 / 2 - 271 * z / 216) == 0
    assert sp.simplify(c3 - c1 * c2 + c1**3 / 3
                       - (sp.Rational(393, 1120) - 1304 * z**3 / 42525)) == 0
    assert sp.Rational(393, 1120) + sp.Rational(1, 12) == sp.Rational(1459, 3360)
    return {"residual_coefficients_minus1_through3": "all exactly zero",
            "relative_to_log_conversion": "exactly checked",
            "stirling_E_constant": "1459/3360"}


def numerical_check():
    mp.mp.dps = 180
    z = mp.airyaizero(1)
    gamma = mp.mpf("173.12670485")
    A = 3 * z
    B = 53 * z**2 / 90
    D = 271 * z / 216
    E = mp.mpf(1459) / 3360 - 1304 * z**3 / 42525
    p = mp.mpf(5) / 4
    C = mp.log(gamma * mp.sqrt(2 * mp.pi))

    def h(n):
        return (n * mp.log(4 * n / mp.e) + A * mp.root(n, 3)
                + p * mp.log(n) + C + B / mp.root(n, 3)
                + D / mp.root(n, 3)**2 + E / n)

    def hp(n):
        return (mp.log(4 * n) + A / (3 * mp.root(n, 3)**2)
                + p / n - B / (3 * n * mp.root(n, 3))
                - 2 * D / (3 * n * mp.root(n, 3)**2) - E / n**2)

    rows = []
    for power in [2, 3, 6, 12, 24, 48]:
        n = mp.mpf(10)**power
        T = h(n)
        x = T / mp.lambertw(4 * T / mp.e)
        s = mp.log(4 * x)
        q = p * mp.log(x) + C
        u = -A / s
        v = -q / s
        w = -B / s + A**2 / (3 * s**2) - A**2 / (2 * s**3)
        r = -D / s + A * (p + q / 3) / s**2 - A * q / s**3
        k = (-E / s + p * q / s**2 - (A * B + q**2 / 2) / s**3
             + A**3 / (3 * s**4) - A**3 / (2 * s**5))
        rhat = x + u * mp.root(x, 3) + v + w / mp.root(x, 3)
        rhat += r / mp.root(x, 3)**2 + k / x
        x1 = x - (h(x) - T) / hp(x)
        x2 = x1 - (h(x1) - T) / hp(x1)
        rows.append({
            "n": f"1e{power}",
            "explicit_error": mp.nstr(rhat - n, 14),
            "explicit_scaled_x_4_3_log": mp.nstr((rhat - n) * x**(mp.mpf(4)/3) * s, 14),
            "newton2_error": mp.nstr(x2 - n, 14),
            "newton2_scaled_x_5_3_log7": mp.nstr((x2 - n) * x**(mp.mpf(5)/3) * s**7, 14),
        })
    return {
        "model": "truncated logarithmic forward model h; not exact sequence",
        "gamma": "173.12670485 (illustrative, uncertified)",
        "constants": {"z": mp.nstr(z, 20), "A": mp.nstr(A, 20),
                      "B": mp.nstr(B, 20), "D": mp.nstr(D, 20),
                      "E": mp.nstr(E, 20), "C": mp.nstr(C, 20)},
        "rows": rows,
    }


if __name__ == "__main__":
    result = {"symbolic": symbolic_check(), "numeric": numerical_check()}
    rendered = json.dumps(result, indent=2)
    print(rendered)
    Path(__file__).with_suffix(".json").write_text(rendered + "\n")
