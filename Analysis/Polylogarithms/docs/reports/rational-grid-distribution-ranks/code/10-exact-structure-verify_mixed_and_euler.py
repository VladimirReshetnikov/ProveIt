#!/usr/bin/env python3
"""Reproduce the mixed-polylogarithm and Euler-sum checks in the article.

Requires Python 3.10+ and mpmath. Run from any directory:

    python code/verify_mixed_and_euler.py
    python code/verify_mixed_and_euler.py --quick

The partial-fraction checks use exact rational polynomial arithmetic.
Quadrature checks are independent high-precision numerical checks, not
interval-arithmetic error certificates and not proofs of independence.
The mathematical proofs are in article.tex.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
import json
from math import comb, factorial
from pathlib import Path
import time

import mpmath as mp


SOURCE_COMMIT = "3a6d80ed618d839915deb0d19ab687f45e81d995"
ROOT = Path(__file__).resolve().parents[1]


def mixed_coefficients(a: int, b: int) -> dict:
    """Exact coefficients of the article's all-weight mixed reduction.

    M_{a,b}(z) = sum d_j Li_{w-j,j}(z,1) + c Li_w(z)
                 + sum p_j zeta(j) Li_{w-j}(z).
    """
    if a < 1 or b < 1:
        raise ValueError("Both indices must be positive integers.")
    w = a + b
    doubles = {
        j: Fraction((-1) ** (b + 1) * comb(w - j - 1, b - 1))
        for j in range(1, a + 1)
    }
    single = Fraction((-1) ** (b + 1) * comb(w - 1, b))
    products: dict[int, Fraction] = {}
    for j in range(2, b + 1):
        products[j] = products.get(j, Fraction(0)) + Fraction(
            (-1) ** (b - j) * comb(w - j - 1, a - 1)
        )
    for j in range(2, a + 1):
        products[j] = products.get(j, Fraction(0)) + Fraction(
            (-1) ** b * comb(w - j - 1, b - 1)
        )
    return {
        "a": a,
        "b": b,
        "weight": w,
        "doubles": doubles,
        "single": single,
        "products": {j: q for j, q in products.items() if q},
    }


def coefficient_record(a: int, b: int) -> dict:
    c = mixed_coefficients(a, b)
    w = c["weight"]
    return {
        "a": a,
        "b": b,
        "weight": w,
        "double_coefficients": [
            {"indices": [w - j, j], "coefficient": str(q)}
            for j, q in c["doubles"].items()
        ],
        "Li_weight_coefficient": str(c["single"]),
        "zeta_product_coefficients": [
            {"zeta_index": j, "Li_index": w - j, "coefficient": str(q)}
            for j, q in sorted(c["products"].items())
        ],
    }


def exact_partial_fraction_check(a: int, b: int) -> bool:
    """Check the full polynomial identity, not pointwise samples.

    Homogeneity permits setting the gap k=1 and multiplying the proposed
    rational identity by x^b(x+1)^a. All coefficients of the resulting
    polynomial must be those of the constant polynomial 1.
    """
    w = a + b
    polynomial = [Fraction(0) for _ in range(w)]
    for j in range(1, b + 1):
        c = Fraction((-1) ** (b - j) * comb(w - j - 1, a - 1))
        for power in range(a + 1):
            polynomial[b - j + power] += c * comb(a, power)
    for j in range(1, a + 1):
        c = Fraction((-1) ** b * comb(w - j - 1, b - 1))
        for power in range(a - j + 1):
            polynomial[b + power] += c * comb(a - j, power)
    return polynomial == [Fraction(1)] + [Fraction(0)] * (w - 1)


def mp_fraction(q: Fraction):
    return mp.mpf(q.numerator) / q.denominator


def li(s: int, z):
    return -mp.log(1 - z) if s == 1 else mp.polylog(s, z)


def mixed_integral(a: int, b: int, z):
    """Independent one-dimensional integral for Li_{a,b}(z,z^{-1})."""
    def integrand(t):
        if t == 0 or t == 1:
            return mp.mpf(0)
        return (-mp.log(t)) ** (a - 1) * li(b, t) / (1 - z * t)

    return z * mp.quad(integrand, [0, mp.mpf("0.5"), 1]) / factorial(a - 1)


def one_color_integral(a: int, b: int, z):
    """Independent integral for Li_{a,b}(z,1)."""
    def integrand(t):
        if t == 0 or t == 1:
            return mp.mpf(0)
        return (-mp.log(t)) ** (a - 1) * li(b, z * t) / (1 - z * t)

    return z * mp.quad(integrand, [0, mp.mpf("0.5"), 1]) / factorial(a - 1)


def beta(s: int):
    return mp.im(li(s, mp.j))


def euler_integral(p: int):
    def integrand(x):
        if x == 0:
            return mp.mpf(0)
        return (-mp.log(x)) ** (p - 1) * mp.log1p(x * x) / (1 + x * x)

    return -mp.quad(integrand, [0, mp.mpf("0.5"), 1]) / factorial(p - 1)


def euler_odd_formula(p: int):
    if p < 1 or p % 2 != 1:
        raise ValueError("The closed form requires a positive odd p.")
    return (
        p * beta(p + 1)
        - 2 * beta(p) * mp.log(2)
        - mp.fsum(
            (2 - mp.mpf(2) ** (-2 * j)) * beta(p - 2 * j) * mp.zeta(2 * j + 1)
            for j in range(1, (p - 1) // 2 + 1)
        )
    )


def generator_formula(t):
    """Meromorphic E(t); callers avoid its poles and removable +/-1."""
    return (
        (mp.polygamma(1, (1 + t) / 4) - mp.polygamma(1, (3 + t) / 4)) / 16
        + mp.pi / (4 * mp.cos(mp.pi * t / 2))
        * (mp.digamma((1 + t) / 2) - mp.digamma(1))
    )


def generator_integral(t):
    if abs(mp.re(t)) >= 3:
        raise ValueError("The integral requires |Re(t)| < 3.")

    def integrand(x):
        if x == 0:
            return mp.mpf(0)
        return (x**t + x**(-t)) * mp.log1p(x * x) / (1 + x * x)

    return -mp.quad(integrand, [0, mp.mpf("0.5"), 1]) / 2


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="Use 60 rather than 80 digits.")
    parser.add_argument("--dps", type=int, help="Override working precision (minimum 40).")
    parser.add_argument("--output", type=Path, default=ROOT / "data" / "mixed_and_euler.json")
    args = parser.parse_args()
    dps = args.dps or (60 if args.quick else 80)
    if dps < 40:
        parser.error("Use at least 40 decimal working digits.")
    mp.mp.dps = dps
    display_digits = dps - 15
    tolerance = mp.mpf(10) ** (-(dps - 20))
    start = time.monotonic()

    def number(value):
        if isinstance(value, mp.mpc):
            return {"real": mp.nstr(mp.re(value), display_digits),
                    "imag": mp.nstr(mp.im(value), display_digits)}
        return mp.nstr(value, display_digits)

    all_residuals = []

    def check(name, lhs, rhs, **extra):
        residual = abs(lhs - rhs)
        all_residuals.append(residual)
        passed = residual < tolerance
        if not passed:
            raise AssertionError(f"{name}: residual {residual} exceeds {tolerance}")
        return {"name": name, "lhs": number(lhs), "rhs": number(rhs),
                "absolute_residual": number(residual), "passed": passed, **extra}

    polynomial_checks = []
    for a in range(1, 9):
        for b in range(1, 9):
            passed = exact_partial_fraction_check(a, b)
            if not passed:
                raise AssertionError(f"Exact partial-fraction failure at a={a}, b={b}")
            polynomial_checks.append({"a": a, "b": b, "passed": passed})
    print("64 exact rational polynomial identities verified.", flush=True)

    rho = mp.exp(2 * mp.pi * mp.j / 3)
    roots = {"gaussian_i": mp.j, "eisenstein_rho2": mp.conj(rho)}

    @lru_cache(maxsize=None)
    def cached_double(a, b, root_name):
        return one_color_integral(a, b, roots[root_name])

    @lru_cache(maxsize=None)
    def cached_mixed(a, b, root_name):
        return mixed_integral(a, b, roots[root_name])

    mixed_checks = []
    for root_name, z in roots.items():
        for a in range(1, 4):
            for b in range(1, 4):
                c = mixed_coefficients(a, b)
                w = a + b
                lhs = cached_mixed(a, b, root_name)
                rhs = mp_fraction(c["single"]) * li(w, z)
                rhs += mp.fsum(
                    mp_fraction(q) * cached_double(w - j, j, root_name)
                    for j, q in c["doubles"].items()
                )
                rhs += mp.fsum(
                    mp_fraction(q) * mp.zeta(j) * li(w - j, z)
                    for j, q in c["products"].items()
                )
                mixed_checks.append(check(
                    f"mixed_reduction_{root_name}_{a}_{b}", lhs, rhs,
                    root=root_name, indices=[a, b],
                    boundary="conditional outer sum" if a == 1 else "absolute outer sum",
                ))
        print(f"All a,b in 1..3 checked at {root_name}.", flush=True)

    q = lambda n, d=1: mp.mpf(n) / d
    survivor_formulas = [
        ("gaussian_real_4_1", "gaussian_i", 4, mp.re,
         -q(587, 1024) * mp.zeta(5) + q(3, 32) * mp.zeta(2) * mp.zeta(3)
         + q(135, 256) * mp.zeta(4) * mp.log(2)),
        ("gaussian_imag_5_1", "gaussian_i", 5, mp.im,
         3 * beta(6) - mp.zeta(2) * beta(4) - mp.zeta(4) * mp.catalan
         - q(5, 3072) * mp.pi**5 * mp.log(2)),
        ("eisenstein_real_4_1", "eisenstein_rho2", 4, mp.re,
         -q(281, 162) * mp.zeta(5) + q(4, 9) * mp.zeta(2) * mp.zeta(3)
         + q(20, 27) * mp.zeta(4) * mp.log(3)),
        ("eisenstein_imag_5_1", "eisenstein_rho2", 5, mp.im,
         -3 * mp.im(li(6, rho)) + mp.zeta(2) * mp.im(li(4, rho))
         + mp.zeta(4) * mp.im(li(2, rho)) + mp.pi**5 * mp.log(3) / 729),
    ]
    survivor_checks = [
        check(name, projection(cached_mixed(a, 1, root_name)), rhs)
        for name, root_name, a, projection, rhs in survivor_formulas
    ]
    print("Four asserted mixed survivors reduced and checked by quadrature.", flush=True)

    euler_checks = [
        check(f"Euler_S{p}", euler_integral(p), euler_odd_formula(p), p=p)
        for p in (1, 3, 5, 7, 9)
    ]
    generator_checks = [
        check(f"generator_{label}", generator_integral(t), generator_formula(t), argument=number(t))
        for label, t in (
            ("one_quarter", mp.mpf("0.25")),
            ("1_3", mp.mpf("1.3")),
            ("complex", mp.mpc("0.4", "0.7")),
            ("two", mp.mpf(2)),
        )
    ]
    generator_checks.append(check(
        "generator_removable_plus_one", generator_integral(mp.mpf(1)), -mp.pi**2 / 48
    ))
    generator_checks.append(check(
        "generator_removable_minus_one", generator_integral(mp.mpf(-1)), -mp.pi**2 / 48
    ))

    # Symmetric residue estimates have O(epsilon^2) analytic truncation error.
    # Their tolerance differs from equality checks for that explicit reason.
    eps = mp.mpf(10) ** (-(dps // 5))
    residue_tolerance = eps ** mp.mpf("1.5")
    residue_checks = []
    for pole in (3, 5, -3):
        n = (abs(pole) - 1) // 2
        h_n = sum((Fraction(1, j) for j in range(1, n + 1)), Fraction(0))
        exact_residue = Fraction((-1) ** (n + 1), 2) * h_n
        if pole < 0:
            exact_residue = -exact_residue
        estimate = eps * (generator_formula(pole + eps) - generator_formula(pole - eps)) / 2
        residual = abs(estimate - mp_fraction(exact_residue))
        passed = residual < residue_tolerance
        if not passed:
            raise AssertionError(f"Residue check failed at pole {pole}: {residual}")
        residue_checks.append({
            "pole": pole, "exact_residue": str(exact_residue),
            "estimate": number(estimate), "epsilon": number(eps),
            "absolute_residual": number(residual),
            "tolerance": number(residue_tolerance), "passed": passed,
        })
    print("Euler sums, meromorphic generator, and simple residues checked.", flush=True)

    result = {
        "source_commit": SOURCE_COMMIT,
        "working_decimal_digits": dps,
        "equality_tolerance": number(tolerance),
        "maximum_equality_residual": number(max(all_residuals)),
        "status": "all checks passed",
        "epistemic_status": {
            "exact": "64 rational polynomial identities; integer/rational coefficient maps",
            "numerical": "mpmath quadrature and special functions; no rigorous quadrature enclosure",
            "proofs": "See article.tex for all-weight mathematical proofs.",
            "independence": "No arithmetic-independence claim is inferred from numerical checks.",
        },
        "exact_partial_fraction_checks": polynomial_checks,
        "coefficient_tables_a_b_1_to_6": [
            coefficient_record(a, b) for a in range(1, 7) for b in range(1, 7)
        ],
        "mixed_reduction_checks": mixed_checks,
        "explicit_survivor_reductions": survivor_checks,
        "euler_sum_checks": euler_checks,
        "generator_checks": generator_checks,
        "residue_checks": residue_checks,
        "elapsed_seconds": round(time.monotonic() - start, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"Saved {args.output}", flush=True)
    print(f"Maximum equality residual: {mp.nstr(max(all_residuals), 8)}", flush=True)


if __name__ == "__main__":
    main()
