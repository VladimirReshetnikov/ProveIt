#!/usr/bin/env python3
"""Independent empirical checks for the multiple-resolvent identities.

Checks the Gamma convolution (mr:ck), the exponential moment (mr:expmean),
and the log-Gamma transform (mr:logGamma) in sections/02_resolvents.tex.

This is a numerical diagnostic, not an interval calculation or a proof.
All input decimals are parsed exactly as decimal strings before mpmath
rounding.  The direct integral uses cotangent resolvents and their interval
logarithms, independently of the sine/Gamma formula.  Since Im(R_z) has
the same sign as Im(z), the principal logarithm agrees with the interval
branch normalized by Log(R_z(x))-log(x) -> 0 as x -> 0+.

Run:
    python verify_multiple_resolvents.py --output multiple_resolvents.json

Dependencies: Python >= 3.10 and mpmath.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
import json
import platform
from pathlib import Path
import time

import mpmath as mp


def cdec(re: str, im: str = "0"):
    return mp.mpc(mp.mpf(re), mp.mpf(im))


def pack(value):
    z = mp.mpc(value)
    return {
        "real": mp.nstr(z.real, mp.mp.dps),
        "imag": mp.nstr(z.imag, mp.mp.dps),
    }


def realstr(value):
    return mp.nstr(value, mp.mp.dps)


def binomial_coefficients(lam, q, cutoff):
    result = [mp.mpc(1)]
    for n in range(cutoff):
        result.append(result[-1] * q * (lam + n) / (n + 1))
    return result


def convolve_truncated(left, right, cutoff):
    return [
        mp.fsum(left[j] * right[n - j] for j in range(n + 1))
        for n in range(cutoff + 1)
    ]


def make_gamma_coefficients(a, b):
    prefactor = (
        mp.exp(mp.pi * mp.j * (a - b) / 2)
        * mp.gamma(1 + a + b)
        / mp.power(2 * mp.pi, a + b)
    )

    @lru_cache(maxsize=None)
    def coefficient(k):
        # rgamma is entire; for integer a,b it gives the exact finite support
        # without attempting to evaluate Gamma at a nonpositive integer.
        sign = -1 if k % 2 else 1
        return (
            prefactor
            * sign
            * mp.rgamma(1 + a - k)
            * mp.rgamma(1 + b + k)
        )

    return coefficient


def interval_kernel(x, zs, exponents):
    if x == 0 or x == 1:
        # Every test below has positive real total exponent.
        return mp.mpc(0)
    cotangent = mp.pi * mp.cot(mp.pi * x)
    logarithm = mp.fsum(
        lam * mp.log(1 / (cotangent - z))
        for z, lam in zip(zs, exponents)
    )
    return mp.exp(logarithm)


def integrate(func):
    return mp.quad(
        func,
        [mp.mpf(0), mp.mpf(1) / 8, mp.mpf(1) / 2,
         mp.mpf(7) / 8, mp.mpf(1)],
        method="tanh-sinh",
    )


def gamma_convolution_check(cutoff, short_cutoff):
    signs = [1, 1, -1]
    qs = [cdec("0.25", "0.10"), cdec("-0.32", "0.20"),
          cdec("0.20", "-0.25")]
    exponents = [cdec("0.70", "0.20"), cdec("-0.20", "0.13"),
                 cdec("1.10", "-0.17")]
    zs = [eps * mp.pi * mp.j * (1 + q) / (1 - q)
          for eps, q in zip(signs, qs)]
    assert all(abs(q) <= mp.mpf("0.4") for q in qs)
    assert all(mp.sign(z.imag) == eps for z, eps in zip(zs, signs))
    a, b = exponents[0] + exponents[1], exponents[2]
    assert (a + b).real > 0
    upper0 = binomial_coefficients(exponents[0], qs[0], cutoff)
    upper1 = binomial_coefficients(exponents[1], qs[1], cutoff)
    upper = convolve_truncated(upper0, upper1, cutoff)
    lower = binomial_coefficients(exponents[2], qs[2], cutoff)
    normalizer = mp.exp(mp.fsum(
        lam * mp.log(1 - q) for lam, q in zip(exponents, qs)
    ))
    gamma_coefficient = make_gamma_coefficients(a, b)
    for j in range(-cutoff - 2, cutoff + 3):
        gamma_coefficient(j)

    def convolution(k, stop):
        return normalizer * mp.fsum(
            upper[n] * mp.fsum(
                lower[m] * gamma_coefficient(k - n + m)
                for m in range(stop + 1)
            )
            for n in range(stop + 1)
        )

    checks = []
    for k in range(-2, 3):
        full = convolution(k, cutoff)
        short = convolution(k, short_cutoff)
        direct = integrate(
            lambda x: interval_kernel(x, zs, exponents)
            * mp.exp(-2 * mp.pi * mp.j * k * x)
        )
        checks.append({
            "k": k,
            "gamma_convolution": pack(full),
            "direct_cotangent_quadrature": pack(direct),
            "absolute_difference": realstr(abs(full - direct)),
            "shorter_truncation_difference": realstr(abs(full - short)),
        })
    return {
        "formula": "mr:ck",
        "parameters": [
            {"sign": eps, "q": pack(q), "abs_q": realstr(abs(q)),
             "z": pack(z), "lambda": pack(lam)}
            for eps, q, z, lam in zip(signs, qs, zs, exponents)
        ],
        "a": pack(a), "b": pack(b), "total_exponent": pack(a + b),
        "B": pack(normalizer),
        "truncation": {
            "shape": "rectangle, endpoints included",
            "n": [0, cutoff], "m": [0, cutoff],
            "shorter_n": [0, short_cutoff],
            "shorter_m": [0, short_cutoff],
            "upper_coefficients": "finite convolution of two binomial series",
            "lower_coefficients": "one binomial series",
            "gamma_cache_size": gamma_coefficient.cache_info().currsize,
        },
        "checks": checks,
        "maximum_absolute_difference": realstr(max(
            mp.mpf(item["absolute_difference"]) for item in checks
        )),
    }


def finite_spectrum_checks():
    a, b = mp.mpf(2), mp.mpf(1)
    zs = [mp.pi * mp.j, -mp.pi * mp.j]
    exponents = [a, b]
    gamma_coefficient = make_gamma_coefficients(a, b)
    coefficients = {k: gamma_coefficient(k) for k in range(-1, 3)}
    outside_values = {k: gamma_coefficient(k)
                      for k in [-8, -3, -2, 3, 4, 8]}
    assert all(value == 0 for value in outside_values.values())
    base = mp.j / (8 * mp.pi**3)
    explicit_coefficients = {-1: -base, 0: 3 * base, 1: -3 * base, 2: base}
    finite_formula_error = max(abs(coefficients[k] - explicit_coefficients[k])
                               for k in coefficients)

    def exponential_beta(t):
        return (
            mp.exp(mp.pi * mp.j * (a - b) / 2 + t / 2)
            * mp.gamma(1 + a + b) / mp.power(2 * mp.pi, a + b)
            * mp.rgamma(1 + a + t / (2 * mp.pi * mp.j))
            * mp.rgamma(1 + b - t / (2 * mp.pi * mp.j))
        )

    def exprel(z):
        return mp.mpc(1) if z == 0 else mp.expm1(z) / z

    exponential_checks = []
    for label, t in [
        ("mean", mp.mpc(0)),
        ("nonreal exponential parameter", cdec("0.45", "0.70")),
        ("exact Gamma zero", 4 * mp.pi * mp.j),
        ("finite-spectrum mode k=2", -4 * mp.pi * mp.j),
    ]:
        beta_value = exponential_beta(t)
        finite_value = mp.fsum(
            ck * exprel(t + 2 * mp.pi * mp.j * k)
            for k, ck in coefficients.items()
        )
        direct_value = integrate(
            lambda x: mp.exp(t * x) * interval_kernel(x, zs, exponents)
        )
        exponential_checks.append({
            "case": label, "t": pack(t),
            "beta_rgamma_formula": pack(beta_value),
            "finite_fourier_integral": pack(finite_value),
            "direct_cotangent_quadrature": pack(direct_value),
            "beta_vs_direct_absolute_difference": realstr(abs(beta_value - direct_value)),
            "beta_vs_finite_absolute_difference": realstr(abs(beta_value - finite_value)),
        })

    sigma_plus, sigma_minus = -2 * mp.pi * mp.j, 2 * mp.pi * mp.j
    ds = {
        "plus": mp.fsum(coefficients[n] / n for n in [1, 2]),
        "minus": coefficients[-1],
    }
    dprimes = {
        "plus": -mp.fsum(coefficients[n] * mp.log(n) / n for n in [1, 2]),
        "minus": mp.mpc(0),
    }
    loggamma_spectral = (
        mp.log(2 * mp.pi) * coefficients[0] / 2
        + ((mp.euler + mp.log(sigma_plus)) * ds["plus"] - dprimes["plus"])
        / sigma_plus
        + ((mp.euler + mp.log(sigma_minus)) * ds["minus"] - dprimes["minus"])
        / sigma_minus
    )
    loggamma_direct = integrate(
        lambda x: mp.loggamma(x) * interval_kernel(x, zs, exponents)
        if 0 < x < 1 else mp.mpc(0)
    )
    loggamma_elementary = (
        (3 * (mp.euler + mp.log(2 * mp.pi)) - mp.log(2)) / (32 * mp.pi**4)
        + mp.j * (12 * mp.log(2 * mp.pi) - 7) / (64 * mp.pi**3)
    )
    return {
        "parameters": {"q_plus": pack(0), "q_minus": pack(0),
                       "alpha": pack(a), "beta": pack(b)},
        "finite_support": [-1, 0, 1, 2],
        "finite_coefficients": {str(k): pack(value)
                                for k, value in coefficients.items()},
        "explicit_coefficient_formula":
            "(c_-1,c_0,c_1,c_2)=i/(8*pi^3)*(-1,3,-3,1)",
        "explicit_coefficient_maximum_difference": realstr(finite_formula_error),
        "sampled_exact_rgamma_zeros": {str(k): pack(value)
                                      for k, value in outside_values.items()},
        "exponential_moment": {"formula": "mr:expmean",
                               "checks": exponential_checks},
        "loggamma_transform": {
            "formula": "mr:logGamma",
            "D_plus_at_1": pack(ds["plus"]),
            "D_minus_at_1": pack(ds["minus"]),
            "D_plus_derivative_at_1": pack(dprimes["plus"]),
            "D_minus_derivative_at_1": pack(dprimes["minus"]),
            "spectral_formula": pack(loggamma_spectral),
            "direct_cotangent_quadrature": pack(loggamma_direct),
            "elementary_formula":
                "[3*(EulerGamma+log(2*pi))-log(2)]/(32*pi^4)"
                "+i*[12*log(2*pi)-7]/(64*pi^3)",
            "elementary_value": pack(loggamma_elementary),
            "spectral_vs_direct_absolute_difference":
                realstr(abs(loggamma_spectral - loggamma_direct)),
            "spectral_vs_elementary_absolute_difference":
                realstr(abs(loggamma_spectral - loggamma_elementary)),
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=80)
    parser.add_argument("--cutoff", type=int, default=160)
    parser.add_argument("--short-cutoff", type=int, default=120)
    parser.add_argument("--output", type=Path, default=Path("multiple_resolvents.json"))
    args = parser.parse_args()
    if not 0 <= args.short_cutoff < args.cutoff:
        parser.error("require 0 <= short-cutoff < cutoff")
    mp.mp.dps = args.dps
    started = time.perf_counter()
    output = {
        "purpose": "Independent numerical diagnostics for the multiple-resolvent formulas",
        "status": "empirical only; no certified error bounds or interval arithmetic",
        "source": "output/research_package/sections/02_resolvents.tex",
        "python_version": platform.python_version(),
        "mpmath_version": mp.__version__,
        "working_decimal_precision": args.dps,
        "quadrature": {
            "algorithm": "mpmath tanh-sinh",
            "subintervals": ["0", "1/8", "1/2", "7/8", "1"],
            "kernel": "exp(sum_j lambda_j*principal_log(1/(pi*cot(pi*x)-z_j)))",
            "branch": "principal Log agrees with the normalized interval branch",
        },
        "gamma_convolution": gamma_convolution_check(args.cutoff, args.short_cutoff),
        "finite_spectrum": finite_spectrum_checks(),
    }
    output["elapsed_seconds"] = round(time.perf_counter() - started, 3)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "output": str(args.output),
        "working_decimal_precision": args.dps,
        "gamma_convolution_maximum_absolute_difference":
            output["gamma_convolution"]["maximum_absolute_difference"],
        "loggamma_spectral_vs_direct_absolute_difference":
            output["finite_spectrum"]["loggamma_transform"]
            ["spectral_vs_direct_absolute_difference"],
        "elapsed_seconds": output["elapsed_seconds"],
        "status": output["status"],
    }, indent=2))


if __name__ == "__main__":
    main()
