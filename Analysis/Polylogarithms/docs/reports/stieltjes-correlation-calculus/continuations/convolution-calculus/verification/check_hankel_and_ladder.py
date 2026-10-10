#!/usr/bin/env python3
"""Numerical diagnostics for the Stieltjes Hankel and Hurwitz-ladder theorems.

The article contains the proofs. These high-precision computations are NOT
interval certificates and do not establish equality by numerical agreement.

Run from any working directory:
    python verification/check_hankel_and_ladder.py

Requires mpmath. Results are written beside this script by default.
"""
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import argparse
import json
import platform

import mpmath as mp

REPOSITORY_COMMIT = "570b0567f311cf1890865065896be2665f469e4f"


def fmt(value, digits=48):
    if isinstance(value, (mp.mpc, complex)):
        return {"real": mp.nstr(mp.re(value), digits),
                "imag": mp.nstr(mp.im(value), digits)}
    return mp.nstr(value, digits)


def relative_error(actual, expected):
    return abs(actual - expected) / max(abs(actual), abs(expected), mp.mpf("1e-100"))


def check_close(actual, expected, tolerance=mp.mpf("1e-48")):
    err = relative_error(actual, expected)
    assert err < tolerance, (fmt(actual), fmt(expected), fmt(err))
    return err


def complete_homogeneous(k, max_order):
    """Exact coefficients of product_(j=1)^k (1-z/j)^(-1)."""
    values = [Fraction(0) for _ in range(max_order + 1)]
    values[0] = Fraction(1)
    for j in range(1, k + 1):
        for r in range(1, max_order + 1):
            values[r] += values[r - 1] / j
    return values


def mp_fraction(value):
    return mp.mpf(value.numerator) / value.denominator


def zeta_moments(p, a, max_order):
    """Infinite discrete log moments, evaluated by spectral differentiation."""
    return [
        (-1) ** n * mp.diff(lambda s: mp.zeta(s, a), p, n)
        for n in range(max_order + 1)
    ]


def determinant_from_moments(moments, d):
    return mp.det(mp.matrix([[moments[i + j] for j in range(d)]
                             for i in range(d)]))


def tuple_data(a, indices):
    points = [a + m for m in indices]
    product = mp.fprod(points)
    vandermonde = mp.fprod(
        mp.log(points[j] / points[i]) ** 2
        for i in range(len(points)) for j in range(i + 1, len(points))
    )
    return product, vandermonde


def leading_data(a, d):
    a0, v0 = tuple_data(a, tuple(range(d)))
    rho1 = (a + d - 1) / (a + d)
    rho2 = (a + d - 1) / (a + d + 1)
    c1 = mp.fprod(
        (mp.log((a + d) / (a + j)) /
         mp.log((a + d - 1) / (a + j))) ** 2
        for j in range(d - 1)
    )
    return a0, v0, rho1, rho2, c1


def transform_checks():
    records = []
    for a_text, k in [("0.7", 1), ("1.3", 2), ("0.4", 3)]:
        a = mp.mpf(a_text)
        p = mp.mpf(k + 1)
        order = 4
        # This route differentiates mpmath's Stieltjes integral in a,
        # independently of the spectral-zeta moment evaluator.
        raw = [
            mp.diff(lambda x: mp.stieltjes(n, x), a, k)
            for n in range(order + 1)
        ]
        f = [(-1) ** k * x / mp.factorial(k) for x in raw]
        h = complete_homogeneous(k, order)
        compensated = [
            mp.fsum(
                mp.factorial(n) / mp.factorial(n - r) *
                mp_fraction(h[r]) * f[n - r]
                for r in range(n + 1)
            )
            for n in range(order + 1)
        ]
        moments = zeta_moments(p, a, order)
        errors = [check_close(compensated[n], moments[n])
                  for n in range(order + 1)]
        harmonic = {r: mp.fsum(mp.mpf(j) ** (-r)
                              for j in range(1, k + 1))
                    for r in [2, 3, 4]}
        h2, h3, h4 = harmonic[2], harmonic[3], harmonic[4]
        compensated2 = f[0] * f[2] - f[1] ** 2 + h2 * f[0] ** 2
        determinant2 = determinant_from_moments(moments, 2)
        error2 = check_close(compensated2, determinant2)
        translated = [
            f[0],
            f[1],
            f[2] + h2 * f[0],
            f[3] + 3 * h2 * f[1] + 2 * h3 * f[0],
            f[4] + 6 * h2 * f[2] + 8 * h3 * f[1]
            + (3 * h2 ** 2 + 6 * h4) * f[0],
        ]
        determinant3 = determinant_from_moments(moments, 3)
        error3 = check_close(
            determinant_from_moments(translated, 3), determinant3
        )
        lower2 = (a * (a + 1)) ** (-p) * mp.log(1 + 1 / a) ** 2
        assert determinant2 > lower2 > 0
        assert determinant3 > 0
        records.append({
            "a": a_text,
            "k": k,
            "raw_gamma_parameter_derivatives": [fmt(x) for x in raw],
            "compensated_log_moments": [fmt(x) for x in compensated],
            "spectral_zeta_moments": [fmt(x) for x in moments],
            "coefficient_relative_errors": [fmt(x) for x in errors],
            "determinant_d2": fmt(determinant2),
            "strict_d2_lower_bound": fmt(lower2),
            "d2_compensated_formula_relative_error": fmt(error2),
            "determinant_d3": fmt(determinant3),
            "d3_translated_formula_relative_error": fmt(error3),
            "log_support_minimum": fmt(mp.log(a)),
        })
    return records


def cauchy_binet_checks():
    records = []
    for a_text, p_text, d in [("0.7", "3", 2), ("0.7", "3", 3),
                              ("1.3", "4", 2), ("1.3", "4", 3)]:
        a, p = mp.mpf(a_text), mp.mpf(p_text)
        truncation = 8
        finite_moments = [
            mp.fsum(mp.log(a + m) ** n * (a + m) ** (-p)
                    for m in range(truncation))
            for n in range(2 * d - 1)
        ]
        finite_determinant = determinant_from_moments(finite_moments, d)
        tuple_sum = mp.fsum(
            vandermonde * product ** (-p)
            for product, vandermonde in
            (tuple_data(a, indices)
             for indices in combinations(range(truncation), d))
        )
        error = check_close(finite_determinant, tuple_sum)
        full_determinant = determinant_from_moments(
            zeta_moments(p, a, 2 * d - 2), d)
        a0, v0, _, _, _ = leading_data(a, d)
        first_term = v0 * a0 ** (-p)
        assert full_determinant > finite_determinant > first_term > 0
        records.append({
            "a": a_text, "p": p_text, "d": d,
            "finite_support_size": truncation,
            "finite_gram_determinant": fmt(finite_determinant),
            "finite_cauchy_binet_sum": fmt(tuple_sum),
            "relative_error": fmt(error),
            "infinite_gram_determinant": fmt(full_determinant),
            "strict_first_tuple_lower_bound": fmt(first_term),
        })
    return records


def tuple_order_checks():
    records = []
    for a_text in ["0.1", "1", "10", "100"]:
        a = mp.mpf(a_text)
        for d in range(1, 6):
            tuples = list(combinations(range(d + 3), d))
            ranked = sorted(tuples, key=lambda indices: tuple_data(a, indices)[0])
            expected = [
                tuple(range(d)),
                tuple(range(d - 1)) + (d,),
                tuple(range(d - 1)) + (d + 1,),
            ]
            assert ranked[:3] == expected
            records.append({"a": a_text, "d": d,
                            "first_three_tuples": ranked[:3]})
    return records


def asymptotic_checks():
    records = []
    p0 = mp.mpf(2)
    for a_text in ["0.7", "2.3"]:
        a = mp.mpf(a_text)
        for d in [1, 2, 3]:
            a0, v0, rho1, rho2, c1 = leading_data(a, d)
            base_d = determinant_from_moments(
                zeta_moments(p0, a, 2 * d - 2), d)
            e0 = base_d / (v0 * a0 ** (-p0)) - 1 - c1 * rho1 ** p0
            assert e0 > 0
            samples = []
            for p_int in [2, 6, 12, 24, 40]:
                p = mp.mpf(p_int)
                det = determinant_from_moments(
                    zeta_moments(p, a, 2 * d - 2), d)
                normalized = det / (v0 * a0 ** (-p))
                first_correction = c1 * rho1 ** p
                remainder = normalized - 1 - first_correction
                bound = e0 * rho2 ** (p - p0)
                assert remainder > 0
                # p=p0 is equality; allow only arithmetic roundoff there.
                assert remainder <= bound * (1 + mp.mpf("1e-48"))
                samples.append({
                    "p": p_int,
                    "normalized_determinant": fmt(normalized),
                    "first_correction": fmt(first_correction),
                    "positive_remainder": fmt(remainder),
                    "explicit_remainder_bound": fmt(bound),
                    "remainder_to_bound_ratio": fmt(remainder / bound),
                })
            records.append({
                "a": a_text, "d": d, "p0": 2,
                "A0": fmt(a0), "V0": fmt(v0),
                "rho1": fmt(rho1), "rho2": fmt(rho2), "C1": fmt(c1),
                "E_at_p0": fmt(e0), "samples": samples,
            })
    return records


def ladder_checks():
    records = []
    cases = [
        (mp.mpf("0.1"), [100, 400]),
        (mp.mpf("0.5"), [40, 150]),
        (mp.mpf(1), [40, 120]),
        (mp.mpf(2), [30, 80]),
        (mp.mpc("0.7", "0.9"), [40, 100]),
        (mp.mpc("0.25", "2"), [40, 150]),
    ]
    for z, truncations in cases:
        sigma = mp.re(z)
        target = (mp.loggamma(z) - (z - mp.mpf("0.5")) * mp.log(z)
                  + z - mp.log(2 * mp.pi) / 2)
        terms = [
            mp.mpf(n - 1) * mp.zeta(n, z + 1) / (2 * n * (n + 1))
            for n in range(2, max(truncations) + 1)
        ]
        samples = []
        for truncation in truncations:
            partial = mp.fsum(terms[:truncation - 1])
            residual = abs(target - partial)
            zeta_bound = mp.zeta(truncation, sigma + 1) / (
                2 * (truncation + 1) * sigma)
            elementary_bound = (
                (sigma + 1) ** (-truncation)
                + (sigma + 1) ** (1 - truncation) / (truncation - 1)
            ) / (2 * (truncation + 1) * sigma)
            assert residual <= zeta_bound <= elementary_bound
            samples.append({
                "N": truncation,
                "partial_ladder_sum": fmt(partial),
                "absolute_residual": fmt(residual),
                "zeta_tail_bound": fmt(zeta_bound),
                "elementary_tail_bound": fmt(elementary_bound),
            })
        records.append({"z": fmt(z), "sigma": fmt(sigma),
                        "binet_remainder": fmt(target), "samples": samples})
    divergent_terms = []
    for n in [10, 20, 40]:
        term = mp.mpf(n - 1) * mp.zeta(n, mp.mpf("0.5")) / (2 * n * (n + 1))
        divergent_terms.append({"n": n, "term_at_z_minus_half": fmt(term)})
    return {"convergent_cases": records,
            "domain_counterexample": {
                "z": "-1/2",
                "identity": "zeta(n,1/2)=(2^n-1)*zeta(n)",
                "terms_fail_to_tend_to_zero": divergent_terms,
            }}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("results_hankel_ladder.json"))
    args = parser.parse_args()
    mp.mp.dps = 80
    results = {
        "status": "passed",
        "verification_kind": "high-precision diagnostics, not interval certificates",
        "decimal_precision": mp.mp.dps,
        "python_version": platform.python_version(),
        "mpmath_version": mp.__version__,
        "repository_commit": REPOSITORY_COMMIT,
        "qualifications": [
            "The uncompensated Stieltjes derivative generating function is entire.",
            "The compensated moment generating function zeta(k+1-z,a) has a pole at z=k.",
            "For 0<a<1 these are Hamburger moments; odd moments need not be positive.",
            "The large-p theorem fixes a>0 and d>=1; its stated remainder uses p>=p0>1.",
            "The Hurwitz ladder is checked on Re(z)>0 with holomorphic loggamma there.",
            "No arithmetic independence or historical novelty is inferred.",
        ],
    }
    results["compensated_derivative_checks"] = transform_checks()
    print("Compensated Stieltjes derivative checks passed.", flush=True)
    results["finite_cauchy_binet_checks"] = cauchy_binet_checks()
    print("Strict determinant and finite Cauchy-Binet checks passed.", flush=True)
    results["first_three_tuple_checks"] = tuple_order_checks()
    results["large_p_asymptotic_checks"] = asymptotic_checks()
    print("Tuple ordering and explicit large-p remainder checks passed.", flush=True)
    results["hurwitz_ladder_checks"] = ladder_checks()
    print("Hurwitz ladder and tail-bound checks passed.", flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n")
    print(str(args.output))


if __name__ == "__main__":
    main()

