#!/usr/bin/env python3
"""High-precision regression checks for the polylogarithm corrections.

These are numerical diagnostics, not proofs or interval certificates.  In
particular, no finite partial-sum test is used to assess convergence: the
convergence counterexamples in the article are justified analytically.

Requires mpmath.  Run from the package root:
    python code/verify_polylog_corrections.py
"""

import argparse
import json
from pathlib import Path

import mpmath as mp


def modified_polylog(order, z, include_extra_term=False):
    """Standard P_m, or the erroneous formula with a j=m Li_0 term."""
    upper = order if include_extra_term else order - 1
    logarithm = mp.log(abs(z))
    total = mp.fsum(
        mp.mpf(2) ** j * mp.bernoulli(j) / mp.factorial(j)
        * logarithm ** j * mp.polylog(order - j, z)
        for j in range(upper + 1)
    )
    return mp.re(total) if order % 2 else mp.im(total)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=80)
    parser.add_argument("--output", type=Path,
                        default=Path("data/polylog_correction_checks.json"))
    args = parser.parse_args()
    if args.dps < 50:
        parser.error("Use at least 50 decimal digits for these diagnostics.")
    mp.mp.dps = args.dps
    tolerance = mp.mpf(10) ** (-args.dps + 10)
    digits = args.dps - 5
    worst = mp.mpf(0)
    records = []

    def real_string(value):
        return mp.nstr(value, digits)

    def complex_data(value):
        return {"real": real_string(mp.re(value)),
                "imaginary": real_string(mp.im(value))}

    def check_residual(actual, expected):
        nonlocal worst
        residual = abs(actual - expected)
        assert residual < tolerance, (actual, expected, residual)
        worst = max(worst, residual)
        return real_string(residual)

    assert mp.bernoulli(1) == -mp.mpf(1) / 2
    z = mp.j / 2
    corrected = modified_polylog(2, z)
    printed = modified_polylog(2, z, include_extra_term=True)
    expected_excess = 2 * mp.log(2) ** 2 / 15
    records.append({
        "check": "modified_P2_extra_term",
        "z": complex_data(z),
        "corrected_P2": real_string(corrected),
        "printed_P2": real_string(printed),
        "printed_minus_corrected": real_string(printed - corrected),
        "exact_expected_excess": "2*log(2)^2/15",
        "expected_excess_value": real_string(expected_excess),
        "absolute_residual": check_residual(printed - corrected, expected_excess),
    })

    roots = mp.polyroots([1, 0, 1, -1], maxsteps=200, extraprec=30)
    lower_roots = [root for root in roots if mp.im(root) < 0]
    assert len(lower_roots) == 1
    z = lower_roots[0]
    root_residual = check_residual(z ** 3 + z - 1, 0)
    corrected = modified_polylog(4, z)
    printed = modified_polylog(4, z, include_extra_term=True)
    expected_excess = (
        mp.mpf(2) ** 4 * mp.bernoulli(4) / mp.factorial(4)
        * mp.log(abs(z)) ** 4 * mp.im(z / (1 - z))
    )
    # Check the quoted decimal prefixes separately from the exact excess
    # identity.  Prefix checks cannot certify additional digits.
    assert abs(corrected - mp.mpf("-0.916010467826680838722383200166")) < mp.mpf("1e-30")
    assert abs(printed - mp.mpf("-0.915999527027516872882916723105")) < mp.mpf("1e-30")
    records.append({
        "check": "modified_P4_at_lower_complex_embedding",
        "defining_polynomial": "z^3+z-1",
        "root": complex_data(z),
        "root_absolute_residual": root_residual,
        "corrected_sum_endpoint": "j=0,...,m-1",
        "printed_sum_endpoint": "j=0,...,m",
        "corrected_P4": real_string(corrected),
        "printed_P4": real_string(printed),
        "printed_minus_corrected": real_string(printed - corrected),
        "extra_Li0_term": real_string(expected_excess),
        "absolute_residual": check_residual(printed - corrected, expected_excess),
        "quoted_decimal_prefixes_agree": True,
    })

    zeta6 = mp.zeta(6)
    beta6 = mp.dirichlet(6, [0, 1, 0, -1])
    level_four = [
        ("Li6_at_minus_one", -mp.mpf(1), -mp.mpf(31) * zeta6 / 32,
         "-31*zeta(6)/32"),
        ("Li6_at_i", mp.j, -mp.mpf(31) * zeta6 / 2048 + mp.j * beta6,
         "-31*zeta(6)/2048+i*beta(6)"),
        ("Li6_at_minus_i", -mp.j, -mp.mpf(31) * zeta6 / 2048 - mp.j * beta6,
         "-31*zeta(6)/2048-i*beta(6)"),
    ]
    for name, z, expected, formula in level_four:
        actual = mp.polylog(6, z)
        records.append({
            "check": name,
            "z": complex_data(z),
            "polylog_value": complex_data(actual),
            "expected_formula": formula,
            "expected_value": complex_data(expected),
            "absolute_residual": check_residual(actual, expected),
        })

    z = mp.exp(2 * mp.pi * mp.j / 3)
    value = mp.polylog(3, z)
    sine_value = 2 * mp.pi ** 3 / 81
    clausen3 = -4 * mp.zeta(3) / 9
    records.append({
        "check": "Eisenstein_weight_three_sine_component",
        "argument": "exp(2*pi*i/3)",
        "imaginary_polylog_value": real_string(mp.im(value)),
        "expected_formula": "2*pi^3/81",
        "expected_value": real_string(sine_value),
        "absolute_residual": check_residual(mp.im(value), sine_value),
    })
    records.append({
        "check": "Eisenstein_weight_three_Clausen_parity",
        "argument": "2*pi/3",
        "standard_convention": "Cl_3(theta)=Re Li_3(exp(i*theta))",
        "clausen_value": real_string(mp.re(value)),
        "expected_formula": "-4*zeta(3)/9",
        "expected_value": real_string(clausen3),
        "absolute_residual": check_residual(mp.re(value), clausen3),
        "difference_from_sine_component": real_string(mp.re(value) - mp.im(value)),
    })
    assert abs(mp.re(value) - mp.im(value)) > 1

    payload = {
        "description": "Numerical regression diagnostics for polylogarithm corrections; not proofs.",
        "mpmath_version": mp.__version__,
        "decimal_precision": args.dps,
        "absolute_residual_threshold": real_string(tolerance),
        "bernoulli_convention": "B_1=-1/2",
        "polylogarithm_branch": "mpmath principal branch",
        "case_count": len(records),
        "all_assertions_passed": True,
        "worst_absolute_residual": real_string(worst),
        "convergence_checks": "None: convergence counterexamples use analytic comparisons, not finite sums.",
        "cases": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in payload.items() if key != "cases"}, indent=2))


if __name__ == "__main__":
    main()
