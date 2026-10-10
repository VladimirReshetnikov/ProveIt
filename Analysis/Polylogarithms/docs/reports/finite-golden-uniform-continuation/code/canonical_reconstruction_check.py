#!/usr/bin/env python3
"""Replay a proposed notation repair in ProveIt's golden ladder section.

The Fraction calculations certify equivalence of rational coefficient
vectors. The mpmath and defining-series checks are numerical diagnostics,
not proofs of the evaluated polylogarithm identities. No PSLQ is used.

Run from the bundle root:
    python code/canonical_reconstruction_check.py
"""

import argparse
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
from math import factorial
from pathlib import Path

import mpmath as mp


# RHS coordinates are zeta(5), ell**5, pi**2*ell**3, pi**4*ell,
# with ell = log(rho) = -log(phi). These are the source's three rows.
SOURCE = [
    ({2: F(4455), 4: F(-1215), 6: F(-360), 12: F(15)},
     [F(3015), F(702), F(-180), F(38)]),
    ({2: F(45000), 4: F(-16875), 10: F(-144), 20: F(9)},
     [F(28944), F(6000), F(-1600), F(356)]),
    ({2: F(15660), 4: F(-19440), 6: F(7680), 8: F(2430), 24: F(-15)},
     [F(5025), F(-2088), F(240), F(28)]),
]

# Coefficients multiply Li_n(rho**a)/a**(n-1).
CANONICAL = {
    12: ({12: F(1), 6: F(-3, 2), 4: F(-1), 2: F(11, 48)},
         [F(-13, 48), F(1, 48), F(-19, 1728)], F(67, 6912)),
    20: ({20: F(1), 10: F(-1), 4: F(-3), 2: F(1, 2)},
         [F(-1, 2), F(1, 25), F(-89, 4000)], F(201, 10000)),
    24: ({24: F(1), 12: F(-4, 3), 8: F(-2), 4: F(7, 3),
          2: F(-205, 576)},
         [F(179, 576), F(-5, 192), F(629, 41472)], F(-1541, 110592)),
}

TRANSFORMS = {
    12: ([F(1), F(0), F(0)], F(15 * 12**4)),
    20: ([F(0), F(1), F(0)], F(9 * 20**4)),
    24: ([F(64, 3), F(0), F(1)], F(-15 * 24**4)),
}


def exact_checks():
    rows = []
    for index, (weights, divisor) in TRANSFORMS.items():
        lhs = {}
        rhs = [F(0)] * 4
        for weight, (source_lhs, source_rhs) in zip(weights, SOURCE):
            for a, c in source_lhs.items():
                lhs[a] = lhs.get(a, F(0)) + weight * c
            rhs = [u + weight * v for u, v in zip(rhs, source_rhs)]
        normalized = {a: c * a**4 / divisor for a, c in lhs.items() if c}
        tails = [-rhs[1] * factorial(5) / divisor,
                 -rhs[2] * 6 * factorial(3) / divisor,
                 -rhs[3] * 90 / divisor]
        expected_lhs, expected_tails, expected_zeta = CANONICAL[index]
        assert normalized == expected_lhs
        assert tails == expected_tails
        assert rhs[0] / divisor == expected_zeta
        rows.append({
            "canonical_index": index,
            "source_row_multipliers_before_division": list(map(str, weights)),
            "divisor": str(divisor),
            "rhs_before_division": list(map(str, rhs)),
            "normalized_Li_coefficients": {str(a): str(c)
                                            for a, c in sorted(normalized.items())},
            "tail_triple": list(map(str, tails)),
            "zeta5_coefficient": str(expected_zeta),
        })
    z12, z20, z24 = [CANONICAL[j][2] for j in (12, 20, 24)]
    assert z20 - F(1296, 625) * z12 == 0
    assert z24 + F(23, 16) * z12 == 0
    return rows


def numerical_checks(dps, terms):
    mp.mp.dps = dps
    rho = (mp.sqrt(5) - 1) / 2
    ell = mp.log(rho)

    def m(value):
        value = F(value)
        return mp.mpf(value.numerator) / value.denominator

    def show(value):
        return mp.nstr(value, 20)

    @lru_cache(None)
    def series(n, a):
        z = rho**a
        return mp.fsum(z**k / mp.mpf(k)**n for k in range(1, terms + 1))

    @lru_cache(None)
    def builtin(n, a):
        return mp.polylog(n, rho**a)

    def ladder(index, n, method):
        coeff, tails, _ = CANONICAL[index]
        value = mp.fsum(m(c) * method(n, a) / a**(n - 1)
                        for a, c in coeff.items())
        for j, coefficient in enumerate(tails):
            power = n - 2 * j
            if power < 0:
                continue  # Omit the negative-factorial summand.
            factor = mp.mpf(1) if j == 0 else mp.zeta(2 * j)
            value += m(coefficient) * factor * ell**power / factorial(power)
        return value

    max_backend_difference = mp.mpf(0)
    for a in (2, 4, 6, 8, 10, 12, 20, 24):
        for n in range(1, 10):
            max_backend_difference = max(max_backend_difference,
                                         abs(series(n, a) - builtin(n, a)))

    low_rows = []
    max_low_residual = mp.mpf(0)
    for index in CANONICAL:
        for n in range(1, 6):
            target = m(CANONICAL[index][2]) * mp.zeta(5) if n == 5 else mp.mpf(0)
            residuals = [ladder(index, n, method) - target
                         for method in (builtin, series)]
            max_low_residual = max(max_low_residual, *map(abs, residuals))
            low_rows.append({"index": index, "order": n,
                             "builtin_residual": show(residuals[0]),
                             "defining_series_residual": show(residuals[1])})

    source_rows = []
    max_source_residual = mp.mpf(0)
    for row_number, (coeff, rhs) in enumerate(SOURCE, 1):
        rhs_terms = [mp.zeta(5), ell**5, mp.pi**2 * ell**3, mp.pi**4 * ell]
        right = mp.fsum(m(c) * value for c, value in zip(rhs, rhs_terms))
        residuals = [mp.fsum(m(c) * method(5, a) for a, c in coeff.items()) - right
                     for method in (builtin, series)]
        max_source_residual = max(max_source_residual, *map(abs, residuals))
        source_rows.append({"displayed_source_row": row_number,
                            "builtin_residual": show(residuals[0]),
                            "defining_series_residual": show(residuals[1])})

    def combination(n, method):
        l12, l20, l24 = [ladder(j, n, method) for j in (12, 20, 24)]
        m20 = l20 - m(F(1296, 625)) * l12
        m24 = l24 + m(F(23, 16)) * l12
        return m24 + m(F(409375, 373248)) * m20

    t9_target = (m(F(66452911, 41278242816000)) * mp.zeta(9)
                 + m(F(3537283, 2063912140800)) * mp.zeta(8) * ell
                 - m(F(11527, 2866544640)) * mp.zeta(6) * ell**3 / factorial(3))
    t9_residuals = [combination(9, method) - t9_target
                    for method in (builtin, series)]

    # A rigorous exact bound on truncation ALONE. Rounding is not enclosed.
    # Since 0 < rho**a <= rho**2 < 2/5, for n>=1 the tail is at most
    # (2/5)**(N+1)/((N+1)*(1-2/5)).
    tail = F(2, 5)**(terms + 1) / (F(terms + 1) * F(3, 5))
    tolerance = mp.power(10, -dps + 12)
    assert max_backend_difference < tolerance
    assert max_low_residual < tolerance
    assert max_source_residual < tolerance
    assert max(map(abs, t9_residuals)) < tolerance
    return {
        "working_decimal_digits": dps,
        "defining_series_terms": terms,
        "diagnostic_absolute_tolerance": show(tolerance),
        "mpmath_version": mp.__version__,
        "two_evaluation_methods": ["mpmath.polylog", "finite defining power series with mpmath.fsum"],
        "finite_series_truncation_bound_only": {
            "exact_fraction": str(tail),
            "decimal": show(m(tail)),
            "bound_expression": "(2/5)^(N+1)/((N+1)*(1-2/5))",
            "floating_point_rounding_enclosed": False,
        },
        "maximum_individual_polylog_evaluation_difference": show(max_backend_difference),
        "maximum_canonical_orders_1_to_5_residual": show(max_low_residual),
        "maximum_original_weight5_formula_residual": show(max_source_residual),
        "canonical_orders_1_to_5": low_rows,
        "original_weight5_formulas": source_rows,
        "source_T9_formula_replayed": {
            "builtin_residual": show(t9_residuals[0]),
            "defining_series_residual": show(t9_residuals[1]),
        },
        "all_numerical_diagnostics_passed": True,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=160)
    parser.add_argument("--terms", type=int, default=600)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] /
                        "data/canonical_reconstruction_check.json")
    args = parser.parse_args()
    if args.dps < 40 or args.terms < 100:
        parser.error("Use at least 40 decimal digits and 100 terms.")
    report = {
        "pinned_commit": "28357e8ca63dd78327db91d9be239d75e4462879",
        "source": "Analysis/Polylogarithms/docs/manuscript/chapters/03-algebraic.tex",
        "source_sha256": "270ffd30430d1b3737026263040725c00953c3efe733ccb45b1f053dd2dc07aa",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "status": "Proposed notation reconstruction; exact coefficient equivalence and numerical replay, not an analytic proof of the evaluations.",
        "exact_rational_transformations": exact_checks(),
        "exact_rational_checks_passed": True,
        "numerical_replay": numerical_checks(args.dps, args.terms),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"output": str(args.output),
                      "exact_rational_checks_passed": True,
                      "maximum_canonical_residual": report["numerical_replay"]["maximum_canonical_orders_1_to_5_residual"],
                      "maximum_source_residual": report["numerical_replay"]["maximum_original_weight5_formula_residual"],
                      "T9_residual": report["numerical_replay"]["source_T9_formula_replayed"]}, indent=2))


if __name__ == "__main__":
    main()
