#!/usr/bin/env python3
"""Independent numerical cross-check of the exact rational certificates.

The certificates themselves come from proved inequalities and Fraction
arithmetic. This script checks their implementation against mpmath zeta
values and the independent finite log-sine formula for F(n).
Floating-point containment checks are corroboration, not interval proofs.
"""

import argparse
import json
import sys
from pathlib import Path

import mpmath as mp
from certified_intervals import zeta_interval


def numeric_fraction(record):
    return mp.mpf(record["numerator"]) / mp.mpf(record["denominator"])


def finite_F_integer(n):
    # F(1) follows by summing psi(k)/k using harmonic numbers and the
    # defining limit for the first Stieltjes constant. Reciprocity and
    # the reciprocal-integer evaluation then give this finite formula.
    f_one = -mp.stieltjes(1) - mp.euler**2 / 2 - mp.pi**2 / 12
    log_sine_sum = mp.fsum(
        mp.log(2 * mp.sin(mp.pi * k / n))**2 for k in range(1, n)
    )
    return (f_one - mp.pi**2 * (n - 1) * (n - 2) / (24 * n)
            + mp.log(n)**2 / 2 + log_sine_sum / 2)


def main():
    sys.set_int_max_str_digits(0)
    package = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--digits", type=int, default=400)
    parser.add_argument("--input", type=Path,
                        default=package / "data" / "rational_intervals.json")
    parser.add_argument("--output", type=Path,
                        default=package / "data" / "interval_cross_checks.json")
    args = parser.parse_args()
    if args.digits < 150:
        parser.error("Use at least 150 digits for these cross-checks.")
    mp.mp.dps = args.digits
    certificates = json.loads(args.input.read_text())
    bound = max(case["terms"] for case in certificates["cases"])
    exponents = [2] + list(range(3, 2 * bound + 8, 2))
    zeta_checks = []
    for s in exponents:
        interval = zeta_interval(s, certificates["zeta_cutoff"],
                                 certificates["zeta_EM_order"])
        lo = mp.mpf(interval.lo.numerator) / interval.lo.denominator
        hi = mp.mpf(interval.hi.numerator) / interval.hi.denominator
        value = mp.zeta(s)
        assert lo <= value <= hi, f"Numerical zeta containment failed at s={s}"
        zeta_checks.append({"s": s, "contained": True})
    records = []
    for case in certificates["cases"]:
        n = int(case["x"])
        record = case["F_interval"]
        lo, hi = numeric_fraction(record["lower"]), numeric_fraction(record["upper"])
        value = finite_F_integer(n)
        assert lo < value < hi, f"Numerical F containment failed at x={n}"
        records.append({
            "x": n, "contained": True, "F_from_finite_formula": mp.nstr(value, 90),
            "fraction_of_interval_from_lower": mp.nstr((value - lo) / (hi - lo), 30),
        })
    payload = {
        "status": "independent high-precision numerical cross-check",
        "not_a_proof_of_containment": True,
        "precision_digits": args.digits,
        "zeta_checks": zeta_checks,
        "F_checks": records,
        "all_checks_passed": True,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"Passed {len(zeta_checks)} zeta and {len(records)} finite-F cross-checks.")


if __name__ == "__main__":
    main()
