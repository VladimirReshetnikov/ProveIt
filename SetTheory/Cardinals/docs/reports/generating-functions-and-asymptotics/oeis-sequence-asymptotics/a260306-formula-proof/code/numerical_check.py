#!/usr/bin/env python3
"""High-precision illustrations of the proved asymptotic expansion.

Requires mpmath. This is a numerical consistency check, not an interval
certificate or a replacement for the error bound in the article.
"""
from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

try:
    import mpmath as mp
except ImportError as exc:
    raise SystemExit("Install the optional dependency with: pip install mpmath") from exc

from verify import coefficients_recurrence


def theta_gamma(N: int) -> mp.mpf:
    """Real continuation via the regularized lower incomplete gamma function."""
    x = mp.mpf(N)
    scale = mp.exp(x + mp.loggamma(x + 1) - x * mp.log(x))
    return scale * (mp.gammainc(x, 0, x, regularized=True) - mp.mpf("0.5"))


def theta_definition(N: int) -> mp.mpf:
    """Original finite-sum definition, scaled by exp(-N)."""
    x = mp.mpf(N)
    term = mp.exp(-x)
    total = mp.mpf(0)
    for k in range(N):
        total += term
        term *= x / (k + 1)
    # term is now exp(-N)*N**N/N!.
    return (mp.mpf("0.5") - total) / term


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=100)
    parser.add_argument(
        "--out-dir", type=Path, default=Path(__file__).resolve().parents[1] / "artifacts"
    )
    args = parser.parse_args()
    if args.dps < 50:
        parser.error("Use at least 50 decimal digits for this test.")
    args.out_dir.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = args.dps
    coefficients = coefficients_recurrence(6)
    c = [mp.mpf(x.numerator) / x.denominator for x in coefficients]
    rows = []
    max_discrepancy = mp.mpf(0)
    for N in [5, 10, 20, 50, 100, 200, 500, 1000]:
        theta = theta_gamma(N)
        difference = abs(theta - theta_definition(N))
        max_discrepancy = max(max_discrepancy, difference)
        if difference > mp.power(10, -(args.dps - 20)):
            raise AssertionError(f"The two theta evaluations disagree at N={N}.")
        for R in [1, 2, 3, 4, 6]:
            partial = mp.fsum(c[n] / mp.mpf(N)**n for n in range(R))
            error = theta - partial
            scaled = mp.mpf(N)**R * error
            rows.append([
                N, R, mp.nstr(theta, 45), mp.nstr(partial, 45),
                mp.nstr(error, 35), mp.nstr(scaled, 35),
                mp.nstr(c[R], 35), mp.nstr(scaled / c[R], 35),
            ])
    with (args.out_dir / "numerical_checks.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["N", "R", "theta", "partial_sum", "error",
                         "N_to_R_times_error", "c_R", "scaled_error_over_c_R"])
        writer.writerows(rows)
    report = {
        "status": "PASS", "mpmath_version": mp.__version__,
        "decimal_working_precision": args.dps,
        "N_values": [5, 10, 20, 50, 100, 200, 500, 1000],
        "truncation_orders": [1, 2, 3, 4, 6],
        "max_absolute_discrepancy_between_theta_evaluations": mp.nstr(max_discrepancy, 12),
        "scope": "High-precision consistency check, not certified interval arithmetic.",
    }
    (args.out_dir / "numerical_summary.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(report, indent=2))
    print("\nN, N^4*(theta(N)-sum_{n=0}^3 c_n/N^n), ratio to c_4")
    for row in rows:
        if row[1] == 4:
            print(row[0], row[5], row[7])


if __name__ == "__main__":
    main()
