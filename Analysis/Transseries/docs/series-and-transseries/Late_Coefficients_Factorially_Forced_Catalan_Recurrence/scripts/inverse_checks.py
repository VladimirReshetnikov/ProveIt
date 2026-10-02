#!/usr/bin/env python3
"""Verify selected Gamma/Lambert smooth inverses using optional mpmath.

Requires Python >= 3.11 and mpmath==1.3.0 (see ../requirements.txt)::

    python3 -m pip install -r requirements.txt
    python3 scripts/inverse_checks.py

For exact y=c_k at k=100,300,600,1000 (by default), compute the Lambert seed
x0=Y/W(Y/(e*rho)), Y=log(y), rho=log(2), its first explicit shift, and Newton
solutions of log Gamma(x)-x log(rho)+log Q_J(1/(x-1))=Y for J=0,1,3,6.
Also check the original a_n model Gamma(x+1)*P_J(1/x), where P_J has the
exact coefficients c_0,...,c_J, for J=0,3,6 at the same indices.
The derivative uses digamma and an explicit derivative of Q_J; no numerical
differentiation is needed. A second calculation at 20 extra decimal digits
checks all displayed numerical values.

This specifies a smooth Gamma model, not a canonical interpolation of c_k.
The small errors are numerical observations, not certified constants for
integer-threshold bracketing. The script performs no network access.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

try:
    import mpmath as mp
except ImportError as exc:
    raise SystemExit("Optional dependency missing: install requirements.txt to run inverse_checks.py") from exc

from verify import (DEFAULT_RESULTS, convolve, corrections_stirling,
                    exact_sequences, require, write_csv, write_json)
from render_tables import render_tables


def checks_at_precision(c: list[int], q: list[list[int]], points: list[int],
                        precision: int, orders: list[int],
                        original: bool = False) -> list[dict[str, object]]:
    """Solve every model at fixed precision and return decimal-string records."""
    rows = []
    with mp.workdps(precision):
        rho = mp.log(2)
        log_rho = mp.mpf(0) if original else mp.log(rho)
        qvalues = [sum(mp.mpf(v) * rho ** i for i, v in enumerate(poly)) for poly in q]
        tolerance = mp.power(10, -(precision - 15))

        def number(value: mp.mpf) -> str:
            return mp.nstr(value, 40, strip_zeros=False, min_fixed=-6, max_fixed=6)

        def model_and_derivative(x: mp.mpf, order: int) -> tuple[mp.mpf, mp.mpf]:
            denominator = x if original else x - 1
            gamma_argument = x + 1 if original else x
            qvalue = 1 + sum(qvalues[j] / denominator ** j for j in range(1, order + 1))
            qderiv = -sum(j * qvalues[j] / denominator ** (j + 1)
                         for j in range(1, order + 1))
            value = mp.loggamma(gamma_argument) - x * log_rho + mp.log(qvalue)
            derivative = mp.digamma(gamma_argument) - log_rho + qderiv / qvalue
            return value, derivative

        for k in points:
            ylog = mp.log(c[k])
            w = mp.lambertw(ylog / (mp.e * (1 if original else rho)))
            seed = ylog / w
            if original:
                shifted = seed - (mp.log(seed) + mp.log(2 * mp.pi)) / (2 * (1 + w))
            else:
                shifted = seed + (mp.log(seed) - mp.log(2 * mp.pi)) / (2 * (1 + w))
            row: dict[str, object] = {"k": k, "log_y": number(ylog),
                                      "lambert_seed_error": number(seed - k),
                                      "first_shift_error": number(shifted - k), "orders": {}}
            for order in orders:
                x = seed
                for _ in range(25):
                    value, derivative = model_and_derivative(x, order)
                    require(derivative > 0, "Newton iterate is outside the increasing model branch")
                    step = (value - ylog) / derivative
                    x -= step
                    if abs(step) < tolerance:
                        break
                else:
                    raise ArithmeticError(f"Newton iteration did not converge for k={k}, J={order}")
                residual = model_and_derivative(x, order)[0] - ylog
                require(abs(residual) < tolerance * max(1, abs(ylog)),
                        f"Newton residual too large at k={k}, J={order}")
                row["orders"][str(order)] = {
                    "inverse_error": number(x - k),
                    "log_model_error_at_k": number(model_and_derivative(mp.mpf(k), order)[0] - ylog)}
            rows.append(row)
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--points", type=int, nargs="+", default=[100, 300, 600, 1000])
    parser.add_argument("--precision", type=int, default=80,
                        help="mpmath working decimal precision, at least 70 (default: 80)")
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_RESULTS)
    args = parser.parse_args()
    if sys.version_info < (3, 11):
        parser.error("Python 3.11 or newer is required")
    if min(args.points) < 20 or args.precision < 70:
        parser.error("All inverse-check indices must be >=20 and precision must be >=70")
    if mp.__version__ != "1.3.0":
        parser.error("Use the pinned reproducibility dependency mpmath==1.3.0")
    sys.set_int_max_str_digits(0)
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    points = sorted(set(args.points))
    a, d, c = exact_sequences(max(points))
    h = [2 * v for v in convolve(convolve(d, d, 6), d, 6)]
    q = corrections_stirling(h, 6)
    orders = [0, 1, 3, 6]
    rows = checks_at_precision(c, q, points, args.precision, orders)
    require(rows == checks_at_precision(c, q, points, args.precision + 20, orders),
            "Displayed inverse values changed under a precision increase")
    result = {"mpmath_version": mp.__version__, "working_decimal_precision": args.precision,
              "higher_precision_recheck": args.precision + 20, "displayed_significant_digits": 40,
              "all_precision_checks_passed": True,
              "definition": "F_J(x)=Gamma(x)*rho^(-x)*Q_J(1/(x-1)); y=c_k; rho=log(2)",
              "scope": "Numerical smooth-model errors; not certified integer-threshold bounds.",
              "checks": rows}
    write_json(output / "inverse_checks.json", result)
    csv_rows = []
    for row in rows:
        for order in orders:
            values = row["orders"][str(order)]
            csv_rows.append({"k": row["k"], "J": order,
                             "lambert_seed_error": row["lambert_seed_error"],
                             "first_shift_error": row["first_shift_error"],
                             "inverse_error": values["inverse_error"],
                             "log_model_error_at_k": values["log_model_error_at_k"]})
    write_csv(output / "inverse_checks.csv", csv_rows)
    original_orders = [0, 3, 6]
    original_q = [[coefficient] for coefficient in c[:7]]
    original_rows = checks_at_precision(a, original_q, points, args.precision,
                                        original_orders, original=True)
    require(original_rows == checks_at_precision(a, original_q, points, args.precision + 20,
                                                 original_orders, original=True),
            "Displayed original-sequence inverse values changed under a precision increase")
    original_rows = [{"n": row["k"], "log_y": row["log_y"],
                      "lambert_seed_error": row["lambert_seed_error"],
                      "first_shift_error": row["first_shift_error"],
                      "orders": {str(order): {
                          "inverse_error": row["orders"][str(order)]["inverse_error"],
                          "log_model_error_at_n": row["orders"][str(order)]["log_model_error_at_k"]}
                          for order in original_orders}}
                     for row in original_rows]
    original_result = {
        "mpmath_version": mp.__version__, "working_decimal_precision": args.precision,
        "higher_precision_recheck": args.precision + 20, "displayed_significant_digits": 40,
        "all_precision_checks_passed": True,
        "definition": "B_J(x)=Gamma(x+1)*P_J(1/x); P_J(t)=sum_{j=0}^J c_j*t^j; y=a_n",
        "scope": "Numerical smooth-model errors; not certified integer-threshold bounds.",
        "checks": original_rows}
    write_json(output / "original_inverse_checks.json", original_result)
    original_csv_rows = []
    for row in original_rows:
        for order in original_orders:
            values = row["orders"][str(order)]
            original_csv_rows.append({"n": row["n"], "J": order,
                                      "lambert_seed_error": row["lambert_seed_error"],
                                      "first_shift_error": row["first_shift_error"],
                                      "inverse_error": values["inverse_error"],
                                      "log_model_error_at_n": values["log_model_error_at_n"]})
    write_csv(output / "original_inverse_checks.csv", original_csv_rows)
    render_tables(output)
    for row in rows:
        print(f"k={row['k']}: seed-k={row['lambert_seed_error']}; "
              f"x_6-k={row['orders']['6']['inverse_error']}")
    for row in original_rows:
        print(f"original n={row['n']}: seed-n={row['lambert_seed_error']}; "
              f"b_6-n={row['orders']['6']['inverse_error']}")
    print("All displayed values agree at the higher precision.")


if __name__ == "__main__":
    main()
