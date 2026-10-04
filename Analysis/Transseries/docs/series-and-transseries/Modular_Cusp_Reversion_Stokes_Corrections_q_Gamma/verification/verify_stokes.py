#!/usr/bin/env python3
"""Check a q-Pochhammer Stokes jump by independent ray quadratures.

Requires Python 3 and mpmath.  Run:
    python verify_stokes.py --dps 80

The Borel convention is B(t**n) = xi**(n-1)/(n-1)!.
At a = exp(-1), the paired j,-j summand is

    B_j(xi) = -(f(i*xi/(2*pi*j)) + f(-i*xi/(2*pi*j)))
              /(4*pi**2*j**2),
    f(w) = a*exp(w)/(1-a*exp(w)).

We compare direct quadratures along angles 0 and pi/4 with

    S_{pi/4,j} - S_{0,j}
      = (1/j) * sum_{n>=1} exp(-j*(4*pi**2*n + 2*pi*i)/t).

The infinite geometric sum is evaluated by its closed form.  No residue
formula is used to evaluate either ray integral.  The complex line
element dxi = exp(i*theta) ds is included explicitly.

These are arbitrary-precision numerical checks, not interval certificates.
The proof and the justification of the contour deformation are in the
article.  All numerical values are serialized as decimal strings.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp


def exp_ratio(log_z: mp.mpc) -> mp.mpc:
    """Return exp(log_z)/(1-exp(log_z)), avoiding enormous exponentials."""
    if mp.re(log_z) > 0:
        return -1 / (-mp.expm1(-log_z))
    return mp.exp(log_z) / (-mp.expm1(log_z))


def paired_borel(xi: mp.mpc, j: int) -> mp.mpc:
    w = mp.j * xi / (2 * mp.pi * j)
    return -(exp_ratio(w - 1) + exp_ratio(-w - 1)) / (
        4 * mp.pi**2 * j**2
    )


def ray_integral(j: int, t: mp.mpf, theta: mp.mpf):
    direction = mp.exp(mp.j * theta)

    def integrand(s):
        xi = direction * s
        return direction * mp.exp(-xi / t) * paired_borel(xi, j)

    # The intervals resolve the main contribution and the exponentially
    # small portions that matter in an 80-digit subtraction.  The final
    # interval is infinite: there is no finite-cutoff tail approximation.
    return mp.quad(
        integrand,
        [0, 4, 12, 30, 60, 120, 240, 480, mp.inf],
        error=True,
    )


def expected_jump(j: int, t: mp.mpf) -> mp.mpc:
    log_q = -4 * mp.pi**2 * j / t
    return mp.exp(log_q - 2 * mp.pi * mp.j * j / t) / (
        j * (-mp.expm1(log_q))
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=80)
    parser.add_argument(
        "--output", type=Path, default=Path(__file__).with_suffix(".json")
    )
    args = parser.parse_args()
    if args.dps < 50:
        parser.error("Use at least 50 decimal digits for the j=2, t=1 check.")
    mp.mp.dps = args.dps

    def real_string(x) -> str:
        return mp.nstr(x, args.dps)

    def complex_record(z):
        return {"real": real_string(mp.re(z)), "imag": real_string(mp.im(z))}

    results = []
    for j in (1, 2):
        for t_integer in (1, 2):
            t = mp.mpf(t_integer)
            ray_0, error_0 = ray_integral(j, t, mp.mpf(0))
            ray_45, error_45 = ray_integral(j, t, mp.pi / 4)
            measured = ray_45 - ray_0
            predicted = expected_jump(j, t)
            residual = abs(measured - predicted)
            relative = residual / abs(predicted)
            # This threshold tests the tiny jump itself, not merely the
            # much larger individual integrals.  At 80 digits the smallest
            # expected jump is about 2.56e-35, leaving ample guard digits.
            relative_tolerance = mp.power(10, -(args.dps - 50))
            passed = bool(relative < relative_tolerance)
            results.append(
                {
                    "j": j,
                    "t": t_integer,
                    "ray_0_integral": complex_record(ray_0),
                    "ray_pi_over_4_integral": complex_record(ray_45),
                    "measured_jump": complex_record(measured),
                    "predicted_jump": complex_record(predicted),
                    "absolute_residual": real_string(residual),
                    "relative_residual": real_string(relative),
                    "quadrature_error_estimate_ray_0": real_string(error_0),
                    "quadrature_error_estimate_ray_pi_over_4": real_string(
                        error_45
                    ),
                    "relative_tolerance": real_string(relative_tolerance),
                    "passed": passed,
                }
            )
            print(
                f"j={j}, t={t_integer}: "
                f"jump={mp.nstr(predicted, 18)}, "
                f"absolute residual={mp.nstr(residual, 6)}, "
                f"relative residual={mp.nstr(relative, 6)}, "
                f"passed={passed}",
                flush=True,
            )

    record = {
        "description": "Direct paired-summand q-Pochhammer Stokes checks",
        "mpmath_version": mp.__version__,
        "decimal_working_precision": args.dps,
        "a": "exp(-1)",
        "directions": ["0", "pi/4"],
        "difference_orientation": "ray_pi_over_4 minus ray_0",
        "quadrature_method": "mpmath.quad, piecewise tanh-sinh, infinite tail",
        "certification": "Numerical evidence; not an interval certificate",
        "all_passed": all(item["passed"] for item in results),
        "results": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    if not record["all_passed"]:
        raise SystemExit("At least one Stokes comparison failed its tolerance.")


if __name__ == "__main__":
    main()
