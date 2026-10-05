#!/usr/bin/env python3
"""Independent numerical diagnostic for the first Catalan edge correction.

This script evaluates a finite, central Fourier integral in ordinary floating
point.  It does NOT compute exact integer coefficients, does NOT use interval
arithmetic, and does NOT certify its quadrature or truncation errors.

For M in {20,40,80,160}, fix theta=0.37 and put m=M+theta,

    r(x) = x log(4) - log(pi)/2 + log Gamma(x+1/2) - log Gamma(x+2),
    t = exp(-r(m)),       v_k = t c_k = exp(r(k)-r(m)).

The full Fourier integrand is centered at the continuous mean E_t S=B1/t,
where B1=sum(v_k/(exp(v_k)-1)).  No integer n is chosen, and t is therefore
not asserted to be the exact saddle for an integer coefficient in this
diagnostic.  If E_t S is rounded to the nearest integer, its scaled change
is at most t/2.  The corresponding saddle coordinate changes by O(t/m),
using B2~m and r'(m)~log(4); neither observation certifies the separate
Fourier and part-cutoff truncations made here.

For K=M+h, the ratio of the prefix and full central integrals, multiplied
by the probability that every tail occupancy vanishes, is compared with

    G_h(theta) * (1 + C_h(theta)/m),

where C_h=-A+(V-A*A)/2-(3/2)*sum((j-theta)*u_j*mu_j), j>h.
Bounded m^2*(diagnostic/G_h - 1 - C_h/m) supports the first correction,
but is only a numerical check of the separately proved theorem.

Dependencies: Python 3, numpy, scipy.  Run from any working directory:

    python code/audit_correction.py

The default JSON destination is ../data/correction_fourier_audit.json,
resolved relative to this file.  An optional output path can be supplied.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import platform

import numpy as np
import scipy
from scipy.integrate import quad
from scipy.special import gammaln


ALPHA = float(np.log(4.0))
THETA = 0.37
M_VALUES = (20, 40, 80, 160)
H_VALUES = (-2, 0, 1)
INTEGRATION_ENDPOINT = 20.0
EPSABS = 2e-13
EPSREL = 2e-13
EXTRA_PARTS = 11


def r(x: np.ndarray | float) -> np.ndarray | float:
    """Exact gamma interpolation satisfying r(k)=log(c_k)."""
    return (
        ALPHA * x
        - 0.5 * np.log(np.pi)
        + gammaln(x + 0.5)
        - gammaln(x + 2.0)
    )


def geometric_mean(v: np.ndarray) -> np.ndarray:
    """Stable 1/expm1(v), avoiding overflow when v is very large."""
    return np.exp(-v) / (-np.expm1(-v))


def central_integral(
    rates: np.ndarray, scaled_target: float
) -> tuple[float, float]:
    """Integrate the real half of the central characteristic integral.

    The integration variable is x=phi/t, with phi the original coefficient
    angle.  Full coefficient integration would reach pi/t.  Both finite
    cutoff and quadrature errors remain uncertified in this diagnostic.
    The omitted common factor t/pi cancels in the ratio.
    """
    log_normalizers = np.log(-np.expm1(-rates))

    def integrand(x: float) -> float:
        log_characteristic = np.sum(
            log_normalizers
            - np.log(-np.expm1(-rates + 1j * rates * x))
        )
        centered = log_characteristic - 1j * x * scaled_target
        return float(np.exp(centered).real)

    value, error_estimate = quad(
        integrand,
        0.0,
        INTEGRATION_ENDPOINT,
        epsabs=EPSABS,
        epsrel=EPSREL,
        limit=300,
    )
    return float(value), float(error_estimate)


def ideal_constants(h: int) -> dict[str, float]:
    # The final u is already enormous; omitted factors round to 1.  This
    # summation cutoff is another numerical cutoff, not a certified bound.
    j = np.arange(h + 1, h + 22, dtype=float)
    d = j - THETA
    u = np.power(4.0, d)
    mu = geometric_mean(u)
    q = np.exp(-u)
    normalizer = -np.expm1(-u)
    A = float(np.sum(u * mu))
    V = float(np.sum(u * u * q / (normalizer * normalizer)))
    curvature_sum = float(1.5 * np.sum(d * u * mu))
    G = float(np.exp(np.sum(np.log(normalizer))))
    C = -A + 0.5 * (V - A * A) - curvature_sum
    return {
        "A": A,
        "V": V,
        "curvature_sum": curvature_sum,
        "G": G,
        "C": C,
    }


def run_audit() -> dict:
    constants = {h: ideal_constants(h) for h in H_VALUES}
    rows = []
    for M in M_VALUES:
        m = M + THETA
        log_t = -float(r(m))
        t = float(np.exp(log_t))
        k = np.arange(1, M + EXTRA_PARTS + 1, dtype=float)
        rates = np.exp(r(k) - r(m))
        B1 = float(np.sum(rates * geometric_mean(rates)))
        full_integral, full_quad_error = central_integral(rates, B1)

        for h in H_VALUES:
            K = M + h
            prefix_integral, prefix_quad_error = central_integral(
                rates[:K], B1
            )
            zero_tail_probability = float(
                np.exp(np.sum(np.log(-np.expm1(-rates[K:]))))
            )
            diagnostic = (
                zero_tail_probability * prefix_integral / full_integral
            )
            G = constants[h]["G"]
            C = constants[h]["C"]
            rows.append(
                {
                    "M": M,
                    "m": m,
                    "theta": THETA,
                    "h": h,
                    "K": K,
                    "log_t": log_t,
                    "t": t,
                    "scaled_continuous_mean_B1": B1,
                    "scaled_nearest_integer_displacement_bound": t / 2.0,
                    "last_retained_part_index": int(k[-1]),
                    "last_retained_scaled_rate": float(rates[-1]),
                    "full_central_integral": full_integral,
                    "prefix_central_integral": prefix_integral,
                    "full_quad_reported_error_estimate": full_quad_error,
                    "prefix_quad_reported_error_estimate": prefix_quad_error,
                    "zero_tail_probability": zero_tail_probability,
                    "central_integral_ratio_diagnostic": diagnostic,
                    "first_order_prediction": G * (1.0 + C / m),
                    "m_times_relative_difference_from_G": m
                    * (diagnostic / G - 1.0),
                    "m_squared_scaled_first_order_residual": m
                    * m
                    * (diagnostic / G - 1.0 - C / m),
                }
            )

    return {
        "kind": "uncertified central-Fourier numerical diagnostic",
        "normalization": (
            "m=M+theta; t=exp(-r(m)); v_k=t*c_k; continuous target "
            "E_t S=B1/t; no integer coefficient is evaluated"
        ),
        "interpretation": (
            "The quadrature and infinite-product truncations are numerical "
            "and uncertified. Bounded scaled residuals support the analytic "
            "first-order correction; they do not replace its proof. The "
            "reported quad errors are heuristic quadrature estimates."
        ),
        "nearest_integer_note": (
            "Rounding E_t S changes the scaled target by at most t/2. "
            "The exact saddle m for the resulting integer changes by "
            "O(t/m), from B2~m and r'(m)~log(4). This does not certify "
            "the truncated Fourier calculation as an integer coefficient."
        ),
        "versions": {
            "python": platform.python_version(),
            "numpy": np.__version__,
            "scipy": scipy.__version__,
        },
        "settings": {
            "theta": THETA,
            "M_values": list(M_VALUES),
            "h_values": list(H_VALUES),
            "scaled_integration_interval": [0.0, INTEGRATION_ENDPOINT],
            "epsabs": EPSABS,
            "epsrel": EPSREL,
            "extra_parts_after_M": EXTRA_PARTS,
        },
        "ideal_constants": {str(h): constants[h] for h in H_VALUES},
        "rows": rows,
    }


def main() -> None:
    default_output = (
        Path(__file__).resolve().parents[1]
        / "data"
        / "correction_fourier_audit.json"
    )
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", nargs="?", type=Path, default=default_output)
    args = parser.parse_args()
    result = run_audit()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")

    print("Uncertified central-Fourier diagnostic at a continuous mean.")
    print("No exact integer coefficient is computed.")
    print(" h       m       m*(diagnostic/G-1)    m^2*first-order residual")
    for row in result["rows"]:
        print(
            f"{row['h']:2d}  {row['m']:7.2f}"
            f"  {row['m_times_relative_difference_from_G']:23.12g}"
            f"  {row['m_squared_scaled_first_order_residual']:26.12g}"
        )
    print(f"Saved {args.output}")


if __name__ == "__main__":
    main()
