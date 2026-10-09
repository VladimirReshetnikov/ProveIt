#!/usr/bin/env python3
"""Independent saddle-integral check for the largest component of path forests.

The labelled path-forest assembly has p[1] = 1 and p[k] = 1/2 for k >= 2,
and hence C(z) = z/(2(1-z)) + z/2.  This script evaluates the exact
coefficient ratio

    Pr(M_n <= m) = [z^n] exp(C(z) - z^(m+1)/(2(1-z)))
                   / [z^n] exp(C(z))

by centered Fourier inversion at the exact positive saddle.  It does not
evaluate the asymptotic CDF in place of the coefficient ratio.  Gauss-
Legendre quadrature is repeated at two node counts, and an explicit absolute
bound for the omitted Fourier arc is reported.  These numerical checks do
not constitute a computer-assisted proof of the asymptotic theorem.

Both ends of every sampled CDF step are compared to the continuous curves;
at the right end the CDF means its left limit.  This is essential for the
Kolmogorov comparison of a lattice distribution to a continuous curve.

Dependencies: Python >= 3.10, NumPy, SciPy.  Example (from project root):

    python code/forest_numerics.py --output data/forest_errors.csv

All thresholds are examined when their count is at most --grid-points.
For larger n, a uniform mesh in the normalized coordinate and additional
points near the limiting extrema are used.  Consequently, the reported
errors are sampled maxima, not certified global maximizers.
"""

from __future__ import annotations

import argparse
import csv
from decimal import Decimal, localcontext
import math
from pathlib import Path

import numpy as np
from scipy.optimize import brentq
from scipy.special import roots_legendre


C = 0.5
D = 0.5
Z_EXTREMUM = (3.0 + math.sqrt(5.0)) / 2.0
KAPPA = Z_EXTREMUM * (Z_EXTREMUM - 1.0) * math.exp(-Z_EXTREMUM)
LATTICE_CONSTANT = 1.0 / (2.0 * math.e)


def saddle(n: int) -> tuple[float, float, float, float, float]:
    """Return tau, r, 1-r, B1 and B2 without cancellation near r=1."""
    scale = math.sqrt(C / n)

    def relative_mean(t: float) -> float:
        tau = scale * t
        q = -math.expm1(-tau)
        r = math.exp(-tau)
        return (C * r / q**2 + D * r) / n - 1.0

    t = brentq(relative_mean, 0.1, 4.0, xtol=1e-15, rtol=1e-15)
    tau = scale * t
    q = -math.expm1(-tau)
    r = math.exp(-tau)
    b1 = C * r / q**2 + D * r
    b2 = C * r * (1.0 + r) / q**3 + D * r
    return tau, r, q, b1, b2


def gumbel(x: np.ndarray) -> np.ndarray:
    return np.exp(-np.exp(-x))


def calibrated_coordinate(x: np.ndarray, tau: float, ell: float) -> np.ndarray:
    """The full smooth conditioning correction h_n(x)."""
    s = ell + x
    beta = np.exp(-x)
    return x + tau / (4.0 * C) * (s**2 - s - 1.0 - beta * (s + 1.0) ** 2)


def expm1_minus_linear(theta: np.ndarray) -> np.ndarray:
    """Compute exp(i theta)-1-i theta accurately for small real theta."""
    real = -2.0 * np.sin(theta / 2.0) ** 2
    t2 = theta**2
    imag_small = theta**3 * (
        -1.0 / 6.0
        + t2 * (1.0 / 120.0 + t2 * (-1.0 / 5040.0 + t2 / 362880.0))
    )
    imag = np.where(np.abs(theta) < 0.1, imag_small, np.sin(theta) - theta)
    return real + 1j * imag


def fourier_cdfs(
    n: int,
    thresholds: np.ndarray,
    nodes: int,
    cutoff: float,
    batch: int = 256,
) -> tuple[np.ndarray, float]:
    """Return exact-integral approximations and an omitted-arc error bound.

    With sigma^2=B2, quadrature uses u=sigma*theta and |u|<=cutoff.
    The Fourier damping outside this interval is bounded monotonically
    using the closed form of C.  The numerator bound allows its full tail
    mass H0, so it is valid for every supplied threshold, although crude.
    """
    tau, r, q, b1, b2 = saddle(n)
    sigma = math.sqrt(b2)
    half_width = min(cutoff, math.pi * sigma)
    abscissae, weights = roots_legendre(nodes)
    u = half_width * abscissae
    weights = half_width * weights
    theta = u / sigma
    v = np.expm1(1j * theta)
    denominator = q - r * v

    # Algebraically equal to C(r exp(i theta))-C(r)-i*n*theta.
    # Direct evaluation would subtract imaginary terms of size n*theta.
    centered = (
        b1 * expm1_minus_linear(theta)
        + 1j * (b1 - n) * theta
        + C * r**2 * v**2 / (q**2 * denominator)
    )
    base = np.exp(centered)
    integral0 = float(np.dot(weights, base.real))
    if integral0 <= 0.0:
        raise ArithmeticError("Nonpositive saddle integral; increase quadrature nodes.")

    cdfs = np.empty(len(thresholds), dtype=float)
    for start in range(0, len(thresholds), batch):
        m_plus_one = thresholds[start : start + batch, None] + 1
        tail = C * np.exp(m_plus_one * (-tau + 1j * theta)) / denominator
        integrand = base * np.exp(-tail)
        cdfs[start : start + batch] = integrand.real @ weights / integral0

    if half_width == math.pi * sigma:
        return cdfs, 0.0

    theta0 = half_width / sigma
    one_minus_cos = 2.0 * math.sin(theta0 / 2.0) ** 2
    damping = (
        C * r * (1.0 + r) * one_minus_cos
        / (q * (q**2 + 2.0 * r * one_minus_cos))
        + D * r * one_minus_cos
    )
    max_h0 = C * math.exp(-tau * (int(thresholds.min()) + 1)) / q
    # Absolute omitted integrals in the u variable.  Their ratio error is
    # at most (R_num + |computed ratio| R_den)/(integral0 - R_den).
    log_length = math.log(2.0 * (math.pi * sigma - half_width))
    tail0 = math.exp(log_length - damping)
    tailm = math.exp(log_length - damping + max_h0)
    if tail0 >= integral0:
        error_bound = math.inf
    else:
        error_bound = max(
            (tailm + np.max(np.abs(cdfs)) * tail0) / (integral0 - tail0),
            np.finfo(float).tiny,
        )
        # Flooring extremely small reported bounds avoids displaying zero
        # after floating-point underflow.  This floor is conservative.
    return cdfs, float(error_bound)


def threshold_grid(tau: float, ell: float, points: int, low: float, high: float) -> np.ndarray:
    first = max(1, int(math.ceil((ell + low) / tau)))
    last = max(first, int(math.floor((ell + high) / tau)))
    if last - first + 1 <= points:
        return np.arange(first, last + 1, dtype=np.int64)
    normalized = np.linspace(low, high, points)
    # Fine local meshes make the sampled error maxima reproducible well
    # beyond the precision needed to distinguish the two asymptotic rates.
    for peak in (-math.log(Z_EXTREMUM), 0.0):
        normalized = np.concatenate((normalized, peak + np.linspace(-0.04, 0.04, 801)))
    thresholds = np.rint((ell + normalized) / tau).astype(np.int64)
    return np.unique(np.clip(thresholds, first, last))


def error_summary(cdf: np.ndarray, x: np.ndarray, tau: float, ell: float) -> dict[str, float]:
    raw_left = cdf - gumbel(x)
    raw_right = cdf - gumbel(x + tau)
    corrected_left = cdf - gumbel(calibrated_coordinate(x, tau, ell))
    corrected_right = cdf - gumbel(calibrated_coordinate(x + tau, tau, ell))

    def maximum(left: np.ndarray, right: np.ndarray) -> tuple[float, float, int]:
        both = np.column_stack((np.abs(left), np.abs(right)))
        index, side = np.unravel_index(int(np.argmax(both)), both.shape)
        return float(both[index, side]), float(x[index] + side * tau), int(side)

    raw, raw_x, raw_side = maximum(raw_left, raw_right)
    corrected, corrected_x, corrected_side = maximum(corrected_left, corrected_right)
    delta = tau * ell**2 / (4.0 * C)
    return {
        "raw_max_error": raw,
        "raw_over_delta_kappa": raw / (delta * KAPPA),
        "raw_max_x": raw_x,
        "raw_max_right_limit": raw_side,
        "corrected_max_error": corrected,
        "corrected_over_tau": corrected / tau,
        "corrected_over_lattice_optimum": corrected / (tau * LATTICE_CONSTANT),
        "corrected_max_x": corrected_x,
        "corrected_max_right_limit": corrected_side,
    }


def recurrence_check() -> float:
    """Check Fourier inversion against a distinct, 60-digit coefficient method.

    Multiplying F_m'=C_m' F_m by (1-z)^2 gives a sparse recurrence for the
    coefficients of F_m.  This check uses neither a saddle approximation nor
    quadrature, and is inexpensive at the fixed test size n=10000.
    """
    n = 10000
    tau, _, _, _, _ = saddle(n)
    ell = math.log(C / tau)
    thresholds = np.rint((ell + np.array([-1.0, 0.0, 1.0])) / tau).astype(np.int64)

    def coefficient(m: int | None) -> Decimal:
        with localcontext() as context:
            context.prec = 60
            half = Decimal(1) / 2
            coefficients = [Decimal(1)]
            for j in range(n):
                value = (2 * j + 1) * coefficients[j]
                if j >= 1:
                    value -= j * coefficients[j - 1]
                if j >= 2:
                    value += half * coefficients[j - 2]
                if m is not None and j >= m:
                    value -= half * (m + 1) * coefficients[j - m]
                if m is not None and j >= m + 1:
                    value += half * m * coefficients[j - m - 1]
                coefficients.append(value / (j + 1))
            return coefficients[n]

    full = coefficient(None)
    reference = np.array([float(coefficient(int(m)) / full) for m in thresholds])
    quadrature, _ = fourier_cdfs(n, thresholds, 1024, 40.0)
    difference = float(np.max(np.abs(reference - quadrature)))
    print(f"60-digit sparse coefficient check at n={n}: max absolute difference={difference:.3e}", flush=True)
    if difference > 2e-12:
        raise ArithmeticError("The independent coefficient recurrence check failed.")
    return difference


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--n", nargs="+", type=int, default=[10**k for k in range(4, 13)])
    parser.add_argument("--coarse-nodes", type=int, default=512)
    parser.add_argument("--fine-nodes", type=int, default=1024)
    parser.add_argument("--cutoff", type=float, default=40.0)
    parser.add_argument("--grid-points", type=int, default=6001)
    parser.add_argument("--x-min", type=float, default=-3.0)
    parser.add_argument("--x-max", type=float, default=8.0)
    parser.add_argument("--recurrence-check", action="store_true", help="also compare three CDF values to a 60-digit sparse coefficient recurrence")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "data" / "forest_errors.csv")
    args = parser.parse_args()
    if args.recurrence_check:
        recurrence_check()
    rows = []
    print(f"kappa = {KAPPA:.15g}; lattice constant = {LATTICE_CONSTANT:.15g}", flush=True)
    for n in args.n:
        if n < 10000:
            raise ValueError("This default Fourier cutoff is designed for n >= 10000.")
        tau, _, _, b1, _ = saddle(n)
        ell = math.log(C / tau)
        thresholds = threshold_grid(tau, ell, args.grid_points, args.x_min, args.x_max)
        coarse, arc_coarse = fourier_cdfs(n, thresholds, args.coarse_nodes, args.cutoff)
        fine, arc_fine = fourier_cdfs(n, thresholds, args.fine_nodes, args.cutoff)
        quadrature_difference = float(np.max(np.abs(fine - coarse)))
        x = tau * thresholds - ell
        row = {
            "n": n,
            "tau": tau,
            "L": ell,
            "thresholds_sampled": len(thresholds),
            "coarse_nodes": args.coarse_nodes,
            "fine_nodes": args.fine_nodes,
            "scaled_fourier_cutoff": args.cutoff,
            "relative_saddle_residual": abs(b1 / n - 1.0),
            "max_quadrature_difference": quadrature_difference,
            "omitted_arc_error_bound": max(arc_coarse, arc_fine),
            **error_summary(fine, x, tau, ell),
        }
        rows.append(row)
        print(
            f"n={n:>13d}  raw/(delta*kappa)={row['raw_over_delta_kappa']:.9f}  "
            f"corrected/(tau/(2e))={row['corrected_over_lattice_optimum']:.9f}  "
            f"quadrature diff={quadrature_difference:.2e}  arc<={row['omitted_arc_error_bound']:.2e}",
            flush=True,
        )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(f"Wrote {args.output}", flush=True)


if __name__ == "__main__":
    main()
