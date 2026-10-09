#!/usr/bin/env python3
"""Numerical validation of the uniform lattice/continuum transfer.

The integrand subtracts the two infrared singularities before quadrature.
At delta=0, ``difference`` means the common-energy-cutoff regularized
difference; neither density is separately finite there.  The omitted
large-energy tails have an explicit rigorous bound.  The numerical
quadrature error is assessed by comparing two orders, not certified.

Dependencies: Python 3.10+, NumPy, SciPy.  Run from any directory:
    python lattice_validate.py --output ../data/lattice_validation.json
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import gamma, zeta


A = float(gamma(0.25) ** 2 / (32 * math.pi ** 2.5))
RHO = float(gamma(0.75) / gamma(0.25))
B = float(math.sqrt(2) * zeta(1.5, 1) / (128 * math.pi ** 1.5))
C2 = float(A * zeta(2, 1) * (19 / 256 + RHO**2 / 64))


def interval_rule(order: int, upper: float) -> tuple[np.ndarray, np.ndarray]:
    nodes, weights = leggauss(order)
    return (nodes + 1) * upper / 2, weights * upper / 2


def geometry(order: int, cutoff: float) -> dict[str, np.ndarray | float]:
    """Smooth coordinates for Dirichlet(1/2, 1/4, 1/4) energy angles."""
    theta, wt = interval_rule(order, math.pi / 2)
    eta, we = interval_rule(order, math.pi / 2)
    # a=cos(theta)^2; b=sin(theta)^2 cos(phi)^2; c=sin(theta)^2 sin(phi)^2.
    # The further change phi=(pi/2) sin(eta)^2 removes the square-root
    # endpoint singularities of the phi probability density.
    phi = (math.pi / 2) * np.sin(eta) ** 2
    beta_quarter = gamma(0.25) ** 2 / gamma(0.5)
    phi_weight = (
        2
        * math.pi
        * np.sin(eta)
        * np.cos(eta)
        / (beta_quarter * np.sqrt(np.sin(phi) * np.cos(phi)))
    )
    angular_weights = np.outer(wt * (2 / math.pi), we * phi_weight)
    a = np.cos(theta)[:, None] ** 2 * np.ones((1, order))
    sqrt_b = np.sin(theta)[:, None] * np.cos(phi)[None, :]
    sqrt_c = np.sin(theta)[:, None] * np.sin(phi)[None, :]
    radial, radial_weights = interval_rule(order, math.sqrt(cutoff))
    return {
        "a": a,
        "sqrt_b": sqrt_b,
        "sqrt_c": sqrt_c,
        "angular_weights": angular_weights,
        "radial": radial,
        "radial_weights": radial_weights,
        "angular_mass": float(angular_weights.sum()),
    }


def subtracted_difference(
    temperature: float, crossover: float, order: int, cutoff: float = 36
) -> dict[str, float]:
    """Compute N_lattice-N_continuum without subtracting divergent integrals.

    crossover=delta/sqrt(T).  At crossover=0, the finite subtracted
    integral is the limit as delta decreases to zero.
    """
    if temperature <= 0 or crossover < 0 or cutoff <= 0:
        raise ValueError("Require T>0, s>=0, and cutoff>0.")
    if temperature * cutoff >= 4:
        raise ValueError("Energy cutoff must stay inside the transformed cube.")
    rule = geometry(order, cutoff)
    a = rule["a"]
    sqrt_b = rule["sqrt_b"]
    sqrt_c = rule["sqrt_c"]
    aw = rule["angular_weights"]
    integral = 0.0
    first_moment = 0.0
    for t, weight in zip(rule["radial"], rule["radial_weights"]):
        r = t * t
        # Physical squared coordinates are T*r*a, sqrt(T)*t*sqrt_b/c.
        log_jacobian = -0.5 * (
            np.log1p(-temperature * r * a / 4)
            + np.log1p(-math.sqrt(temperature) * t * sqrt_b / 4)
            + np.log1p(-math.sqrt(temperature) * t * sqrt_c / 4)
        )
        denominator = np.expm1(r + crossover * t * sqrt_c)
        # expm1 keeps the small-T Jacobian subtraction numerically stable.
        integral += float(weight * 2 * t * np.sum(aw * np.expm1(log_jacobian) / denominator))
        first_moment += float(
            weight * 2 * t * np.sum(aw * (t * (sqrt_b + sqrt_c) / 8) / denominator)
        )
    difference = A * temperature * integral
    c1 = A * first_moment
    tail = math.exp(-cutoff) / (1 - math.exp(-cutoff))
    tail += A * temperature * (-math.log1p(-math.exp(-cutoff)))
    return {
        "difference": difference,
        "difference_divided_by_T32": difference / temperature**1.5,
        "C1_at_s": c1,
        "tail_absolute_bound": tail,
        "angular_mass_error": abs(float(rule["angular_mass"]) - 1),
    }


def run(output: Path, coarse_order: int, fine_order: int) -> None:
    temperatures = [0.1, 0.05, 0.02, 0.01]
    crossovers = [0.0, 0.01, 0.1, 1.0, 10.0]
    rows = []
    for s in crossovers:
        for t in temperatures:
            coarse = subtracted_difference(t, s, coarse_order)
            fine = subtracted_difference(t, s, fine_order)
            row = {
                "T": t,
                "s_delta_over_sqrtT": s,
                "delta": s * math.sqrt(t),
                **fine,
                "quadrature_order_difference": abs(fine["difference"] - coarse["difference"]),
                "scaled_quadrature_order_difference": abs(
                    fine["difference_divided_by_T32"] - coarse["difference_divided_by_T32"]
                ),
                "residual_after_C1_divided_by_T2": (
                    fine["difference"] - fine["C1_at_s"] * t**1.5
                )
                / t**2,
            }
            if s == 0:
                row["residual_after_B_C2_divided_by_T52"] = (
                    fine["difference"] - B * t**1.5 - C2 * t**2
                ) / t**2.5
            rows.append(row)
            print(
                f"T={t:.3g} s={s:.3g} "
                f"difference/T^(3/2)={row['difference_divided_by_T32']:.12g} "
                f"coarse-fine={row['scaled_quadrature_order_difference']:.3g}",
                flush=True,
            )
    metadata = {
        "method": "Positive infrared subtraction (J-1), energy radial coordinates, tensor Gauss-Legendre quadrature",
        "coarse_order": coarse_order,
        "fine_order": fine_order,
        "energy_cutoff_E0_over_T": 36,
        "quadrature_error_status": "Order differences are diagnostics, not rigorous quadrature error bounds.",
        "tail_error_status": "The reported absolute tail bound is rigorous analytically, up to floating-point evaluation.",
        "delta_zero_status": "At s=0 only the common-energy-cutoff regularized difference is computed; separate densities diverge.",
        "constants": {"A": A, "B": B, "C2_at_zero": C2, "gamma_ratio": RHO},
        "rows": rows,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(metadata, indent=2) + "\n")
    print(f"Saved {output}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().parents[1] / "data" / "lattice_validation.json",
    )
    parser.add_argument("--coarse-order", type=int, default=56)
    parser.add_argument("--fine-order", type=int, default=88)
    args = parser.parse_args()
    run(args.output, args.coarse_order, args.fine_order)
