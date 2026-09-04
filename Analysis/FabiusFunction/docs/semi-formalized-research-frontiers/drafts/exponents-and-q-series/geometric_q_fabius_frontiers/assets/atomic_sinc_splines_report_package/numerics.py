#!/usr/bin/env python3
"""Deterministic numerical experiments for the atomic sinc-product spline report.

The script studies the compactly supported densities

    h_a = law of X_a,   X_a = sum_{j>=1} a^{-j} U_j,

where U_j are independent uniform random variables on [-1,1].  With the
Fourier convention

    f_hat(xi) = integral f(x) exp(-2*pi*i*x*xi) dx,

the characteristic/Fourier transform is

    Phi_a(xi) = product_{j>=1} sinc(2*pi*a^{-j}*xi).

All experiments are deterministic.  Exact symbolic checks use SymPy rational
arithmetic; density plots and finite-product convergence use FFT inversion of
the explicit Fourier products.  No Monte Carlo simulation is used.

Outputs
-------
figures/family_profiles.png
figures/scaled_prefix_error_a22.png
figures/fourier_envelope_a22.png
figures/cantor_gap_atlas_a3.png
data/moments.csv
data/prouhet_checks.csv
data/prefix_errors.csv

Run from the package directory with

    python numerics.py

The FFT experiments are corroborative numerical checks.  The theorems in the
report are proved analytically and do not depend on floating-point output.
"""

from __future__ import annotations

import argparse
import csv
import itertools
import math
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import numpy as np
import sympy as sp


ROOT = Path(__file__).resolve().parent
FIG_DIR = ROOT / "figures"
DATA_DIR = ROOT / "data"


def sinc_product(freq: np.ndarray, a: float, factors: int) -> np.ndarray:
    """Return the first ``factors`` terms of Phi_a on a frequency grid.

    NumPy's sinc is normalized as sinc_N(x)=sin(pi*x)/(pi*x).  Therefore
    sinc(2*pi*a^{-j}*xi) in the report is np.sinc(2*a^{-j}*xi).
    """

    phi = np.ones_like(freq, dtype=np.float64)
    scale = 1.0 / a
    for _ in range(factors):
        phi *= np.sinc(2.0 * scale * freq)
        scale /= a
    return phi


def fft_density(
    a: float,
    *,
    factors: int,
    n_grid: int = 2**17,
    domain_factor: float = 4.0,
    derivative_order: int = 0,
) -> tuple[np.ndarray, np.ndarray]:
    """Invert a finite sinc product by FFT on a zero-padded periodic box.

    The true support is [-b,b], b=1/(a-1).  The box length is
    ``domain_factor * (2*b)``; since this is strictly larger than the support
    diameter, periodic copies do not overlap.  For derivative_order r, the
    Fourier multiplier (2*pi*i*xi)^r is applied before inversion.
    """

    if a <= 1.0:
        raise ValueError("a must be greater than 1")
    if factors < 1:
        raise ValueError("factors must be positive")
    if n_grid <= 0 or n_grid & (n_grid - 1):
        raise ValueError("n_grid must be a positive power of two")

    b = 1.0 / (a - 1.0)
    length = domain_factor * (2.0 * b)
    dx = length / n_grid
    freq = np.fft.fftfreq(n_grid, d=dx)
    phi = sinc_product(freq, a, factors)
    if derivative_order:
        phi = phi.astype(np.complex128) * (
            2.0j * np.pi * freq
        ) ** derivative_order
    values = np.fft.fftshift(np.fft.ifft(phi)).real / dx
    x = (np.arange(n_grid) - n_grid // 2) * dx
    return x, values


def exact_even_cumulant(a: sp.Rational, m: int) -> sp.Rational:
    """Return kappa_{2m}(X_a) exactly for rational a."""

    if m < 1:
        raise ValueError("m must be positive")
    return sp.factor(
        sp.Rational(2 ** (2 * m), 2 * m)
        * sp.bernoulli(2 * m)
        / (a ** (2 * m) - 1)
    )


def exact_even_moments(a: sp.Rational, max_order: int) -> dict[int, sp.Rational]:
    """Compute exact even moments from the standard cumulant recurrence."""

    if max_order % 2:
        raise ValueError("max_order must be even")
    moments: dict[int, sp.Rational] = {0: sp.Rational(1)}
    for n in range(1, max_order // 2 + 1):
        total = sp.Rational(0)
        for j in range(1, n + 1):
            total += (
                sp.binomial(2 * n - 1, 2 * j - 1)
                * exact_even_cumulant(a, j)
                * moments[2 * n - 2 * j]
            )
        moments[2 * n] = sp.factor(total)
    return moments


def write_moment_table() -> None:
    """Write exact moments for representative rational parameters."""

    parameters = [
        ("2", sp.Rational(2)),
        ("11/5", sp.Rational(11, 5)),
        ("3", sp.Rational(3)),
    ]
    rows: list[dict[str, str]] = []
    for label, a in parameters:
        moments = exact_even_moments(a, 12)
        for order in range(0, 13, 2):
            value = sp.factor(moments[order])
            rows.append(
                {
                    "a": label,
                    "order": str(order),
                    "numerator": str(sp.numer(value)),
                    "denominator": str(sp.denom(value)),
                    "decimal_30_digits": str(sp.N(value, 30)),
                }
            )

    path = DATA_DIR / "moments.csv"
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def signed_power_sum(a: int, n: int, power: int) -> int:
    """Compute the weighted Prouhet sum over signs exactly as an integer."""

    total = 0
    for eta in itertools.product((-1, 1), repeat=n):
        location = sum(eta[j] * (a**j) for j in range(n))
        weight = math.prod(eta)
        total += weight * (location**power)
    return total


def write_prouhet_checks() -> None:
    """Verify vanishing signed moments and the first nonzero moment."""

    rows: list[dict[str, str]] = []
    for a in (2, 3):
        for n in range(1, 9):
            expected = 2**n * math.factorial(n) * a ** (n * (n - 1) // 2)
            for power in range(n + 1):
                actual = signed_power_sum(a, n, power)
                target = expected if power == n else 0
                rows.append(
                    {
                        "a": str(a),
                        "n": str(n),
                        "power": str(power),
                        "actual": str(actual),
                        "expected": str(target),
                        "verified": str(actual == target),
                    }
                )

    path = DATA_DIR / "prouhet_checks.csv"
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def plot_family_profiles() -> None:
    """Plot h_a for the critical and separated-spline regimes."""

    plt.figure(figsize=(8.0, 4.8))
    for a, label in ((2.0, "a=2"), (2.2, "a=2.2"), (3.0, "a=3")):
        x, density = fft_density(a, factors=42, n_grid=2**17)
        support = 1.0 / (a - 1.0)
        mask = np.abs(x) <= 1.04 * support
        plt.plot(x[mask], density[mask], label=label)
    plt.xlabel("x")
    plt.ylabel(r"$h_a(x)$")
    plt.title("Atomic sinc-product densities")
    plt.legend()
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    plt.savefig(FIG_DIR / "family_profiles.png", dpi=220)
    plt.close()


def prefix_error_data(a: float, reference_factors: int = 46) -> list[dict[str, str]]:
    """Return convergence diagnostics for ordinary finite sinc products."""

    n_grid = 2**18
    b = 1.0 / (a - 1.0)
    length = 4.0 * (2.0 * b)
    dx = length / n_grid
    freq = np.fft.fftfreq(n_grid, d=dx)
    phi_ref = sinc_product(freq, a, reference_factors)
    h_ref = np.fft.fftshift(np.fft.ifft(phi_ref)).real / dx
    h2_ref = np.fft.fftshift(
        np.fft.ifft(phi_ref * (2.0j * np.pi * freq) ** 2)
    ).real / dx
    x = (np.arange(n_grid) - n_grid // 2) * dx
    mask = np.abs(x) <= b + 4.0 * dx

    coefficient = 1.0 / (6.0 * (a * a - 1.0))
    h2_sup = float(np.max(np.abs(h2_ref[mask])))
    predicted_norm_limit = coefficient * h2_sup

    rows: list[dict[str, str]] = []
    for factors in (4, 6, 8, 10, 12, 14, 16):
        phi_n = sinc_product(freq, a, factors)
        h_n = np.fft.fftshift(np.fft.ifft(phi_n)).real / dx
        difference = h_n - h_ref
        sup_error = float(np.max(np.abs(difference[mask])))
        scaled_profile = (a ** (2 * factors)) * difference
        residual = scaled_profile + coefficient * h2_ref
        residual_sup = float(np.max(np.abs(residual[mask])))
        rows.append(
            {
                "a": f"{a:.16g}",
                "N": str(factors),
                "sup_error": f"{sup_error:.16e}",
                "a^(2N)*sup_error": f"{(a ** (2 * factors) * sup_error):.16e}",
                "predicted_norm_limit": f"{predicted_norm_limit:.16e}",
                "scaled_profile_residual_sup": f"{residual_sup:.16e}",
                "reference_h2_sup": f"{h2_sup:.16e}",
            }
        )
    return rows


def write_prefix_error_table() -> None:
    """Write finite-product convergence tables for several parameters."""

    rows: list[dict[str, str]] = []
    for a in (2.0, 2.2, 3.0):
        rows.extend(prefix_error_data(a))
    path = DATA_DIR / "prefix_errors.csv"
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def plot_scaled_prefix_error_a22() -> None:
    """Plot the profile-level first-order asymptotic for a=2.2."""

    a = 2.2
    n_grid = 2**18
    b = 1.0 / (a - 1.0)
    length = 4.0 * (2.0 * b)
    dx = length / n_grid
    freq = np.fft.fftfreq(n_grid, d=dx)
    phi_ref = sinc_product(freq, a, 46)
    h_ref = np.fft.fftshift(np.fft.ifft(phi_ref)).real / dx
    h2_ref = np.fft.fftshift(
        np.fft.ifft(phi_ref * (2.0j * np.pi * freq) ** 2)
    ).real / dx
    x = (np.arange(n_grid) - n_grid // 2) * dx
    coefficient = 1.0 / (6.0 * (a * a - 1.0))

    plt.figure(figsize=(8.0, 4.8))
    for factors in (6, 8, 10):
        phi_n = sinc_product(freq, a, factors)
        h_n = np.fft.fftshift(np.fft.ifft(phi_n)).real / dx
        scaled = (a ** (2 * factors)) * (h_n - h_ref)
        mask = np.abs(x) <= b
        plt.plot(x[mask], scaled[mask], label=f"N={factors}")
    mask = np.abs(x) <= b
    plt.plot(x[mask], -coefficient * h2_ref[mask], label="predicted limit")
    plt.xlabel("x")
    plt.ylabel(r"$a^{2N}(h_{a,N}-h_a)$")
    plt.title("First correction for ordinary finite sinc products (a=2.2)")
    plt.legend()
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    plt.savefig(FIG_DIR / "scaled_prefix_error_a22.png", dpi=220)
    plt.close()


def plot_fourier_envelope_a22() -> None:
    """Compare the product with the elementary log-Gaussian envelope."""

    a = 2.2
    xi = np.geomspace(1.0, 2.0e5, 7000)
    phi = np.ones_like(xi)
    scale = 1.0 / a
    for _ in range(55):
        phi *= np.sinc(2.0 * scale * xi)
        scale /= a
    modulus = np.maximum(np.abs(phi), 1.0e-300)

    t = 2.0 * np.pi * xi
    n = np.floor(np.log(t) / np.log(a)).astype(int)
    n = np.maximum(n, 0)
    log_bound = 0.5 * n * (n + 1) * np.log(a) - n * np.log(t)
    bound = np.minimum(1.0, np.exp(np.maximum(log_bound, -700.0)))

    plt.figure(figsize=(8.0, 4.8))
    plt.loglog(xi, modulus, label=r"$|\widehat h_a(\xi)|$")
    plt.loglog(xi, bound, label="selected-factor envelope")
    plt.xlabel(r"$|\xi|$")
    plt.ylabel("magnitude")
    plt.title("Fourier product and log-Gaussian envelope (a=2.2)")
    plt.legend()
    plt.grid(True, which="both", alpha=0.25)
    plt.tight_layout()
    plt.savefig(FIG_DIR / "fourier_envelope_a22.png", dpi=220)
    plt.close()


def gap_intervals(a: float, depth: int) -> list[tuple[float, float]]:
    """Return all depth-``depth`` images of the central gap for a>2."""

    if a <= 2.0:
        raise ValueError("the separated-gap construction requires a>2")
    b = 1.0 / (a - 1.0)
    b1 = (a - 2.0) / (a * (a - 1.0))
    intervals = [(-b1, b1)]
    for _ in range(depth):
        next_intervals: list[tuple[float, float]] = []
        for left, right in intervals:
            next_intervals.append(((left - 1.0) / a, (right - 1.0) / a))
            next_intervals.append(((left + 1.0) / a, (right + 1.0) / a))
        intervals = next_intervals
    return sorted(intervals)


def plot_cantor_gap_atlas_a3() -> None:
    """Visualize the disjoint polynomial gaps in the a=3 support."""

    a = 3.0
    b = 1.0 / (a - 1.0)
    plt.figure(figsize=(8.0, 4.8))
    for depth in range(7):
        for left, right in gap_intervals(a, depth):
            plt.plot([left, right], [depth, depth], linewidth=5.0)
    plt.xlim(-1.04 * b, 1.04 * b)
    plt.ylim(-0.6, 6.6)
    plt.xlabel("x")
    plt.ylabel("gap depth")
    plt.title("Polynomial-gap atlas for the a=3 atomic spline")
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    plt.savefig(FIG_DIR / "cantor_gap_atlas_a3.png", dpi=220)
    plt.close()


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--quick",
        action="store_true",
        help=(
            "Skip the three expensive prefix-error tables.  Exact tables and "
            "all figures are still produced."
        ),
    )
    args = parser.parse_args(argv)

    FIG_DIR.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)

    write_moment_table()
    write_prouhet_checks()
    plot_family_profiles()
    plot_scaled_prefix_error_a22()
    plot_fourier_envelope_a22()
    plot_cantor_gap_atlas_a3()
    if not args.quick:
        write_prefix_error_table()

    print(f"Wrote figures to {FIG_DIR}")
    print(f"Wrote tables to {DATA_DIR}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
