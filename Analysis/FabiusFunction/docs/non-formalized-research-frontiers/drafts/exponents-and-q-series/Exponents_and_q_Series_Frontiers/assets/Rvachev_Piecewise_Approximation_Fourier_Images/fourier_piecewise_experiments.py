#!/usr/bin/env python3
"""Numerical and symbolic experiments for finite Rvachev-up splines.

The repeated-integration approximant f_n has Fourier transform

    F_n(xi) = [prod_{k=1}^n sinc(xi / 2^k)] sinc(xi / 2^n),

where sinc(z) = sin(z)/z.  The limiting Rvachev up-function has Fourier
transform

    Phi(xi) = prod_{k=1}^infinity sinc(xi / 2^k).

This program validates the exact transfer identity

    F_n(xi) = Phi(xi) A(xi / 2^n),  A(z) = sinc(z)/Phi(z),

computes exact Taylor coefficients of A from the Bernoulli-number logarithm,
checks the pole-dominated coefficient asymptotic, estimates Fourier L^p error
constants, and tests several accelerated tail replacements.

The script is deliberately self-contained and uses only NumPy, SciPy, SymPy,
mpmath, and Matplotlib.  It writes figures, CSV tables, and a JSON summary to
an output directory.  The integrations are split at the common zero lattice
2*pi*Z; this is slower than an FFT-based estimate but considerably easier to
audit numerically.

Usage:
    python fourier_piecewise_experiments.py --output-dir figures_and_data

The default calculations use ordinary double precision except for very small
high-order surrogate errors, where mpmath is used at 100 decimal digits.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Callable, Iterable

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
import sympy as sp
from scipy.integrate import quad
from scipy.optimize import minimize_scalar
from scipy.special import spherical_jn
from numpy.polynomial.legendre import leggauss

PI = math.pi


def sinc_np(x: np.ndarray | float) -> np.ndarray:
    """Unnormalized sinc sin(x)/x, vectorized through numpy.sinc."""
    return np.sinc(np.asarray(x, dtype=float) / PI)


def phi_np(x: np.ndarray | float, factors: int = 70) -> np.ndarray:
    """Finite-precision evaluation of Phi by a safely overlong product.

    For real x in the ranges used below, 70 factors make the uncomputed tail
    much smaller than IEEE double precision.  At exact zeros, floating-point
    argument reduction may leave tiny residuals; plots and integrals do not
    rely on those residual values.
    """
    arr = np.asarray(x, dtype=float)
    value = np.ones_like(arr)
    for k in range(1, factors + 1):
        value *= np.sinc(arr / (PI * (2.0**k)))
    return value


def head_spectrum_np(x: np.ndarray | float, n: int) -> np.ndarray:
    """Fourier transform of the n-box head convolution."""
    arr = np.asarray(x, dtype=float)
    value = np.ones_like(arr)
    for k in range(1, n + 1):
        value *= np.sinc(arr / (PI * (2.0**k)))
    return value


def finite_spectrum_np(x: np.ndarray | float, n: int) -> np.ndarray:
    """Fourier transform F_n of the repeated-integration spline."""
    arr = np.asarray(x, dtype=float)
    return head_spectrum_np(arr, n) * np.sinc(arr / (PI * (2.0**n)))


def transfer_np(z: np.ndarray | float) -> np.ndarray:
    """Meromorphic transfer function A(z)=sinc(z)/Phi(z).

    This direct quotient is used only away from zeros of Phi.  The exact
    report treats removable points and poles analytically.
    """
    arr = np.asarray(z, dtype=float)
    return sinc_np(arr) / phi_np(arr)


def transfer_coefficients(max_order: int) -> tuple[list[sp.Rational], list[sp.Rational]]:
    """Return exact coefficients ell_r and a_r.

    With w=z^2,

        log A(z) = sum_{r>=1} ell_r w^r,
        A(z)     = sum_{r>=0} a_r w^r.

    The logarithmic coefficients are the Bernoulli formula already implicit
    in the finite-stage tail comparison.  Exponentiation is performed by the
    exact recurrence

        r a_r = sum_{k=1}^r k ell_k a_{r-k}.
    """
    ell: list[sp.Rational] = [sp.Rational(0)]
    for r in range(1, max_order + 1):
        bernoulli_abs = abs(sp.bernoulli(2 * r))
        coefficient = (
            -sp.Rational(2) ** (2 * r - 1)
            * bernoulli_abs
            / (r * sp.factorial(2 * r))
            * sp.Rational(4**r - 2, 4**r - 1)
        )
        ell.append(sp.factor(coefficient))

    a: list[sp.Rational] = [sp.Rational(1)]
    for r in range(1, max_order + 1):
        coefficient = sum(k * ell[k] * a[r - k] for k in range(1, r + 1)) / r
        a.append(sp.factor(coefficient))
    return ell, a


def phi_mp(x: mp.mpf, digits: int = 100) -> mp.mpf:
    """High-precision Phi evaluation for cancellation-sensitive checks."""
    mp.mp.dps = digits
    x = mp.mpf(x)
    value = mp.mpf(1)
    for k in range(1, 500):
        y = x / (mp.mpf(2) ** k)
        value *= mp.mpf(1) if y == 0 else mp.sin(y) / y
        if abs(y) < mp.mpf(10) ** (-(digits - 15)):
            break
    return value


def head_spectrum_mp(x: mp.mpf, n: int) -> mp.mpf:
    value = mp.mpf(1)
    for k in range(1, n + 1):
        y = x / (mp.mpf(2) ** k)
        value *= mp.mpf(1) if y == 0 else mp.sin(y) / y
    return value


def zero_multiplicity_finite(n: int, m: int) -> int:
    """Order of the zero of F_n at xi=2*pi*m, for m != 0."""
    if m == 0:
        raise ValueError("m must be nonzero")
    v = 0
    q = abs(m)
    while q % 2 == 0:
        q //= 2
        v += 1
    return min(n, v + 1) + (1 if v >= n - 1 else 0)


def zero_multiplicity_limit(m: int) -> int:
    """Order of the zero of Phi at xi=2*pi*m."""
    if m == 0:
        raise ValueError("m must be nonzero")
    v = 0
    q = abs(m)
    while q % 2 == 0:
        q //= 2
        v += 1
    return v + 1


def maximize_on_lobes(function: Callable[[float], float], lobes: int) -> tuple[float, float, int]:
    """Maximize a nonnegative function separately on 2*pi lobes."""
    best_x = 0.0
    best_value = -1.0
    best_lobe = 0
    for m in range(lobes):
        left = 2.0 * PI * m
        right = 2.0 * PI * (m + 1)
        result = minimize_scalar(
            lambda x: -function(float(x)),
            bounds=(left + 1.0e-10, right - 1.0e-10),
            method="bounded",
            options={"xatol": 1.0e-12},
        )
        value = -float(result.fun)
        if value > best_value:
            best_x = float(result.x)
            best_value = value
            best_lobe = m
    return best_x, best_value, best_lobe


def integrate_lobes(function: Callable[[float], float], lobes: int) -> float:
    """Integrate a nonnegative/effectively nonnegative function on [0,2*pi*lobes]."""
    total = 0.0
    for m in range(lobes):
        left = 2.0 * PI * m
        right = 2.0 * PI * (m + 1)
        total += quad(
            function,
            left,
            right,
            epsabs=1.0e-13,
            epsrel=2.0e-10,
            limit=160,
        )[0]
    return total




def integrate_lobes_fixed(
    function: Callable[[np.ndarray], np.ndarray],
    lobes: int,
    nodes_per_lobe: int = 40,
) -> float:
    """Fast composite Gauss-Legendre integration over 2*pi lobes.

    The integrands in this report are smooth inside each common-zero interval.
    A fixed rule therefore converges rapidly and avoids thousands of expensive
    adaptive scalar calls.  Forty nodes per lobe reproduce the independently
    checked adaptive values to the digits printed in the report.
    """
    nodes, weights = leggauss(nodes_per_lobe)
    lobe_indices = np.arange(lobes, dtype=float)[:, None]
    midpoints = 2.0 * PI * (lobe_indices + 0.5)
    half_width = PI
    x = midpoints + half_width * nodes[None, :]
    values = np.asarray(function(x), dtype=float)
    return float(half_width * np.sum(values * weights[None, :]))

def qhat_uniform(z: np.ndarray | float) -> np.ndarray:
    return sinc_np(z)


def qhat_variance_box(z: np.ndarray | float) -> np.ndarray:
    """Uniform[-1/sqrt(3),1/sqrt(3)], matching Var(up)=1/9."""
    return sinc_np(np.asarray(z, dtype=float) / math.sqrt(3.0))


def qhat_lobatto3(z: np.ndarray | float) -> np.ndarray:
    """Three-node endpoint-preserving Lobatto rule for the up law."""
    arr = np.asarray(z, dtype=float)
    return 8.0 / 9.0 + np.cos(arr) / 9.0


def qhat_gauss3(z: np.ndarray | float) -> np.ndarray:
    """Three-node Gaussian rule, exact through polynomial degree five."""
    arr = np.asarray(z, dtype=float)
    a = math.sqrt(19.0 / 75.0)
    total_side_mass = 25.0 / 57.0
    return 1.0 - total_side_mass + total_side_mass * np.cos(a * arr)


def qhat_lobatto5(z: np.ndarray | float) -> np.ndarray:
    """Five-node up-Gauss-Lobatto rule, exact through degree seven.

    The weights below are total symmetric-pair masses; each endpoint or
    interior nonzero node receives half of the corresponding total mass.
    """
    arr = np.asarray(z, dtype=float)
    a = math.sqrt(683.0 / 3087.0)
    endpoint_total = 619.0 / 135225.0
    interior_total = 4941258.0 / 10262075.0
    center = 78976.0 / 153675.0
    return center + interior_total * np.cos(a * arr) + endpoint_total * np.cos(arr)


def qhat_beta3(z: np.ndarray | float) -> np.ndarray:
    """Fourier transform of q(x)=35/32*(1-x^2)^3 on [-1,1].

    The identity qhat(z)=105*j_3(z)/z^3 uses the spherical Bessel function.
    A short series is used near zero to avoid a 0/0 cancellation.
    """
    arr = np.asarray(z, dtype=float)
    result = np.empty_like(arr)
    small = np.abs(arr) < 1.0e-4
    z2 = arr[small] ** 2
    # Moments are E[X^2]=1/9, E[X^4]=1/33, E[X^6]=5/429.
    result[small] = 1.0 - z2 / 18.0 + z2**2 / (24.0 * 33.0) - 5.0 * z2**3 / (720.0 * 429.0)
    nonsmall = ~small
    result[nonsmall] = 105.0 * spherical_jn(3, arr[nonsmall]) / (arr[nonsmall] ** 3)
    return result


SURROGATES: dict[str, Callable[[np.ndarray | float], np.ndarray]] = {
    "uniform": qhat_uniform,
    "variance_box": qhat_variance_box,
    "lobatto3": qhat_lobatto3,
    "gauss3": qhat_gauss3,
    "lobatto5": qhat_lobatto5,
    "beta3": qhat_beta3,
}


def surrogate_spectrum_np(x: np.ndarray | float, n: int, kind: str) -> np.ndarray:
    arr = np.asarray(x, dtype=float)
    return head_spectrum_np(arr, n) * SURROGATES[kind](arr / (2.0**n))


def save_csv(path: Path, fieldnames: Iterable[str], rows: Iterable[dict[str, object]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(fieldnames))
        writer.writeheader()
        writer.writerows(rows)


def make_figures(output: Path, coefficients: list[sp.Rational], phi_pi: float) -> None:
    """Generate the report figures in both PDF and PNG formats."""
    # 1. Signed finite spectra on the first few lobes.
    x = np.linspace(-40.0, 40.0, 16001)
    plt.figure(figsize=(8.0, 4.6))
    plt.plot(x, phi_np(x), linewidth=2.0, label=r"$\Phi$")
    for n in (2, 4, 6):
        plt.plot(x, finite_spectrum_np(x, n), linewidth=1.0, label=rf"$F_{{{n}}}$")
    plt.xlabel(r"frequency $\xi$")
    plt.ylabel("Fourier amplitude")
    plt.title("Finite repeated-integration spectra")
    plt.legend()
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    for suffix in ("pdf", "png"):
        plt.savefig(output / f"finite_spectra.{suffix}", dpi=220)
    plt.close()

    # 2. Absolute spectra over a wider range, exposing the finite algebraic tails.
    x = np.linspace(0.0, 260.0, 30001)
    floor = 1.0e-18
    plt.figure(figsize=(8.0, 4.6))
    plt.semilogy(x, np.maximum(np.abs(phi_np(x)), floor), linewidth=2.0, label=r"$|\Phi|$")
    for n in (3, 5, 7):
        plt.semilogy(
            x,
            np.maximum(np.abs(finite_spectrum_np(x, n)), floor),
            linewidth=1.0,
            label=rf"$|F_{{{n}}}|$",
        )
    plt.xlabel(r"frequency $\xi$")
    plt.ylabel("absolute amplitude")
    plt.title("The finite products retain algebraic far tails")
    plt.ylim(floor, 2.0)
    plt.legend()
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    for suffix in ("pdf", "png"):
        plt.savefig(output / f"finite_spectra_log.{suffix}", dpi=220)
    plt.close()

    # 3. Universal scaled leading error.
    x = np.linspace(-34.0, 34.0, 18001)
    limit_profile = -(x**2) * phi_np(x) / 9.0
    plt.figure(figsize=(8.0, 4.6))
    plt.plot(x, limit_profile, linewidth=2.2, label=r"$-\xi^2\Phi(\xi)/9$")
    for n in (3, 5, 7):
        scaled = (4.0**n) * (finite_spectrum_np(x, n) - phi_np(x))
        plt.plot(x, scaled, linewidth=1.0, label=rf"$4^{{{n}}}(F_{{{n}}}-\Phi)$")
    plt.xlabel(r"frequency $\xi$")
    plt.ylabel("scaled error")
    plt.title(r"Weighted $L^p$ limit profile of the Fourier error")
    plt.legend()
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    for suffix in ("pdf", "png"):
        plt.savefig(output / f"scaled_fourier_error.{suffix}", dpi=220)
    plt.close()

    # 4. Transfer function on the first meromorphic cell.  Values too close to
    # the removable zero of Phi at 2*pi are masked to avoid floating division.
    z = np.linspace(0.0, 3.96 * PI, 24000)
    denominator = phi_np(z)
    A = np.divide(sinc_np(z), denominator, out=np.full_like(z, np.nan), where=np.abs(denominator) > 1.0e-9)
    A[np.abs(A) > 20.0] = np.nan
    plt.figure(figsize=(8.0, 4.6))
    plt.plot(z / PI, A, linewidth=1.2)
    plt.axhline(1.0, linewidth=0.8)
    plt.xlabel(r"$z/\pi$")
    plt.ylabel(r"$A(z)=\operatorname{sinc}(z)/\Phi(z)$")
    plt.title("Universal meromorphic tail-transfer profile")
    plt.ylim(-3.0, 12.0)
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    for suffix in ("pdf", "png"):
        plt.savefig(output / f"transfer_profile.{suffix}", dpi=220)
    plt.close()

    # 5. Darboux coefficient asymptotic from the nearest poles at +/-4*pi.
    orders = np.arange(2, len(coefficients), dtype=int)
    asymptotic = np.array([2.0 / (phi_pi * (4.0 * PI) ** (2 * int(r))) for r in orders])
    exact = np.array([float(coefficients[int(r)]) for r in orders])
    ratio = exact / asymptotic
    plt.figure(figsize=(8.0, 4.6))
    plt.plot(orders, ratio, marker="o", markersize=3.2, linewidth=1.1)
    plt.axhline(1.0, linewidth=0.8)
    plt.xlabel(r"coefficient index $r$")
    plt.ylabel(r"$a_r\,\Phi(\pi)(4\pi)^{2r}/2$")
    plt.title("Nearest-pole asymptotic of the transfer coefficients")
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    for suffix in ("pdf", "png"):
        plt.savefig(output / f"coefficient_asymptotic.{suffix}", dpi=220)
    plt.close()

    # 6. Comparison of original and accelerated tail surrogates at n=3.
    x = np.linspace(0.0, 300.0, 36001)
    plt.figure(figsize=(8.0, 4.8))
    for kind, label in (
        ("uniform", "uniform tail (original)"),
        ("beta3", r"polynomial tail $35(1-x^2)^3/32$"),
        ("lobatto3", "3-node Lobatto tail"),
        ("gauss3", "3-node Gaussian tail"),
        ("lobatto5", "5-node Lobatto tail"),
    ):
        error = np.abs(surrogate_spectrum_np(x, 3, kind) - phi_np(x))
        plt.semilogy(x, np.maximum(error, 1.0e-16), linewidth=1.0, label=label)
    plt.xlabel(r"frequency $\xi$")
    plt.ylabel("absolute spectral error")
    plt.title("Moment-matched tail replacements (stage n=3)")
    plt.ylim(1.0e-16, 1.0)
    plt.legend(fontsize=8)
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    for suffix in ("pdf", "png"):
        plt.savefig(output / f"accelerated_surrogates.{suffix}", dpi=220)
    plt.close()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path("experiment_output"))
    parser.add_argument("--coefficient-order", type=int, default=30)
    args = parser.parse_args()
    output = args.output_dir
    output.mkdir(parents=True, exist_ok=True)

    # Exact transfer coefficients and nearest-pole asymptotic.
    ell, coefficients = transfer_coefficients(args.coefficient_order)
    phi_pi_mp = phi_mp(mp.pi, digits=120)
    phi_pi = float(phi_pi_mp)
    coefficient_rows: list[dict[str, object]] = []
    for r, coefficient in enumerate(coefficients):
        if r == 0:
            asymptotic = float("nan")
            ratio = float("nan")
        else:
            asymptotic = 2.0 / (phi_pi * (4.0 * PI) ** (2 * r))
            ratio = float(coefficient) / asymptotic
        coefficient_rows.append(
            {
                "r": r,
                "a_r_exact": str(coefficient),
                "a_r_decimal": f"{float(coefficient):.18e}",
                "nearest_pole_asymptotic": "" if r == 0 else f"{asymptotic:.18e}",
                "ratio_to_asymptotic": "" if r == 0 else f"{ratio:.18e}",
                "log_coefficient_ell_r": "" if r == 0 else str(ell[r]),
            }
        )
    save_csv(
        output / "transfer_coefficients.csv",
        coefficient_rows[0].keys(),
        coefficient_rows,
    )

    # Leading weighted L^p constants.
    max_x, max_value, max_lobe = maximize_on_lobes(
        lambda x: x * x * abs(float(phi_np(x))), lobes=60
    )
    c_inf = max_value / 9.0
    # The absolute L^1 integral converges somewhat more slowly across lobes;
    # 700 lobes are used for the quoted digits.  L^2 is much faster.
    integral_l1_half = integrate_lobes_fixed(
        lambda x: x * x * np.abs(phi_np(x)), lobes=700, nodes_per_lobe=48
    )
    integral_l2_half = integrate_lobes_fixed(
        lambda x: (x**4) * phi_np(x) ** 2, lobes=260, nodes_per_lobe=40
    )
    c_1 = 2.0 * integral_l1_half / 9.0
    c_2 = math.sqrt(2.0 * integral_l2_half) / 9.0

    norm_rows: list[dict[str, object]] = []
    for n in range(3, 9):
        sup_x, sup_value, sup_lobe = maximize_on_lobes(
            lambda x, n=n: abs(float(finite_spectrum_np(x, n) - phi_np(x))),
            lobes=40,
        )
        l1_half = integrate_lobes_fixed(
            lambda x, n=n: np.abs(finite_spectrum_np(x, n) - phi_np(x)),
            lobes=420,
            nodes_per_lobe=48,
        )
        l2_half = integrate_lobes_fixed(
            lambda x, n=n: (finite_spectrum_np(x, n) - phi_np(x)) ** 2,
            lobes=260,
            nodes_per_lobe=40,
        )
        scale = 4.0**n
        norm_rows.append(
            {
                "n": n,
                "scaled_Linf": f"{scale * sup_value:.15g}",
                "Linf_maximizer_xi": f"{sup_x:.15g}",
                "Linf_lobe": sup_lobe,
                "scaled_L1": f"{scale * 2.0 * l1_half:.15g}",
                "scaled_L2": f"{scale * math.sqrt(2.0 * l2_half):.15g}",
                "limit_Linf": f"{c_inf:.15g}",
                "limit_L1": f"{c_1:.15g}",
                "limit_L2": f"{c_2:.15g}",
            }
        )
    save_csv(output / "fourier_norm_convergence.csv", norm_rows[0].keys(), norm_rows)

    # Exact moments of the up distribution through degree eight.
    kappa2 = sp.Rational(1, 9)
    kappa4 = -sp.Rational(2, 225)
    kappa6 = sp.Rational(16, 3969)
    kappa8 = -sp.Rational(16, 3825)
    mu2 = kappa2
    mu4 = sp.factor(kappa4 + 3 * kappa2**2)
    mu6 = sp.factor(kappa6 + 15 * kappa4 * kappa2 + 15 * kappa2**3)
    mu8 = sp.factor(
        kappa8
        + 28 * kappa6 * kappa2
        + 35 * kappa4**2
        + 210 * kappa4 * kappa2**2
        + 105 * kappa2**4
    )

    # Tail surrogate metadata.  "order" means the first nonzero z^(2M)
    # term in qhat(z)-Phi(z), hence convergence scale 4^(-M n).
    surrogate_rows = [
        {
            "name": "uniform_original",
            "support": "[-1,1]",
            "type": "uniform density",
            "matched_degree": 1,
            "first_power_2M": 2,
            "leading_characteristic_coefficient": "-1/9",
            "rate": "4^(-n)",
        },
        {
            "name": "variance_matched_box",
            "support": "[-1/sqrt(3),1/sqrt(3)]",
            "type": "uniform density",
            "matched_degree": 3,
            "first_power_2M": 4,
            "leading_characteristic_coefficient": "-1/4050",
            "rate": "16^(-n)",
        },
        {
            "name": "up_Lobatto_3",
            "support": "{-1,0,1}",
            "type": "positive atomic, endpoints included",
            "matched_degree": 3,
            "first_power_2M": 4,
            "leading_characteristic_coefficient": "7/2025",
            "rate": "16^(-n)",
        },
        {
            "name": "up_Gauss_3",
            "support": "{0,+/-sqrt(19/75)}",
            "type": "positive atomic",
            "matched_degree": 5,
            "first_power_2M": 6,
            "leading_characteristic_coefficient": "1238/334884375",
            "rate": "64^(-n)",
        },
        {
            "name": "up_Lobatto_5",
            "support": "{-1,0,1,+/-sqrt(683/3087)}",
            "type": "positive atomic, endpoints included",
            "matched_degree": 7,
            "first_power_2M": 8,
            "leading_characteristic_coefficient": "1006207/24604155961875",
            "rate": "256^(-n)",
        },
        {
            "name": "beta_polynomial_3",
            "support": "[-1,1]",
            "type": "density 35(1-x^2)^3/32",
            "matched_degree": 3,
            "first_power_2M": 4,
            "leading_characteristic_coefficient": "2/22275",
            "rate": "16^(-n)",
        },
    ]
    save_csv(output / "tail_surrogates.csv", surrogate_rows[0].keys(), surrogate_rows)

    # High-precision checks at the maximizers of the predicted limit profiles.
    weighted_maxima: dict[int, tuple[float, float, int]] = {}
    for power in (2, 4, 6, 8):
        weighted_maxima[power] = maximize_on_lobes(
            lambda x, power=power: (x**power) * abs(float(phi_np(x))),
            lobes=70,
        )

    mp.mp.dps = 120
    gauss3_a = mp.sqrt(mp.mpf(19) / 75)
    gauss3_side = mp.mpf(25) / 57
    lobatto5_a = mp.sqrt(mp.mpf(683) / 3087)
    lobatto5_endpoint = mp.mpf(619) / 135225
    lobatto5_interior = mp.mpf(4941258) / 10262075
    lobatto5_center = mp.mpf(78976) / 153675

    def qhat_mp(kind: str, z: mp.mpf) -> mp.mpf:
        if kind == "gauss3":
            return 1 - gauss3_side + gauss3_side * mp.cos(gauss3_a * z)
        if kind == "lobatto5":
            return (
                lobatto5_center
                + lobatto5_interior * mp.cos(lobatto5_a * z)
                + lobatto5_endpoint * mp.cos(z)
            )
        raise ValueError(kind)

    high_precision_rows: list[dict[str, object]] = []
    for kind, M, leading in (
        ("gauss3", 3, mp.mpf(1238) / 334884375),
        ("lobatto5", 4, mp.mpf(1006207) / 24604155961875),
    ):
        power = 2 * M
        x_star = mp.mpf(str(weighted_maxima[power][0]))
        predicted = abs(leading) * (x_star**power) * abs(phi_mp(x_star, digits=120))
        n_values = range(6, 12) if kind == "gauss3" else range(8, 15)
        for n in n_values:
            approximation = head_spectrum_mp(x_star, n) * qhat_mp(kind, x_star / (mp.mpf(2) ** n))
            error = approximation - phi_mp(x_star, digits=120)
            scaled = (mp.mpf(4) ** (M * n)) * abs(error)
            high_precision_rows.append(
                {
                    "surrogate": kind,
                    "M": M,
                    "n": n,
                    "xi_test": mp.nstr(x_star, 20),
                    "scaled_point_error": mp.nstr(scaled, 25),
                    "predicted_limit_at_xi_test": mp.nstr(predicted, 25),
                }
            )
    save_csv(
        output / "accelerated_surrogate_validation.csv",
        high_precision_rows[0].keys(),
        high_precision_rows,
    )

    # Zero-multiplicity table for a few representative n and valuations.
    zero_rows: list[dict[str, object]] = []
    for n in range(2, 8):
        for valuation in range(0, n + 5):
            m = 2**valuation
            finite_order = zero_multiplicity_finite(n, m)
            limit_order = zero_multiplicity_limit(m)
            zero_rows.append(
                {
                    "n": n,
                    "v2_m": valuation,
                    "finite_order": finite_order,
                    "limit_order": limit_order,
                    "defect_finite_minus_limit": finite_order - limit_order,
                }
            )
    save_csv(output / "zero_multiplicity_defects.csv", zero_rows[0].keys(), zero_rows)

    make_figures(output, coefficients, phi_pi)

    summary = {
        "phi_pi": mp.nstr(phi_pi_mp, 50),
        "nearest_pole_residue_at_4pi": mp.nstr(-4 * mp.pi / phi_pi_mp, 50),
        "leading_Linf_constant": c_inf,
        "leading_Linf_maximizer": max_x,
        "leading_Linf_lobe": max_lobe,
        "leading_L1_constant": c_1,
        "leading_L2_constant": c_2,
        "up_moments": {
            "mu2": str(mu2),
            "mu4": str(mu4),
            "mu6": str(mu6),
            "mu8": str(mu8),
        },
        "weighted_profile_maxima": {
            str(power): {
                "xi": value[0],
                "max_abs_xi_power_phi": value[1],
                "lobe": value[2],
            }
            for power, value in weighted_maxima.items()
        },
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")

    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
