#!/usr/bin/env python3
"""Numerical and exact-arithmetic experiments for finite dyadic sinc products.

The Rvachev up-function has Fourier transform

    Phi(xi) = product_{j>=0} sinc(pi*xi/2**j),

with the Fourier convention F[f](xi)=integral f(x) exp(-2*pi*i*x*xi) dx.
NumPy's ``np.sinc(y)`` equals sin(pi*y)/(pi*y), so a factor is simply
``np.sinc(xi/2**j)``.

The n-factor prefix product is the transform of the density p_n of

    S_n = sum_{j=0}^{n-1} 2**(-j-1) U_j,   U_j ~ Uniform[-1,1].

This script:
  * reconstructs up and p_n by a Fourier-series/FFT inversion on a box large
    enough to avoid overlap of their compact supports;
  * verifies the sharp formula
        ||p_n^(r)-up^(r)||_infinity
        = 2**(binom(r+3,2)-1) / (9*4**n),  n >= r+3;
  * tests three positive tail surrogates derived from quadrature of the
    exact scale-mixture law: a one-node Gauss rule, a two-node endpoint
    Lobatto rule, and a two-node right-Radau rule;
  * generates the figures and CSV tables used by the accompanying report;
  * supplies a high-precision exact truncated-power evaluator for rational
    arguments and functions for Bell/Richardson coefficients.

The FFT computations are numerical evidence, not the proof.  The report gives
self-contained proofs of the exact prefix error law and of the all-orders
asymptotic expansion.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import numpy as np


# ---------------------------------------------------------------------------
# Fourier products and inversion
# ---------------------------------------------------------------------------

def phi_prefix(freq: np.ndarray, n: int) -> np.ndarray:
    """Return the n-factor partial product Phi_n on an array of frequencies."""
    if n < 1:
        raise ValueError("n must be at least 1")
    ans = np.ones_like(freq, dtype=np.float64)
    for j in range(n):
        ans *= np.sinc(freq / (2**j))
    return ans


def phi_up(freq: np.ndarray, factors: int = 48) -> np.ndarray:
    """Truncate the infinite product after enough factors for double precision.

    For the frequency ranges used here, 48 factors make the omitted logarithmic
    tail far smaller than machine precision at frequencies that materially
    contribute to the inverse transform.
    """
    ans = np.ones_like(freq, dtype=np.float64)
    for j in range(factors):
        ans *= np.sinc(freq / (2**j))
    return ans


def phi_tail_replacement(freq: np.ndarray, n: int) -> np.ndarray:
    """Fourier transform of the repeated-integration/tail-replacement spline.

    The omitted tail has support radius delta=2**(-n).  Replacing it by a
    uniform variable on [-delta,delta] appends sinc(2*pi*delta*xi), which in
    NumPy normalization is np.sinc(freq/2**(n-1)).
    """
    return phi_prefix(freq, n) * np.sinc(freq / (2 ** (n - 1)))




def phi_scale_mixture_tail(
    freq: np.ndarray,
    n: int,
    nodes: Sequence[float],
    weights: Sequence[float],
) -> np.ndarray:
    """Transform of p_n convolved with a positive uniform scale mixture.

    The omitted tail is delta*X with delta=2**(-n).  A quadrature rule for
    the squared scale Z replaces X by sqrt(Z_Q)*U, where U is uniform on
    [-1,1].  Conditional on Z_Q=z, the tail transform is

        sinc(2*pi*delta*sqrt(z)*xi).

    In NumPy normalization this is ``np.sinc(2*delta*sqrt(z)*freq)``.
    Nodes and weights are ordinary floating-point representations of the
    exact rational rules listed in the report.
    """
    if len(nodes) != len(weights):
        raise ValueError("nodes and weights must have the same length")
    if not nodes:
        raise ValueError("at least one quadrature node is required")
    delta = 2.0 ** (-n)
    tail_hat = np.zeros_like(freq, dtype=np.float64)
    for node, weight in zip(nodes, weights):
        if node < 0.0:
            raise ValueError("squared-scale nodes must be nonnegative")
        tail_hat += weight * np.sinc(2.0 * delta * np.sqrt(node) * freq)
    return phi_prefix(freq, n) * tail_hat

def inverse_fourier_series(hat_values: np.ndarray, box_length: float) -> tuple[np.ndarray, np.ndarray]:
    """Invert samples hat_f(k/L) to f on a centered periodic grid.

    All functions in this experiment are supported in [-1,1], while L=4, so
    periodization introduces no overlap.  Increasing the FFT length controls
    Fourier truncation error.
    """
    count = hat_values.size
    values = np.fft.fftshift(np.fft.ifft(hat_values).real) * count / box_length
    x = (np.arange(count) - count // 2) * (box_length / count)
    return x, values


def differentiated_transform(hat_values: np.ndarray, freq: np.ndarray, order: int) -> np.ndarray:
    """Fourier transform of the indicated derivative."""
    return (2j * np.pi * freq) ** order * hat_values


# ---------------------------------------------------------------------------
# Exact formulas
# ---------------------------------------------------------------------------

def thue_morse_sign(k: int) -> int:
    """Signed Thue-Morse value (-1)^s_2(k)."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    return -1 if (k.bit_count() & 1) else 1


def positive_power_fraction(x: Fraction, degree: int) -> Fraction:
    """Return (x_+)^degree, with the standard degree-zero convention."""
    if degree == 0:
        return Fraction(1) if x > 0 else Fraction(0)
    return x**degree if x > 0 else Fraction(0)


def prefix_density_exact(n: int, x: Fraction | int) -> Fraction:
    r"""Evaluate p_n(x) exactly at a rational point.

    The formula is

      p_n(x) = 2^{n(n-1)/2}/(n-1)! * sum_{k=0}^{2^n-1}
               tau_k (x + 1 - 2^{-n} - k/2^{n-1})_+^{n-1}.

    It is exact but can be expensive and cancellation-prone for large n; use it
    as a verification device, not as the main floating-point algorithm.
    """
    if n < 1:
        raise ValueError("n must be at least 1")
    xq = Fraction(x)
    degree = n - 1
    support_radius = Fraction((1 << n) - 1, 1 << n)
    mesh = Fraction(1, 1 << (n - 1))
    coefficient = Fraction(1 << (n * (n - 1) // 2), factorial(degree))
    total = Fraction(0)
    for k in range(1 << n):
        argument = xq + support_radius - k * mesh
        total += thue_morse_sign(k) * positive_power_fraction(argument, degree)
    return coefficient * total


def reciprocal_product_coefficients(count: int) -> list[Fraction]:
    r"""Return a_m in 1/Phi(z)=sum a_m (2*pi*z)^{2m}.

    Write

      alpha_j = |B_{2j}| / (2*j*(2j)!*(1-2^{-2j})),
      exp(sum_{j>=1} alpha_j t^j) = sum_{m>=0} a_m t^m.

    We avoid a mandatory symbolic dependency by hard-coding Bernoulli numbers
    through the modest orders used in the report.  Extend the dictionary when
    more coefficients are desired.
    """
    bernoulli_abs: dict[int, Fraction] = {
        2: Fraction(1, 6),
        4: Fraction(1, 30),
        6: Fraction(1, 42),
        8: Fraction(1, 30),
        10: Fraction(5, 66),
        12: Fraction(691, 2730),
        14: Fraction(7, 6),
        16: Fraction(3617, 510),
        18: Fraction(43867, 798),
        20: Fraction(174611, 330),
    }
    if count > 11:
        raise ValueError("extend bernoulli_abs before requesting count > 11")

    alpha = [Fraction(0)] * count
    for j in range(1, count):
        b = bernoulli_abs[2 * j]
        alpha[j] = b / (
            2 * j * factorial(2 * j) * (Fraction(1) - Fraction(1, 2) ** (2 * j))
        )

    a = [Fraction(0)] * count
    a[0] = Fraction(1)
    # If A(t)=exp(g(t)), then m*a_m=sum_{j=1}^m j*alpha_j*a_{m-j}.
    for m in range(1, count):
        a[m] = sum(j * alpha[j] * a[m - j] for j in range(1, m + 1)) / m
    return a


def richardson_weights(order: int, q: Fraction = Fraction(1, 4)) -> list[Fraction]:
    """Geometric Richardson weights for nodes 1,q,...,q^(order-1).

    They satisfy sum_j w_j q^(j*m)=0 for 1<=m<order and sum_j w_j=1.
    """
    if order < 1:
        raise ValueError("order must be positive")
    weights: list[Fraction] = []
    for j in range(order):
        xj = q**j
        weight = Fraction(1)
        for ell in range(order):
            if ell == j:
                continue
            xell = q**ell
            weight *= -xell / (xj - xell)
        weights.append(weight)
    return weights


# ---------------------------------------------------------------------------
# Experiment driver
# ---------------------------------------------------------------------------

def write_csv(path: Path, rows: Iterable[Sequence[object]], header: Sequence[str]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(header)
        writer.writerows(rows)


def run(output_dir: Path, fft_power: int = 17, box_length: float = 4.0) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    count = 1 << fft_power
    dx = box_length / count
    freq = np.fft.fftfreq(count, d=dx)

    up_hat = phi_up(freq)
    x, up = inverse_fourier_series(up_hat, box_length)
    support_mask = (x >= -1.0) & (x <= 1.0)

    # Figure 1: finite products as piecewise-polynomial densities.
    plt.figure(figsize=(7.2, 4.5))
    plt.plot(x[support_mask], up[support_mask], label="up")
    for n in (2, 3, 5, 8):
        _, pn = inverse_fourier_series(phi_prefix(freq, n), box_length)
        plt.plot(x[support_mask], pn[support_mask], label=f"p_{n}")
    plt.xlabel("x")
    plt.ylabel("density")
    plt.title("Inverse transforms of finite dyadic sinc products")
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "finite_sinc_approximants.pdf")
    plt.close()

    # Figure 2: scaled error profiles and the leading differential profile.
    up_second_hat = differentiated_transform(up_hat, freq, 2)
    _, up_second = inverse_fourier_series(up_second_hat, box_length)
    plt.figure(figsize=(7.2, 4.5))
    for n in (4, 6, 8):
        diff_hat = phi_prefix(freq, n) - up_hat
        _, diff = inverse_fourier_series(diff_hat, box_length)
        plt.plot(x[support_mask], (4**n) * diff[support_mask], label=f"4^{n}(p_{n}-up)")
    plt.plot(x[support_mask], -up_second[support_mask] / 18.0, label="-up''/18")
    plt.xlabel("x")
    plt.ylabel("scaled error")
    plt.title("Collapse of the finite-product error profile")
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "scaled_error_profiles.pdf")
    plt.close()

    # Sharp C^r error verification table.
    sharp_rows: list[list[object]] = []
    for r in range(5):
        for n in range(r + 3, r + 7):
            difference_hat = differentiated_transform(phi_prefix(freq, n) - up_hat, freq, r)
            _, difference = inverse_fourier_series(difference_hat, box_length)
            measured = float(np.max(np.abs(difference[support_mask])))
            exponent = comb(r + 3, 2)
            predicted = (2 ** (exponent - 1)) / (9.0 * (4**n))
            sharp_rows.append([r, n, measured, predicted, measured / predicted])
    write_csv(
        output_dir / "sharp_error_verification.csv",
        sharp_rows,
        ("derivative_order_r", "prefix_length_n", "fft_sup_error", "exact_formula", "ratio"),
    )

    # Positive quadrature acceleration schemes.  The tuple entries are
    # (nodes z_j, weights w_j, first missed Z-moment ell, exact Gamma_Q).
    schemes = {
        "Gauss-1": ((1.0 / 3.0,), (1.0,), 2, 1.0 / 4050.0),
        "Lobatto-2": ((0.0, 1.0), (2.0 / 3.0, 1.0 / 3.0), 2, 13.0 / 8100.0),
        "Radau-2": ((13.0 / 45.0, 1.0), (15.0 / 16.0, 1.0 / 16.0), 3, 44.0 / 13395375.0),
    }
    positive_rows: list[list[object]] = []
    for scheme_name, (nodes, weights, ell, gamma) in schemes.items():
        for r in range(3):
            threshold = r + 2 * ell + 1
            for n in range(threshold, threshold + 2):
                approximant_hat = phi_scale_mixture_tail(freq, n, nodes, weights)
                diff_hat = differentiated_transform(approximant_hat - up_hat, freq, r)
                _, difference = inverse_fourier_series(diff_hat, box_length)
                measured = float(np.max(np.abs(difference[support_mask])))
                predicted = gamma * (2 ** comb(r + 2 * ell + 1, 2)) / ((2 ** (2 * ell)) ** n)
                positive_rows.append(
                    [scheme_name, ell, r, n, measured, predicted, measured / predicted]
                )
    write_csv(
        output_dir / "positive_acceleration_verification.csv",
        positive_rows,
        (
            "scheme",
            "first_missed_Z_moment_ell",
            "derivative_order_r",
            "prefix_length_n",
            "fft_sup_error",
            "exact_formula",
            "ratio",
        ),
    )

    # Figure 3: raw convergence and three positive acceleration hierarchies.
    ns = np.arange(3, 8)
    plt.figure(figsize=(7.2, 4.5))

    raw_errors = []
    for n in ns:
        _, raw_diff = inverse_fourier_series(phi_prefix(freq, int(n)) - up_hat, box_length)
        raw_errors.append(float(np.max(np.abs(raw_diff[support_mask]))))
    plt.semilogy(ns, raw_errors, marker="o", label="raw prefix (order 2)")

    for scheme_name, (nodes, weights, _ell, _gamma) in schemes.items():
        measured_errors = []
        for n in ns:
            approximant_hat = phi_scale_mixture_tail(freq, int(n), nodes, weights)
            _, difference = inverse_fourier_series(approximant_hat - up_hat, box_length)
            measured_errors.append(float(np.max(np.abs(difference[support_mask]))))
        plt.semilogy(ns, measured_errors, marker="o", label=scheme_name)

    plt.xlabel("number n of retained sinc factors")
    plt.ylabel("uniform error")
    plt.title("Raw convergence and positive moment-matched acceleration")
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "convergence_comparison.pdf")
    plt.close()

    # Text file with exact coefficients and Richardson weights.
    coefficients = reciprocal_product_coefficients(6)
    with (output_dir / "exact_coefficients.txt").open("w", encoding="utf-8") as handle:
        handle.write("a_m in 1/Phi(z)=sum a_m (2*pi*z)^(2m):\n")
        for index, coefficient in enumerate(coefficients):
            handle.write(f"a_{index} = {coefficient}\n")
        handle.write("\nGeometric Richardson weights (q=1/4):\n")
        for order in range(1, 6):
            weights = richardson_weights(order)
            handle.write(f"M={order}: {weights}; l1={sum(abs(w) for w in weights)}\n")

    # A few exact rational checks of the truncated-power formula.
    exact_rows = []
    test_points = (Fraction(0), Fraction(1, 4), Fraction(1, 2), Fraction(3, 4))
    for n in range(2, 7):
        for point in test_points:
            exact_rows.append([n, str(point), str(prefix_density_exact(n, point))])
    write_csv(output_dir / "exact_rational_samples.csv", exact_rows, ("n", "x", "p_n(x)"))

    print(f"Wrote figures and tables to {output_dir}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory for figures and tables (default: script directory)",
    )
    parser.add_argument(
        "--fft-power",
        type=int,
        default=17,
        help="use 2**FFT_POWER Fourier modes (default: 17)",
    )
    return parser.parse_args()


if __name__ == "__main__":
    arguments = parse_args()
    run(arguments.output_dir, arguments.fft_power)
