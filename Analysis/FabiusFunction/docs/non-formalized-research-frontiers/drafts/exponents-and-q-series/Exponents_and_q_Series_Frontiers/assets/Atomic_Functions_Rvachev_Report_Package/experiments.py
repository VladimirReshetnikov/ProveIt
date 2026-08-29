#!/usr/bin/env python3
"""Reproducible experiments for the atomic-functions report.

The script verifies the h_3 fixed point, the geometric local-degree law, the
q-Gaussian derivative Gram determinant, and the Edgeworth expansion of the
standardized Fup_n hierarchy.  Every random experiment uses a fixed seed;
Fup densities are obtained by deterministic FFT inversion.
"""
from __future__ import annotations

import csv
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent
FIGURES = ROOT / "figures"
DATA = ROOT / "data"
FIGURES.mkdir(exist_ok=True)
DATA.mkdir(exist_ok=True)


def sinc(z: np.ndarray | float) -> np.ndarray:
    """sin(z)/z with the removable value at zero filled in."""
    return np.sinc(np.asarray(z) / np.pi)


def gaussian(x: np.ndarray) -> np.ndarray:
    return np.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)


def hermite(n: int, x: np.ndarray) -> np.ndarray:
    """Probabilists' Hermite polynomial H_n."""
    if n == 0:
        return np.ones_like(x)
    if n == 1:
        return x.copy()
    hm1 = np.ones_like(x)
    h = x.copy()
    for k in range(1, n):
        hm1, h = h, x * h - k * hm1
    return h


# ---------------------------------------------------------------------------
# h_a fixed point
# ---------------------------------------------------------------------------

def fixed_point_density(
    a: float,
    grid_size: int = 24001,
    max_iterations: int = 300,
    tolerance: float = 2e-13,
) -> tuple[np.ndarray, np.ndarray, int, float]:
    """Iterate h(x)=(a/2) integral_{ax-1}^{ax+1} h(u) du on its support."""
    if a <= 1:
        raise ValueError("a must be greater than 1")
    b = 1.0 / (a - 1.0)
    x = np.linspace(-b, b, grid_size)
    dx = x[1] - x[0]
    f = np.full_like(x, 1.0 / (2.0 * b))
    error = math.inf
    for iteration in range(1, max_iterations + 1):
        primitive = np.empty_like(f)
        primitive[0] = 0.0
        primitive[1:] = np.cumsum((f[:-1] + f[1:]) * (0.5 * dx))
        upper = np.interp(a * x + 1.0, x, primitive, left=0.0, right=primitive[-1])
        lower = np.interp(a * x - 1.0, x, primitive, left=0.0, right=primitive[-1])
        new_f = np.maximum(0.5 * a * (upper - lower), 0.0)
        new_f /= np.trapezoid(new_f, x)
        error = float(np.max(np.abs(new_f - f)))
        f = new_f
        if error < tolerance:
            break
    return x, f, iteration, error


def make_ha_figure() -> None:
    a = 3.0
    b = 1.0 / (a - 1.0)
    b1 = (a - 2.0) / (a * (a - 1.0))
    x, f, iterations, update_error = fixed_point_density(a)
    diagnostics = {
        "a": a,
        "support_half_width": b,
        "central_gap_half_width": b1,
        "iterations": iterations,
        "last_sup_update": update_error,
        "mass": float(np.trapezoid(f, x)),
        "symmetry_sup_error": float(np.max(np.abs(f - f[::-1]))),
        "plateau_sup_error": float(np.max(np.abs(f[np.abs(x) <= 0.97*b1] - a/2.0))),
    }
    with (DATA / "ha_a3_diagnostics.csv").open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out)
        writer.writerow(["quantity", "value"])
        writer.writerows((key, f"{value:.17g}" if isinstance(value, float) else value)
                         for key, value in diagnostics.items())

    fig, ax = plt.subplots(figsize=(8.4, 4.6))
    ax.plot(x, f, linewidth=1.5, label="fixed-point approximation")
    ax.axhline(a / 2.0, linestyle="--", linewidth=0.9, label="exact plateau h_3=3/2")
    ax.axvline(-b1, linestyle=":", linewidth=0.8)
    ax.axvline(b1, linestyle=":", linewidth=0.8)
    ax.set(xlabel="x", ylabel="h_3(x)", xlim=(-b, b), title="The separated atomic density h_3")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(FIGURES / "ha_a3_density.png", dpi=220)
    fig.savefig(FIGURES / "ha_a3_density.pdf")
    plt.close(fig)


# ---------------------------------------------------------------------------
# Local polynomial degree
# ---------------------------------------------------------------------------

def make_local_degree_figure() -> None:
    a = 3.0
    p = 1.0 - 2.0 / a
    rng = np.random.default_rng(0xA70C1C)
    sample = rng.geometric(p, size=400_000) - 1
    degrees = np.arange(14)
    exact = p * (1.0 - p) ** degrees
    empirical = np.array([(sample == n).mean() for n in degrees])
    with (DATA / "local_degree_distribution_a3.csv").open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out)
        writer.writerow(["degree", "exact_probability", "empirical_probability"])
        for n, e, m in zip(degrees, exact, empirical, strict=True):
            writer.writerow([int(n), f"{e:.17g}", f"{m:.17g}"])
        writer.writerow([])
        writer.writerow(["sample_mean", f"{sample.mean():.17g}"])
        writer.writerow(["exact_mean", f"{(1-p)/p:.17g}"])
        writer.writerow(["sample_variance", f"{sample.var():.17g}"])
        writer.writerow(["exact_variance", f"{(1-p)/(p*p):.17g}"])

    width = 0.4
    fig, ax = plt.subplots(figsize=(8.4, 4.6))
    ax.bar(degrees - width/2, exact, width, label="exact geometric law")
    ax.bar(degrees + width/2, empirical, width, label="Monte Carlo")
    ax.set_yscale("log")
    ax.set(xlabel="local polynomial degree", ylabel="probability",
           title="Local degree for a=3")
    ax.set_xticks(degrees)
    ax.legend()
    ax.grid(True, axis="y", alpha=0.25)
    fig.tight_layout()
    fig.savefig(FIGURES / "local_degree_distribution.png", dpi=220)
    fig.savefig(FIGURES / "local_degree_distribution.pdf")
    plt.close(fig)


# ---------------------------------------------------------------------------
# q-Gaussian Gram matrix
# ---------------------------------------------------------------------------

def finite_q_pochhammer(q2: float, n: int) -> float:
    value = 1.0
    for d in range(1, n + 1):
        value *= 1.0 - q2 ** d
    return value


def theta_symbol(theta: np.ndarray, q: float) -> np.ndarray:
    result = np.ones_like(theta)
    for k in range(1, 100):
        term = q ** (k * k)
        if term < 1e-18:
            break
        result += 2.0 * term * np.cos(k * theta)
    return result


def make_gram_figure() -> None:
    a = 3.0
    q = 1.0 / a
    previous_logdet = 0.0
    with (DATA / "gram_determinant_validation.csv").open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out)
        writer.writerow(["N", "numeric_logdet", "product_logdet", "absolute_log_error",
                         "gram_schmidt_pivot", "finite_q_pochhammer"])
        for n in range(41):
            index = np.arange(n + 1)
            gram = q ** ((index[:, None] - index[None, :]) ** 2)
            sign, numeric = np.linalg.slogdet(gram)
            if sign <= 0:
                raise RuntimeError("loss of positive definiteness")
            product = sum((n + 1 - d) * math.log1p(-q ** (2*d)) for d in range(1, n + 1))
            pivot = math.exp(numeric - previous_logdet) if n else 1.0
            qpoch = finite_q_pochhammer(q*q, n)
            writer.writerow([n, f"{numeric:.17g}", f"{product:.17g}",
                             f"{abs(numeric-product):.17g}", f"{pivot:.17g}", f"{qpoch:.17g}"])
            previous_logdet = numeric

    theta = np.linspace(-math.pi, math.pi, 2001)
    symbol = theta_symbol(theta, q)
    lower, upper = float(symbol.min()), float(symbol.max())
    with (DATA / "gram_symbol_bounds.csv").open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out)
        writer.writerow(["a", "q", "theta4_lower_bound", "theta3_upper_bound"])
        writer.writerow([a, q, f"{lower:.17g}", f"{upper:.17g}"])

    fig, ax = plt.subplots(figsize=(8.4, 4.9))
    for dimension in [8, 16, 32, 64]:
        index = np.arange(dimension)
        gram = q ** ((index[:, None] - index[None, :]) ** 2)
        ax.plot(np.arange(dimension), np.linalg.eigvalsh(gram), marker=".", linewidth=0.8,
                label=f"N={dimension}")
    ax.axhline(lower, linestyle="--", linewidth=0.9, label="theta_4(0,q)")
    ax.axhline(upper, linestyle=":", linewidth=0.9, label="theta_3(0,q)")
    ax.set(xlabel="ordered eigenvalue index", ylabel="eigenvalue",
           title="Finite derivative Gram spectra for a=3")
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(FIGURES / "derivative_gram_spectrum.png", dpi=220)
    fig.savefig(FIGURES / "derivative_gram_spectrum.pdf")
    plt.close(fig)


# ---------------------------------------------------------------------------
# Fup_n and exact-cumulant Edgeworth expansion
# ---------------------------------------------------------------------------

def up_characteristic(t: np.ndarray, factors: int = 42) -> np.ndarray:
    result = np.ones_like(t)
    scale = 0.5
    for _ in range(factors):
        result *= sinc(t * scale)
        scale *= 0.5
    return result


def fup_characteristic_standardized(t: np.ndarray, n: int) -> np.ndarray:
    # The standardized law is that of V_n=2X+sum U_j divided by sqrt((3n+4)/9).
    scale = math.sqrt(3.0*n + 4.0) / 3.0
    return up_characteristic(2.0*t/scale) * sinc(t/scale) ** n


def invert_characteristic(values: np.ndarray, dx: float) -> np.ndarray:
    return np.fft.fftshift(np.fft.fft(values) / (values.size * dx)).real


def standardized_cumulant(n: int, m: int) -> float:
    bernoulli = {1: 1/6, 2: -1/30, 3: 1/42, 4: -1/30, 5: 5/66}
    b = bernoulli[m]
    kappa_uniform = 2.0 ** (2*m - 1) * b / m
    kappa_v = kappa_uniform * (n + 2.0 ** (2*m) / (2.0 ** (2*m) - 1.0))
    variance_v = (3.0*n + 4.0) / 9.0
    return kappa_v / variance_v ** m


def edgeworth_density(x: np.ndarray, n: int, order: int) -> np.ndarray:
    """Exact-cumulant Edgeworth polynomial through asymptotic weight `order`."""
    correction = np.zeros_like(x)

    def visit(m: int, remaining: int, coefficient: float, degree: int) -> None:
        if m > order + 1:
            correction[:] += coefficient * hermite(degree, x)
            return
        weight = m - 1
        base = standardized_cumulant(n, m) / math.factorial(2*m)
        term = 1.0
        for count in range(remaining // weight + 1):
            visit(m + 1, remaining - count*weight, coefficient*term, degree + count*2*m)
            term *= base / (count + 1)

    visit(2, order, 1.0, 0)
    return gaussian(x) * correction


def make_fup_figures() -> None:
    size = 2 ** 15
    dx = 0.002
    x = (np.arange(size) - size//2) * dx
    t = 2.0 * math.pi * np.fft.fftfreq(size, d=dx)
    normal = gaussian(x)

    fig, ax = plt.subplots(figsize=(8.4, 4.9))
    ax.plot(x, normal, linewidth=1.5, label="standard Gaussian")
    for n in [1, 4, 16, 64]:
        density = invert_characteristic(fup_characteristic_standardized(t, n), dx)
        ax.plot(x, density, linewidth=1.0, label=f"n={n}")
    ax.set(xlim=(-5, 5), ylim=(-0.002, None), xlabel="standardized coordinate",
           ylabel="density", title="Gaussian scaling limit of the Fup_n hierarchy")
    ax.legend(ncol=3)
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(FIGURES / "fup_clt.png", dpi=220)
    fig.savefig(FIGURES / "fup_clt.pdf")
    plt.close(fig)

    ns = [4, 8, 16, 32, 64, 128]
    errors0: list[float] = []
    errors1: list[float] = []
    errors2: list[float] = []
    with (DATA / "fup_edgeworth_validation.csv").open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out)
        writer.writerow(["n", "lambda4", "lambda6", "gaussian_sup_error",
                         "first_edgeworth_sup_error", "second_edgeworth_sup_error",
                         "n_times_gaussian_error", "n2_times_first_error", "n3_times_second_error"])
        for n in ns:
            density = invert_characteristic(fup_characteristic_standardized(t, n), dx)
            first = edgeworth_density(x, n, 1)
            second = edgeworth_density(x, n, 2)
            e0 = float(np.max(np.abs(density-normal)))
            e1 = float(np.max(np.abs(density-first)))
            e2 = float(np.max(np.abs(density-second)))
            errors0.append(e0); errors1.append(e1); errors2.append(e2)
            writer.writerow([n, f"{standardized_cumulant(n,2):.17g}",
                             f"{standardized_cumulant(n,3):.17g}", f"{e0:.17g}",
                             f"{e1:.17g}", f"{e2:.17g}", f"{n*e0:.17g}",
                             f"{n*n*e1:.17g}", f"{n*n*n*e2:.17g}"])

    fig, ax = plt.subplots(figsize=(8.4, 4.9))
    narray = np.asarray(ns, dtype=float)
    ax.loglog(ns, errors0, marker="o", label="Gaussian only")
    ax.loglog(ns, errors1, marker="s", label="through order n^-1")
    ax.loglog(ns, errors2, marker="^", label="through order n^-2")
    ax.loglog(ns, errors0[0]*(narray/ns[0])**-1, linestyle="--", linewidth=0.8,
              label="reference n^-1")
    ax.loglog(ns, errors1[0]*(narray/ns[0])**-2, linestyle=":", linewidth=0.8,
              label="reference n^-2")
    ax.loglog(ns, errors2[0]*(narray/ns[0])**-3, linestyle="-.", linewidth=0.8,
              label="reference n^-3")
    ax.set(xlabel="hierarchy level n", ylabel="uniform density error",
           title="Exact-cumulant Edgeworth convergence for Fup_n")
    ax.legend(ncol=2)
    ax.grid(True, which="both", alpha=0.25)
    fig.tight_layout()
    fig.savefig(FIGURES / "fup_edgeworth_error.png", dpi=220)
    fig.savefig(FIGURES / "fup_edgeworth_error.pdf")
    plt.close(fig)


def main() -> None:
    make_ha_figure()
    make_local_degree_figure()
    make_gram_figure()
    make_fup_figures()
    print(f"Wrote figures to {FIGURES}")
    print(f"Wrote data to {DATA}")


if __name__ == "__main__":
    main()
