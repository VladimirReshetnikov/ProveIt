#!/usr/bin/env python3
"""Reproducible numerical experiments for the Rvachev atomic-function report.

The script has two purposes.

1. It regenerates every numerical figure and CSV table referenced by the
   LaTeX report.
2. It independently stress-tests the exact identities proved in the report:
   the h_a fixed point, the geometric local-degree law, the q-Gaussian Gram
   determinants, the explicit q-binomial/Rogers--Szego orthogonalization,
   Schur--Vandermonde minor formulae, and the all-orders Edgeworth scaling.

No numerical result is used as a proof.  Exact claims are proved in the LaTeX
source; the computations below are diagnostics that make sign, normalization,
and indexing errors easy to detect.

Requirements
------------
Python 3.10 or newer, NumPy, and Matplotlib.  The script intentionally avoids
SciPy and external data files.
"""

from __future__ import annotations

import csv
import math
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parent
FIGURES = ROOT / "figures"
DATA = ROOT / "data"
FIGURES.mkdir(parents=True, exist_ok=True)
DATA.mkdir(parents=True, exist_ok=True)

RNG_SEED = 0x5A17_2026


def write_csv(path: Path, header: Sequence[str], rows: Iterable[Sequence[object]]) -> None:
    """Write a small machine-readable diagnostic table."""

    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(header)
        writer.writerows(rows)


def sinc(x: np.ndarray | float) -> np.ndarray | float:
    """Return sin(x)/x with the continuous value 1 at the origin."""

    return np.sinc(np.asarray(x) / np.pi)


def up_hat(t: np.ndarray, factors: int = 48) -> np.ndarray:
    """Truncated infinite product for the Fourier transform of Rvachev up.

    For the frequency ranges used below, 48 factors put the omitted logarithm
    far below double-precision roundoff.  The product is evaluated from coarse
    to fine scales so that the early factors suppress large frequencies before
    the near-one tail is multiplied in.
    """

    result = np.ones_like(t, dtype=np.float64)
    scale = 0.5
    for _ in range(factors):
        result *= sinc(t * scale)
        scale *= 0.5
    return result


def fft_inverse_characteristic(
    characteristic: np.ndarray,
    frequency_step: float,
) -> tuple[np.ndarray, np.ndarray]:
    """Invert an evenly sampled characteristic function.

    Frequencies are assumed to be centered and ordered as
    ``(-N/2, ..., N/2-1) * frequency_step``.  With

        f(x) = (2*pi)^(-1) integral exp(i t x) phi(t) dt,

    the returned spatial mesh has spacing ``2*pi/(N*frequency_step)``.
    """

    count = characteristic.size
    spatial_step = 2.0 * np.pi / (count * frequency_step)
    x = (np.arange(count) - count // 2) * spatial_step
    density = np.fft.fftshift(np.fft.ifft(np.fft.ifftshift(characteristic)))
    density *= count * frequency_step / (2.0 * np.pi)
    return x, density.real


def fixed_point_density(
    a: float,
    grid_size: int = 65_537,
    tolerance: float = 2.0e-14,
    max_iterations: int = 200,
) -> tuple[np.ndarray, np.ndarray, list[float]]:
    """Compute h_a by iterating its positive integral refinement operator.

    The operator is

        (T_a f)(x) = a/2 * integral_{a x - 1}^{a x + 1} f(u) du.

    A cumulative trapezoidal primitive turns each iteration into two linear
    interpolations.  Symmetrization and normalization only remove accumulated
    floating-point drift; they preserve the exact fixed point.
    """

    support_half_width = 1.0 / (a - 1.0)
    x = np.linspace(-support_half_width, support_half_width, grid_size)
    dx = x[1] - x[0]
    density = np.full_like(x, 1.0 / (2.0 * support_half_width))
    history: list[float] = []

    for _ in range(max_iterations):
        primitive = np.empty_like(density)
        primitive[0] = 0.0
        primitive[1:] = np.cumsum((density[:-1] + density[1:]) * (0.5 * dx))
        mass = primitive[-1]

        lower = a * x - 1.0
        upper = a * x + 1.0
        p_lower = np.interp(lower, x, primitive, left=0.0, right=mass)
        p_upper = np.interp(upper, x, primitive, left=0.0, right=mass)
        updated = 0.5 * a * (p_upper - p_lower)

        updated = 0.5 * (updated + updated[::-1])
        updated /= np.trapezoid(updated, x)
        error = float(np.max(np.abs(updated - density)))
        history.append(error)
        density = updated
        if error < tolerance:
            break

    return x, density, history


def experiment_h3() -> None:
    """Generate the smooth-Cantor-spline picture and fixed-point diagnostics."""

    a = 3.0
    x, density, history = fixed_point_density(a)
    b = 1.0 / (a - 1.0)
    b1 = (a - 2.0) / (a * (a - 1.0))

    mass = float(np.trapezoid(density, x))
    symmetry_error = float(np.max(np.abs(density - density[::-1])))
    plateau_mask = np.abs(x) <= b1 - 4.0 * (x[1] - x[0])
    plateau_error = float(np.max(np.abs(density[plateau_mask] - a / 2.0)))

    write_csv(
        DATA / "ha_a3_diagnostics.csv",
        ["quantity", "value"],
        [
            ("iterations", len(history)),
            ("final_fixed_point_sup_error", f"{history[-1]:.17e}"),
            ("mass", f"{mass:.17e}"),
            ("mass_error", f"{abs(mass - 1.0):.17e}"),
            ("reflection_sup_error", f"{symmetry_error:.17e}"),
            ("central_plateau_sup_error", f"{plateau_error:.17e}"),
            ("support_half_width", f"{b:.17e}"),
            ("central_gap_half_width", f"{b1:.17e}"),
        ],
    )

    fig, ax = plt.subplots(figsize=(9.0, 5.2))
    ax.plot(x, density, linewidth=1.4, label=r"fixed-point approximation to $h_3$")
    ax.axhline(a / 2.0, linewidth=0.8, linestyle="--", label=r"central plateau $3/2$")
    ax.axvline(-b1, linewidth=0.7, linestyle=":")
    ax.axvline(b1, linewidth=0.7, linestyle=":")
    ax.set_xlabel(r"$x$")
    ax.set_ylabel(r"$h_3(x)$")
    ax.set_xlim(-b, b)
    ax.set_title(r"The smooth Cantor spline $h_3$")
    ax.legend(loc="upper right")
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(FIGURES / "ha_a3_density.png", dpi=220)
    plt.close(fig)


def experiment_local_degree() -> tuple[float, float]:
    """Check the exact geometric law for the local polynomial degree."""

    a = 3.0
    success = 1.0 - 2.0 / a
    ratio = 2.0 / a
    sample_size = 400_000
    rng = np.random.default_rng(RNG_SEED)
    sample = rng.geometric(success, size=sample_size) - 1

    sample_mean = float(np.mean(sample))
    sample_variance = float(np.var(sample))
    max_degree = 22
    degrees = np.arange(max_degree + 1)
    exact = success * ratio**degrees
    observed = np.bincount(sample, minlength=max_degree + 1)[: max_degree + 1] / sample_size

    write_csv(
        DATA / "local_degree_distribution_a3.csv",
        ["degree", "exact_probability", "observed_probability", "sample_count"],
        [
            (
                int(n),
                f"{exact[n]:.17e}",
                f"{observed[n]:.17e}",
                int(np.count_nonzero(sample == n)),
            )
            for n in degrees
        ],
    )
    write_csv(
        DATA / "local_degree_summary_a3.csv",
        ["quantity", "exact", "observed"],
        [
            ("mean", 2.0, f"{sample_mean:.12f}"),
            ("variance", 6.0, f"{sample_variance:.12f}"),
            ("sample_size", sample_size, sample_size),
            ("seed", RNG_SEED, RNG_SEED),
        ],
    )

    fig, ax = plt.subplots(figsize=(8.6, 4.9))
    ax.bar(degrees - 0.18, exact, width=0.36, label="exact geometric law")
    ax.bar(degrees + 0.18, observed, width=0.36, label="deterministic Monte Carlo")
    ax.set_yscale("log")
    ax.set_xlabel("local polynomial degree")
    ax.set_ylabel("probability")
    ax.set_title(r"Local-degree distribution for $a=3$")
    ax.set_xticks(np.arange(0, max_degree + 1, 2))
    ax.grid(True, which="both", axis="y", alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(FIGURES / "local_degree_distribution.png", dpi=220)
    plt.close(fig)

    return sample_mean, sample_variance


def q_pochhammer(q: float, n: int) -> float:
    """Return (q;q)_n as a floating-point product."""

    result = 1.0
    for k in range(1, n + 1):
        result *= 1.0 - q**k
    return result


def gaussian_gram(q: float, order: int) -> np.ndarray:
    """Return [q^((i-j)^2)] for 0 <= i,j <= order."""

    indices = np.arange(order + 1, dtype=np.float64)
    return q ** ((indices[:, None] - indices[None, :]) ** 2)


def q_binomial_table(base: float, order: int) -> np.ndarray:
    """Build Gaussian binomial coefficients [n choose k]_base recursively."""

    table = np.zeros((order + 1, order + 1), dtype=np.float64)
    table[0, 0] = 1.0
    for n in range(1, order + 1):
        table[n, 0] = 1.0
        table[n, n] = 1.0
        for k in range(1, n):
            table[n, k] = table[n - 1, k - 1] + base**k * table[n - 1, k]
    return table


def theta_bounds(q: float, terms: int = 100) -> tuple[float, float]:
    """Compute theta_4(0,q) and theta_3(0,q) by their rapidly convergent sums."""

    k = np.arange(1, terms + 1, dtype=np.float64)
    powers = q ** (k * k)
    theta3 = 1.0 + 2.0 * float(np.sum(powers))
    theta4 = 1.0 + 2.0 * float(np.sum(((-1.0) ** k) * powers))
    return theta4, theta3


def experiment_gram_geometry() -> None:
    """Validate determinant, pivot, Riesz-bound, and q-binomial identities."""

    q = 1.0 / 3.0
    determinant_rows: list[tuple[object, ...]] = []
    previous_logdet = 0.0
    for order in range(0, 41):
        gram = gaussian_gram(q, order)
        sign, direct_logdet = np.linalg.slogdet(gram)
        product_logdet = sum(
            (order + 1 - d) * math.log1p(-(q ** (2 * d)))
            for d in range(1, order + 1)
        )
        direct_pivot = math.exp(direct_logdet - previous_logdet) if order else 1.0
        exact_pivot = q_pochhammer(q * q, order)
        determinant_rows.append(
            (
                order,
                int(sign),
                f"{direct_logdet:.17e}",
                f"{product_logdet:.17e}",
                f"{abs(direct_logdet - product_logdet):.17e}",
                f"{direct_pivot:.17e}",
                f"{exact_pivot:.17e}",
                f"{abs(direct_pivot - exact_pivot):.17e}",
            )
        )
        previous_logdet = direct_logdet

    write_csv(
        DATA / "gram_determinant_validation.csv",
        [
            "order_N",
            "determinant_sign",
            "direct_log_determinant",
            "product_log_determinant",
            "absolute_log_error",
            "direct_pivot",
            "q_pochhammer_pivot",
            "absolute_pivot_error",
        ],
        determinant_rows,
    )

    lower, upper = theta_bounds(q)
    write_csv(
        DATA / "gram_symbol_bounds.csv",
        ["quantity", "value"],
        [
            ("q", q),
            ("theta4_0_q", f"{lower:.17e}"),
            ("theta3_0_q", f"{upper:.17e}"),
        ],
    )

    fig, ax = plt.subplots(figsize=(9.1, 5.2))
    for order in (8, 16, 32, 64):
        eigenvalues = np.linalg.eigvalsh(gaussian_gram(q, order))
        ax.plot(np.arange(order + 1) / order, eigenvalues, marker=".", linewidth=0.8,
                label=fr"$N={order}$")
    ax.axhline(lower, linestyle="--", linewidth=1.0, label=r"$\vartheta_4(0,q)$")
    ax.axhline(upper, linestyle="--", linewidth=1.0, label=r"$\vartheta_3(0,q)$")
    ax.set_xlabel("normalized eigenvalue index")
    ax.set_ylabel("Gram eigenvalue")
    ax.set_title(r"Finite $q$-Gaussian derivative Gram spectra, $q=1/3$")
    ax.grid(True, alpha=0.25)
    ax.legend(ncol=3)
    fig.tight_layout()
    fig.savefig(FIGURES / "derivative_gram_spectrum.png", dpi=220)
    plt.close(fig)

    # Explicit q-binomial/Rogers--Szego Gram--Schmidt filters.
    max_order = 24
    q2 = q * q
    qbinom = q_binomial_table(q2, max_order)
    coefficient_matrix = np.zeros((max_order + 1, max_order + 1))
    validation_rows: list[tuple[object, ...]] = []

    for n in range(max_order + 1):
        coeff = np.array(
            [((-1.0) ** (n - k)) * (q ** (n - k)) * qbinom[n, k] for k in range(n + 1)]
        )
        coefficient_matrix[n, : n + 1] = coeff
        gram = gaussian_gram(q, n)
        previous_inner_products = coeff @ gram[:, :n] if n else np.zeros(0)
        orthogonality_error = (
            float(np.max(np.abs(previous_inner_products))) if previous_inner_products.size else 0.0
        )
        norm_squared = float(coeff @ gram @ coeff)
        exact_norm_squared = q_pochhammer(q2, n)

        # The inverse triangular formula eta_n = sum q^((n-k)^2)[n k] r_k.
        r_matrix = np.zeros((n + 1, n + 1))
        inverse_matrix = np.zeros((n + 1, n + 1))
        for row in range(n + 1):
            for col in range(row + 1):
                r_matrix[row, col] = (
                    ((-1.0) ** (row - col)) * q ** (row - col) * qbinom[row, col]
                )
                inverse_matrix[row, col] = q ** ((row - col) ** 2) * qbinom[row, col]
        inversion_error = float(np.max(np.abs(inverse_matrix @ r_matrix - np.eye(n + 1))))

        validation_rows.append(
            (
                n,
                f"{orthogonality_error:.17e}",
                f"{norm_squared:.17e}",
                f"{exact_norm_squared:.17e}",
                f"{abs(norm_squared - exact_norm_squared):.17e}",
                f"{inversion_error:.17e}",
            )
        )

    write_csv(
        DATA / "q_binomial_orthogonalization.csv",
        [
            "order_n",
            "max_previous_inner_product",
            "computed_residual_norm_squared",
            "q_pochhammer_norm_squared",
            "absolute_norm_error",
            "triangular_inversion_sup_error",
        ],
        validation_rows,
    )

    # Heat map of the exact lower-triangular filter coefficients.  Values below
    # 10^-16 are clipped only for plotting; CSV validation uses the raw values.
    fig, ax = plt.subplots(figsize=(8.4, 6.4))
    image_data = np.full_like(coefficient_matrix, np.nan)
    mask = np.tri(max_order + 1, dtype=bool)
    image_data[mask] = np.log10(np.maximum(np.abs(coefficient_matrix[mask]), 1.0e-16))
    image = ax.imshow(image_data, origin="lower", aspect="auto")
    ax.set_xlabel(r"input index $k$")
    ax.set_ylabel(r"orthogonalized order $n$")
    ax.set_title(r"$\log_{10}$ magnitude of the Rogers--Szegő derivative filters")
    fig.colorbar(image, ax=ax, label=r"$\log_{10}|c_{n,k}|$")
    fig.tight_layout()
    fig.savefig(FIGURES / "q_binomial_orthogonalization.png", dpi=220)
    plt.close(fig)


def complete_homogeneous(values: Sequence[float], max_degree: int) -> np.ndarray:
    """Return h_0,...,h_max for the supplied variables.

    The update implements multiplication by (1-x*t)^(-1), avoiding symbolic
    algebra while retaining the Jacobi--Trudi definition of Schur polynomials.
    """

    h = np.zeros(max_degree + 1, dtype=np.float64)
    h[0] = 1.0
    for x in values:
        updated = np.zeros_like(h)
        updated[0] = h[0]
        for degree in range(1, max_degree + 1):
            updated[degree] = h[degree] + x * updated[degree - 1]
        h = updated
    return h


def schur_polynomial(partition: Sequence[int], values: Sequence[float]) -> float:
    """Evaluate a Schur polynomial by the Jacobi--Trudi determinant."""

    n = len(partition)
    max_index = max(partition[i] - i + (n - 1) for i in range(n))
    h = complete_homogeneous(values, max_index)
    matrix = np.empty((n, n), dtype=np.float64)
    for i in range(n):
        for j in range(n):
            index = partition[i] - i + j
            matrix[i, j] = 0.0 if index < 0 else h[index]
    return float(np.linalg.det(matrix))


def experiment_total_positivity() -> None:
    """Check Schur--Vandermonde formulae for nonconsecutive Gram minors."""

    q = 1.0 / 3.0
    # Moderate index sets keep the two independently evaluated determinant
    # formulae well conditioned in ordinary double precision.
    examples = [
        ((0, 1, 2), (0, 1, 3)),
        ((0, 1, 3), (0, 2, 4)),
        ((0, 2, 4), (1, 2, 5)),
        ((0, 1, 3, 4), (0, 2, 3, 5)),
    ]
    rows_out: list[tuple[object, ...]] = []

    for row_indices, column_indices in examples:
        row = np.array(row_indices, dtype=np.float64)
        column = np.array(column_indices, dtype=np.float64)
        kernel = q ** ((row[:, None] - column[None, :]) ** 2)
        direct = float(np.linalg.det(kernel))

        x = q ** (-2.0 * row)
        vandermonde = 1.0
        for i in range(len(x)):
            for j in range(i + 1, len(x)):
                vandermonde *= x[j] - x[i]
        n = len(column_indices)
        partition = tuple(column_indices[n - 1 - i] - (n - 1 - i) for i in range(n))
        schur = schur_polynomial(partition, x)
        factored = q ** (float(np.sum(row * row) + np.sum(column * column)))
        factored *= vandermonde * schur

        rows_out.append(
            (
                " ".join(map(str, row_indices)),
                " ".join(map(str, column_indices)),
                " ".join(map(str, partition)),
                f"{direct:.17e}",
                f"{factored:.17e}",
                f"{abs(direct - factored):.17e}",
                f"{abs(direct - factored) / abs(direct):.17e}",
                direct > 0.0,
            )
        )

    write_csv(
        DATA / "schur_minor_validation.csv",
        [
            "row_indices",
            "column_indices",
            "partition_lambda",
            "direct_minor",
            "schur_vandermonde_minor",
            "absolute_error",
            "relative_error",
            "strictly_positive",
        ],
        rows_out,
    )


def probabilists_hermite(order: int, x: np.ndarray) -> np.ndarray:
    """Evaluate the probabilists' Hermite polynomial H_order(x)."""

    if order == 0:
        return np.ones_like(x)
    if order == 1:
        return x.copy()
    h_prev = np.ones_like(x)
    h_curr = x.copy()
    for n in range(1, order):
        h_next = x * h_curr - n * h_prev
        h_prev, h_curr = h_curr, h_next
    return h_curr


def standardized_fup_density(
    n: int,
    fft_size: int = 65_536,
    frequency_step: float = 0.03,
) -> tuple[np.ndarray, np.ndarray]:
    """Compute the standardized Fup_n density by deterministic FFT inversion."""

    t = (np.arange(fft_size) - fft_size // 2) * frequency_step
    variance = (3.0 * n + 4.0) / 9.0
    standard_deviation = math.sqrt(variance)
    characteristic = up_hat(2.0 * t / standard_deviation)
    characteristic *= sinc(t / standard_deviation) ** n
    return fft_inverse_characteristic(characteristic, frequency_step)


def standardized_cumulants(n: int) -> tuple[float, float]:
    """Return exact lambda_4,n and lambda_6,n from the report."""

    lambda4 = -18.0 * (15.0 * n + 16.0) / (25.0 * (3.0 * n + 4.0) ** 2)
    lambda6 = 144.0 * (63.0 * n + 64.0) / (49.0 * (3.0 * n + 4.0) ** 3)
    return lambda4, lambda6


def edgeworth_approximants(n: int, x: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Gaussian, first-order, and second-order exact-cumulant approximants."""

    gaussian = np.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)
    lambda4, lambda6 = standardized_cumulants(n)
    first = gaussian * (1.0 + lambda4 * probabilists_hermite(4, x) / 24.0)
    second = gaussian * (
        1.0
        + lambda4 * probabilists_hermite(4, x) / 24.0
        + lambda6 * probabilists_hermite(6, x) / 720.0
        + lambda4 * lambda4 * probabilists_hermite(8, x) / 1152.0
    )
    return gaussian, first, second


def experiment_fup() -> None:
    """Generate the CLT and Edgeworth figures and error tables."""

    clt_orders = (1, 4, 16, 64)
    fig, ax = plt.subplots(figsize=(9.0, 5.2))
    for n in clt_orders:
        x, density = standardized_fup_density(n)
        mask = np.abs(x) <= 5.0
        ax.plot(x[mask], density[mask], linewidth=1.1, label=fr"$n={n}$")
    x_reference = np.linspace(-5.0, 5.0, 2001)
    gaussian_reference = np.exp(-0.5 * x_reference**2) / math.sqrt(2.0 * math.pi)
    ax.plot(x_reference, gaussian_reference, linestyle="--", linewidth=1.5,
            label="standard Gaussian")
    ax.set_xlabel(r"standardized coordinate $x$")
    ax.set_ylabel("density")
    ax.set_title(r"Gaussian scaling limit of the $\operatorname{Fup}_n$ hierarchy")
    ax.grid(True, alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(FIGURES / "fup_clt.png", dpi=220)
    plt.close(fig)

    orders = (8, 12, 16, 24, 32, 48, 64, 96, 128)
    error_rows: list[tuple[object, ...]] = []
    errors0: list[float] = []
    errors1: list[float] = []
    errors2: list[float] = []

    for n in orders:
        x, density = standardized_fup_density(n)
        gaussian, first, second = edgeworth_approximants(n, x)
        error0 = float(np.max(np.abs(density - gaussian)))
        error1 = float(np.max(np.abs(density - first)))
        error2 = float(np.max(np.abs(density - second)))
        errors0.append(error0)
        errors1.append(error1)
        errors2.append(error2)
        lambda4, lambda6 = standardized_cumulants(n)
        error_rows.append(
            (
                n,
                f"{lambda4:.17e}",
                f"{lambda6:.17e}",
                f"{error0:.17e}",
                f"{error1:.17e}",
                f"{error2:.17e}",
                f"{n * error0:.17e}",
                f"{n * n * error1:.17e}",
                f"{n * n * n * error2:.17e}",
            )
        )

    write_csv(
        DATA / "fup_edgeworth_validation.csv",
        [
            "n",
            "lambda4",
            "lambda6",
            "gaussian_sup_error",
            "first_order_sup_error",
            "second_order_sup_error",
            "n_times_gaussian_error",
            "n2_times_first_order_error",
            "n3_times_second_order_error",
        ],
        error_rows,
    )

    fig, ax = plt.subplots(figsize=(9.0, 5.2))
    orders_array = np.asarray(orders, dtype=np.float64)
    ax.loglog(orders_array, errors0, marker="o", label="Gaussian")
    ax.loglog(orders_array, errors1, marker="o", label=r"$H_4$ correction")
    ax.loglog(orders_array, errors2, marker="o", label=r"$H_4,H_6,H_8$ correction")

    # Reference slopes are normalized at the final computed point, so only the
    # power law, not an arbitrary vertical constant, is being compared.
    ax.loglog(orders_array, errors0[-1] * (orders_array[-1] / orders_array),
              linestyle=":", label=r"slope $n^{-1}$")
    ax.loglog(orders_array, errors1[-1] * (orders_array[-1] / orders_array) ** 2,
              linestyle=":", label=r"slope $n^{-2}$")
    ax.loglog(orders_array, errors2[-1] * (orders_array[-1] / orders_array) ** 3,
              linestyle=":", label=r"slope $n^{-3}$")
    ax.set_xlabel(r"hierarchy level $n$")
    ax.set_ylabel("uniform density error")
    ax.set_title(r"Exact-cumulant Edgeworth error scales for $\operatorname{Fup}_n$")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(ncol=2)
    fig.tight_layout()
    fig.savefig(FIGURES / "fup_edgeworth_error.png", dpi=220)
    plt.close(fig)


def log_leading_amplitude(a: float, n: int) -> float:
    """Return log L_n without overflow, using lgamma(n+1)=log(n!)."""

    return 0.5 * (n + 1) * (n + 2) * math.log(a) - (n + 1) * math.log(2.0) - math.lgamma(n + 1)


def experiment_jet_tail() -> None:
    """Check the two-term log-Weibull tail and its critical Orlicz exponent."""

    a = 3.0
    log_a = math.log(a)
    decay = math.log(a / 2.0)
    gamma = decay * math.sqrt(2.0 / log_a)
    beta = decay / (2.0 * log_a)

    rows: list[tuple[object, ...]] = []
    x_values: list[float] = []
    residuals: list[float] = []
    predictions: list[float] = []

    # Choose logarithmic midpoints between consecutive staircase levels.  For
    # L_n < x < L_{n+1}, P(A>x)=(2/a)^(n+1).
    for n in range(4, 121):
        log_x = 0.5 * (log_leading_amplitude(a, n) + log_leading_amplitude(a, n + 1))
        minus_log_tail = (n + 1) * decay
        leading = gamma * math.sqrt(log_x)
        loglog_term = beta * math.log(log_x)
        bounded_remainder = minus_log_tail - leading - loglog_term
        x_values.append(math.sqrt(log_x))
        residuals.append(minus_log_tail - leading)
        predictions.append(loglog_term)
        rows.append(
            (
                n,
                f"{log_x:.17e}",
                f"{-minus_log_tail:.17e}",
                f"{leading:.17e}",
                f"{loglog_term:.17e}",
                f"{bounded_remainder:.17e}",
            )
        )

    # Partial exponential moments below, at, and above the critical exponent.
    moment_rows: list[tuple[object, ...]] = []
    for theta_ratio in (0.9, 1.0, 1.1):
        theta = theta_ratio * gamma
        partial = 0.0
        for n in range(0, 501):
            log_term = math.log(1.0 - 2.0 / a) + n * math.log(2.0 / a)
            log_term += theta * math.sqrt(log_leading_amplitude(a, n))
            term = math.exp(log_term) if log_term < 700.0 else math.inf
            partial += term
            if n in (20, 50, 100, 200, 500):
                moment_rows.append((theta_ratio, n, f"{partial:.17e}", f"{log_term:.17e}"))
            if not math.isfinite(partial):
                break

    write_csv(
        DATA / "jet_tail_refinement_a3.csv",
        [
            "step_n",
            "log_x_midpoint",
            "log_tail_probability",
            "leading_gamma_sqrt_log_x",
            "loglog_correction",
            "bounded_remainder",
        ],
        rows,
    )
    write_csv(
        DATA / "jet_orlicz_partial_sums_a3.csv",
        ["theta_over_critical", "cutoff_n", "partial_expectation", "last_log_summand"],
        moment_rows,
    )

    fig, ax = plt.subplots(figsize=(9.0, 5.1))
    ax.plot(x_values, residuals, linewidth=1.25,
            label=r"$-\log\mathrm{P}(A>x)-\gamma\sqrt{\log x}$")
    ax.plot(x_values, predictions, linestyle="--", linewidth=1.25,
            label=r"$\frac{\log(a/2)}{2\log a}\log\log x$")
    ax.set_xlabel(r"$\sqrt{\log x}$ (midpoints between staircase levels)")
    ax.set_ylabel("subleading tail term")
    ax.set_title(r"The logarithmic correction to jet intermittency, $a=3$")
    ax.grid(True, alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(FIGURES / "jet_tail_refinement.png", dpi=220)
    plt.close(fig)


def main() -> None:
    """Run all deterministic experiments."""

    experiment_h3()
    mean, variance = experiment_local_degree()
    experiment_gram_geometry()
    experiment_total_positivity()
    experiment_fup()
    experiment_jet_tail()

    print("Generated figures in", FIGURES)
    print("Generated diagnostics in", DATA)
    print(f"Local-degree sample mean={mean:.9f}, variance={variance:.9f}")


if __name__ == "__main__":
    main()
