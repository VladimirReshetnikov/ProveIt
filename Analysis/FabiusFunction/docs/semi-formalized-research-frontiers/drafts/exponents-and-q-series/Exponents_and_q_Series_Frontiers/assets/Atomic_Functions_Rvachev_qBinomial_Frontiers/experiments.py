#!/usr/bin/env python3
"""Deterministic numerical experiments for the Rvachev atomic-functions report.

The script has two purposes.

1. Reproduce the report's illustrative figures for h_3, the local polynomial
   degree law, the q-Gaussian derivative Gram spectrum, and the Fup_n central
   limit/Edgeworth regimes.
2. Independently validate the new current-head formulae:
      * q-binomial Gram--Schmidt and exact Cholesky/inverse transforms;
      * arbitrary Gaussian-kernel minors and strict total positivity;
      * the theta spectral factor / limiting innovation filter;
      * the partial-theta Mellin transform of the highest local jet and its
        joint transform with distance to the Cantor knot set.

NumPy, Matplotlib, and mpmath are required.  All random experiments use fixed
seeds.  The mathematical identities are exact; floating-point calculations
are validation and visualization, not substitutes for the proofs.
"""

from __future__ import annotations

import csv
import math
from itertools import combinations
from pathlib import Path
from typing import Iterable

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parent
FIGURES = ROOT / "figures"
DATA = ROOT / "data"
FIGURES.mkdir(exist_ok=True)
DATA.mkdir(exist_ok=True)


def sinc(x: np.ndarray | float) -> np.ndarray | float:
    """sin(x)/x, evaluated stably via NumPy's normalized sinc."""

    return np.sinc(np.asarray(x) / np.pi)


def q_pochhammer(Q: float, n: int) -> float:
    """Finite q-Pochhammer (Q;Q)_n."""

    value = 1.0
    for j in range(1, n + 1):
        value *= 1.0 - Q**j
    return value


def q_pochhammer_inf(Q: float, tolerance: float = 1.0e-16) -> float:
    """Infinite q-Pochhammer (Q;Q)_infty by a rigorously monotone truncation."""

    value = 1.0
    j = 1
    while Q**j > tolerance:
        value *= 1.0 - Q**j
        j += 1
    return value


def gaussian_q_binomial(n: int, k: int, Q: float) -> float:
    """Gaussian binomial coefficient [n choose k]_Q.

    The multiplicative form is stable for the small and medium orders used in
    the validation tables.  Symmetry k <-> n-k keeps the product short.
    """

    if k < 0 or k > n:
        return 0.0
    k = min(k, n - k)
    value = 1.0
    for r in range(1, k + 1):
        value *= (1.0 - Q ** (n - k + r)) / (1.0 - Q**r)
    return value


def gram_matrix(q: float, N: int) -> np.ndarray:
    """G_N(q) = [q^((i-j)^2)]_{0<=i,j<=N}."""

    indices = np.arange(N + 1, dtype=float)
    return q ** ((indices[:, None] - indices[None, :]) ** 2)


def residual_matrix(q: float, N: int) -> np.ndarray:
    """Lower triangular q-binomial Gram--Schmidt matrix C_N.

    r_n = sum_k C[n,k] eta_k, with
      C[n,k] = (-1)^(n-k) q^(n-k) [n choose k]_{q^2}.
    """

    Q = q * q
    C = np.zeros((N + 1, N + 1), dtype=float)
    for n in range(N + 1):
        for k in range(n + 1):
            C[n, k] = ((-1.0) ** (n - k)) * q ** (n - k) * gaussian_q_binomial(n, k, Q)
    return C


def inverse_residual_matrix(q: float, N: int) -> np.ndarray:
    """Exact inverse B_N of C_N.

    eta_n = sum_k B[n,k] r_k, with
      B[n,k] = q^((n-k)^2) [n choose k]_{q^2}.
    """

    Q = q * q
    B = np.zeros((N + 1, N + 1), dtype=float)
    for n in range(N + 1):
        for k in range(n + 1):
            B[n, k] = q ** ((n - k) ** 2) * gaussian_q_binomial(n, k, Q)
    return B


def theta_symbol(q: float, theta: np.ndarray, terms: int = 200) -> np.ndarray:
    """Theta_q(theta) = sum_{k in Z} q^(k^2) exp(i k theta)."""

    result = np.ones_like(theta, dtype=float)
    for k in range(1, terms + 1):
        term = q ** (k * k)
        if term < 1.0e-18:
            break
        result += 2.0 * term * np.cos(k * theta)
    return result


def up_hat(t: np.ndarray, factors: int = 64) -> np.ndarray:
    """Fourier transform of Rvachev's up function."""

    result = np.ones_like(t, dtype=float)
    scale = 0.5
    for _ in range(factors):
        result *= sinc(t * scale)
        scale *= 0.5
    return result


def cosine_inversion(
    characteristic: np.ndarray,
    frequencies: np.ndarray,
    x_values: np.ndarray,
    chunk_size: int = 80,
) -> np.ndarray:
    """Invert an even real characteristic function by cosine quadrature."""

    density = np.empty_like(x_values, dtype=float)
    for start in range(0, len(x_values), chunk_size):
        stop = min(start + chunk_size, len(x_values))
        cosine = np.cos(np.outer(x_values[start:stop], frequencies))
        density[start:stop] = np.trapezoid(cosine * characteristic[None, :], frequencies, axis=1) / np.pi
    return density


def fup_standardized_density(n: int, x_values: np.ndarray, T: float = 220.0, dt: float = 0.0125) -> np.ndarray:
    """Density of W_n=(2X+U_1+...+U_n)/s_n by exact CF inversion."""

    frequencies = np.arange(0.0, T + 0.5 * dt, dt)
    s_n = math.sqrt((3.0 * n + 4.0) / 9.0)
    characteristic = up_hat(2.0 * frequencies / s_n) * sinc(frequencies / s_n) ** n
    return cosine_inversion(characteristic, frequencies, x_values)


def hermite_probabilists(n: int, x: np.ndarray) -> np.ndarray:
    """Probabilists' Hermite polynomial H_n."""

    if n == 0:
        return np.ones_like(x)
    if n == 1:
        return x.copy()
    h0 = np.ones_like(x)
    h1 = x.copy()
    for k in range(1, n):
        h0, h1 = h1, x * h1 - k * h0
    return h1


def normal_density(x: np.ndarray) -> np.ndarray:
    return np.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)


def lambda4(n: int) -> float:
    return -18.0 * (15.0 * n + 16.0) / (25.0 * (3.0 * n + 4.0) ** 2)


def lambda6(n: int) -> float:
    return 144.0 * (63.0 * n + 64.0) / (49.0 * (3.0 * n + 4.0) ** 3)


def edgeworth_approximants(n: int, x: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    phi = normal_density(x)
    l4 = lambda4(n)
    l6 = lambda6(n)
    order0 = phi
    order1 = phi * (1.0 + l4 * hermite_probabilists(4, x) / 24.0)
    order2 = phi * (
        1.0
        + l4 * hermite_probabilists(4, x) / 24.0
        + l6 * hermite_probabilists(6, x) / 720.0
        + l4 * l4 * hermite_probabilists(8, x) / 1152.0
    )
    return order0, order1, order2


def fixed_point_density(a: float, points: int = 30001, iterations: int = 80) -> tuple[np.ndarray, np.ndarray]:
    """Iterate h(x)=(a/2) integral_{ax-1}^{ax+1} h(u)du."""

    b = 1.0 / (a - 1.0)
    x = np.linspace(-b, b, points)
    h = np.full(points, 1.0 / (2.0 * b), dtype=float)
    dx = x[1] - x[0]
    for _ in range(iterations):
        primitive = np.empty(points, dtype=float)
        primitive[0] = 0.0
        primitive[1:] = np.cumsum((h[:-1] + h[1:]) * (0.5 * dx))
        lo = np.clip(a * x - 1.0, -b, b)
        hi = np.clip(a * x + 1.0, -b, b)
        integral = np.interp(hi, x, primitive) - np.interp(lo, x, primitive)
        h_new = 0.5 * a * integral
        mass = np.trapezoid(h_new, x)
        h = h_new / mass
    return x, h


def write_csv(path: Path, header: Iterable[str], rows: Iterable[Iterable[object]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(list(header))
        writer.writerows(rows)


def experiment_h3() -> None:
    a = 3.0
    b = 1.0 / (a - 1.0)
    b1 = (a - 2.0) / (a * (a - 1.0))
    x, h = fixed_point_density(a)
    mass = float(np.trapezoid(h, x))
    symmetry = float(np.max(np.abs(h - h[::-1])))
    plateau = np.abs(x) <= b1 - 3.0 * (x[1] - x[0])
    plateau_error = float(np.max(np.abs(h[plateau] - a / 2.0)))
    write_csv(
        DATA / "ha_a3_diagnostics.csv",
        ["quantity", "computed", "exact_or_target", "absolute_error"],
        [
            ("mass", mass, 1.0, abs(mass - 1.0)),
            ("reflection_symmetry", symmetry, 0.0, symmetry),
            ("central_plateau", float(np.mean(h[plateau])), a / 2.0, plateau_error),
            ("support_half_width", b, b, 0.0),
        ],
    )
    plt.figure(figsize=(8.8, 4.8))
    plt.plot(x, h, linewidth=1.6)
    plt.axvline(-b1, linewidth=0.8, linestyle="--")
    plt.axvline(b1, linewidth=0.8, linestyle="--")
    plt.xlabel("x")
    plt.ylabel(r"$h_3(x)$")
    plt.title(r"Fixed-point approximation to the smooth Cantor spline $h_3$")
    plt.tight_layout()
    plt.savefig(FIGURES / "ha_a3_density.png", dpi=200)
    plt.close()


def experiment_local_degree() -> None:
    a = 3.0
    p = 1.0 - 2.0 / a
    r = 2.0 / a
    n_max = 14
    n = np.arange(n_max + 1)
    exact = p * r**n
    rng = np.random.default_rng(20260828)
    samples = rng.geometric(p, size=400_000) - 1
    observed = np.array([(samples == k).mean() for k in n])
    write_csv(
        DATA / "local_degree_distribution_a3.csv",
        ["degree", "exact_probability", "sample_probability"],
        zip(n, exact, observed),
    )
    width = 0.4
    plt.figure(figsize=(8.4, 4.8))
    plt.bar(n - width / 2.0, exact, width=width, label="exact")
    plt.bar(n + width / 2.0, observed, width=width, label="deterministic Monte Carlo")
    plt.yscale("log")
    plt.xlabel("local polynomial degree")
    plt.ylabel("probability")
    plt.title(r"Geometric local-degree law for $a=3$")
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIGURES / "local_degree_distribution.png", dpi=200)
    plt.close()


def experiment_fup_clt() -> None:
    x = np.linspace(-4.5, 4.5, 721)
    plt.figure(figsize=(8.8, 5.0))
    for n in (1, 4, 16, 64):
        density = fup_standardized_density(n, x)
        plt.plot(x, density, linewidth=1.1, label=fr"$n={n}$")
    plt.plot(x, normal_density(x), linewidth=1.8, linestyle="--", label="standard Gaussian")
    plt.xlabel("standardized coordinate")
    plt.ylabel("density")
    plt.title(r"Standardized $\mathrm{Fup}_n$ densities")
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIGURES / "fup_clt.png", dpi=200)
    plt.close()


def experiment_gram_spectrum() -> None:
    q = 1.0 / 3.0
    theta = np.linspace(-math.pi, math.pi, 20001)
    symbol = theta_symbol(q, theta)
    lower = float(symbol.min())
    upper = float(symbol.max())
    rows = []
    plt.figure(figsize=(8.8, 5.0))
    for N in (4, 8, 16, 32):
        eigenvalues = np.linalg.eigvalsh(gram_matrix(q, N))
        rows.append((N, float(eigenvalues.min()), float(eigenvalues.max()), lower, upper))
        plt.plot(np.arange(N + 1), eigenvalues, marker="o", markersize=2.5, linewidth=0.8, label=fr"$N={N}$")
    plt.axhline(lower, linestyle="--", linewidth=1.1, label=r"$\vartheta_4(0,q)$")
    plt.axhline(upper, linestyle="--", linewidth=1.1, label=r"$\vartheta_3(0,q)$")
    plt.xlabel("ordered eigenvalue index")
    plt.ylabel("eigenvalue")
    plt.title(r"Finite $q$-Gaussian Gram spectra, $q=1/3$")
    plt.legend(ncol=2)
    plt.tight_layout()
    plt.savefig(FIGURES / "derivative_gram_spectrum.png", dpi=200)
    plt.close()
    write_csv(
        DATA / "gram_symbol_bounds.csv",
        ["N", "minimum_eigenvalue", "maximum_eigenvalue", "theta_lower", "theta_upper"],
        rows,
    )


def experiment_edgeworth() -> None:
    x = np.linspace(-5.0, 5.0, 601)
    ns = np.array([8, 16, 32, 64, 128])
    errors = []
    for n in ns:
        density = fup_standardized_density(int(n), x, T=180.0, dt=0.01)
        approximants = edgeworth_approximants(int(n), x)
        errors.append([float(np.max(np.abs(density - approximation))) for approximation in approximants])
    errors_array = np.asarray(errors)
    write_csv(
        DATA / "fup_edgeworth_validation.csv",
        ["n", "gaussian_error", "first_order_error", "second_order_error"],
        ((int(n), *errors_array[i]) for i, n in enumerate(ns)),
    )
    plt.figure(figsize=(8.6, 5.0))
    plt.loglog(ns, errors_array[:, 0], marker="o", label="Gaussian")
    plt.loglog(ns, errors_array[:, 1], marker="o", label=r"through $H_4$")
    plt.loglog(ns, errors_array[:, 2], marker="o", label=r"through $H_8$")
    # Reference slopes are normalized at the first point; they are visual guides only.
    plt.loglog(ns, errors_array[0, 0] * (ns[0] / ns), linestyle="--", linewidth=0.8, label=r"$n^{-1}$ guide")
    plt.loglog(ns, errors_array[0, 1] * (ns[0] / ns) ** 2, linestyle="--", linewidth=0.8, label=r"$n^{-2}$ guide")
    plt.loglog(ns, errors_array[0, 2] * (ns[0] / ns) ** 3, linestyle="--", linewidth=0.8, label=r"$n^{-3}$ guide")
    plt.xlabel("n")
    plt.ylabel("uniform error on [-5,5]")
    plt.title(r"Exact-cumulant Edgeworth errors for standardized $\mathrm{Fup}_n$")
    plt.legend(ncol=2)
    plt.tight_layout()
    plt.savefig(FIGURES / "fup_edgeworth_error.png", dpi=200)
    plt.close()


def experiment_q_binomial_factorization() -> None:
    q = 0.48
    Q = q * q
    N = 36
    G = gram_matrix(q, N)
    C = residual_matrix(q, N)
    B = inverse_residual_matrix(q, N)
    D = np.diag([q_pochhammer(Q, n) for n in range(N + 1)])
    diagonalization_error = float(np.max(np.abs(C @ G @ C.T - D)))
    inversion_error = float(max(np.max(np.abs(C @ B - np.eye(N + 1))), np.max(np.abs(B @ C - np.eye(N + 1)))))
    cholesky_error = float(np.max(np.abs(G - B @ D @ B.T)))
    inverse_formula_error = float(np.max(np.abs(np.linalg.inv(G) - C.T @ np.diag(1.0 / np.diag(D)) @ C)))

    determinant_rows = []
    for n in range(1, N + 1):
        sign, logdet_direct = np.linalg.slogdet(G[: n + 1, : n + 1])
        logdet_product = sum(math.log(q_pochhammer(Q, r)) for r in range(1, n + 1))
        determinant_rows.append((n, sign, logdet_direct, logdet_product, logdet_direct - logdet_product))
    write_csv(
        DATA / "q_binomial_factorization_validation.csv",
        ["N", "diagonalization_max_error", "inverse_transform_max_error", "cholesky_max_error", "inverse_formula_max_error"],
        [(N, diagonalization_error, inversion_error, cholesky_error, inverse_formula_error)],
    )
    write_csv(
        DATA / "gram_determinant_validation.csv",
        ["N", "sign", "direct_logdet", "product_logdet", "difference"],
        determinant_rows,
    )

    # Plot finite prediction coefficients by lag and their limiting filter.
    max_lag = 16
    lag = np.arange(max_lag + 1)
    limit = np.array([((-1.0) ** r) * q**r / q_pochhammer(Q, int(r)) for r in lag])
    plt.figure(figsize=(8.8, 5.0))
    for n in (2, 4, 8, 16):
        finite = np.zeros(max_lag + 1)
        for r in range(min(n, max_lag) + 1):
            finite[r] = ((-1.0) ** r) * q**r * gaussian_q_binomial(n, r, Q)
        plt.plot(lag, finite, marker="o", markersize=3, linewidth=0.9, label=fr"finite $n={n}$")
    plt.plot(lag, limit, marker="s", markersize=3.5, linewidth=1.7, linestyle="--", label="limiting theta-whitening filter")
    plt.axhline(0.0, linewidth=0.6)
    plt.xlabel("lag r")
    plt.ylabel("coefficient")
    plt.title(r"$q$-binomial Gram--Schmidt filters, $q=0.48$")
    plt.legend(ncol=2)
    plt.tight_layout()
    plt.savefig(FIGURES / "q_binomial_filters.png", dpi=200)
    plt.close()

    # Validate the exact spectral factor identity on the unit circle.
    theta = np.linspace(-math.pi, math.pi, 4001)
    z = np.exp(1j * theta)
    A = np.zeros_like(z, dtype=complex)
    for r in range(120):
        term = ((-1.0) ** r) * q**r / q_pochhammer(Q, r)
        A += term * z**r
        if abs(term) < 1.0e-17:
            break
    whitened = np.abs(A) ** 2 * theta_symbol(q, theta)
    target = q_pochhammer_inf(Q)
    write_csv(
        DATA / "theta_whitening_validation.csv",
        ["q", "target_(q2;q2)_infinity", "minimum_product", "maximum_product", "max_absolute_error"],
        [(q, target, float(whitened.min()), float(whitened.max()), float(np.max(np.abs(whitened - target))))],
    )


def experiment_total_positivity() -> None:
    """Validate arbitrary minors with high-precision arithmetic.

    The two determinants are evaluated independently: directly from the
    Gaussian kernel and from the diagonal-times-generalized-Vandermonde
    factorization.  High precision is essential because perfectly positive
    minors can be far below binary64 range.
    """

    q = mp.mpf("0.55")
    mp.mp.dps = 90
    rng = np.random.default_rng(314159265)
    rows = []
    log_values: dict[int, list[float]] = {m: [] for m in range(1, 6)}
    for order in range(1, 6):
        for _ in range(250):
            I = tuple(sorted(rng.choice(14, size=order, replace=False).tolist()))
            J = tuple(sorted(rng.choice(14, size=order, replace=False).tolist()))
            direct_matrix = mp.matrix([[q ** ((i - j) ** 2) for j in J] for i in I])
            direct = mp.det(direct_matrix)

            x = [q ** (-2 * i) for i in I]
            generalized_vandermonde = mp.matrix([[xx**j for j in J] for xx in x])
            diagonal = q ** (sum(i * i for i in I) + sum(j * j for j in J))
            factorized = diagonal * mp.det(generalized_vandermonde)
            relative = abs(direct - factorized) / abs(factorized)
            rows.append(
                (
                    order,
                    " ".join(map(str, I)),
                    " ".join(map(str, J)),
                    mp.nstr(direct, 30),
                    mp.nstr(factorized, 30),
                    mp.nstr(relative, 8),
                )
            )
            log_values[order].append(float(mp.log10(factorized)))
    write_csv(
        DATA / "strict_total_positivity_validation.csv",
        ["order", "row_indices", "column_indices", "direct_minor", "schur_factorized_minor", "relative_error"],
        rows,
    )
    plt.figure(figsize=(8.6, 5.0))
    positions = []
    values = []
    for order in range(1, 6):
        positions.extend([order] * len(log_values[order]))
        values.extend(log_values[order])
    plt.scatter(positions, values, s=7, alpha=0.45)
    plt.xlabel("minor order")
    plt.ylabel(r"$\log_{10}$ of positive minor")
    plt.title(r"Strict total positivity of $[q^{(i-j)^2}]$, $q=0.55$")
    plt.tight_layout()
    plt.savefig(FIGURES / "strict_total_positivity.png", dpi=200)
    plt.close()


def partial_theta(z: float, rho: float, tolerance: float = 1.0e-17) -> float:
    """Partial theta sum sum_{n>=0} rho^(n^2) z^n for 0<rho<1."""

    total = 0.0
    n = 0
    while True:
        term = rho ** (n * n) * z**n
        total += term
        if n > 8 and abs(term) < tolerance * max(1.0, abs(total)):
            break
        n += 1
        if n > 100000:
            raise RuntimeError("partial theta failed to converge")
    return total


def highest_jet(a: float, n: np.ndarray | int) -> np.ndarray:
    """Level J_n=a^((n+1)(n+2)/2)/2^(n+1)."""

    n_array = np.asarray(n, dtype=float)
    log_value = (
        0.5 * (n_array + 1.0) * (n_array + 2.0) * math.log(a)
        - (n_array + 1.0) * math.log(2.0)
    )
    return np.exp(log_value)


def reciprocal_highest_jet_moment(a: float, s: float, t: float = 0.0) -> float:
    """Exact E[J^{-s} Delta^t] from the partial-theta theorem."""

    p = 1.0 - 2.0 / a
    ell0 = 2.0 * (a - 2.0) / (a * (a - 1.0))
    rho = a ** (-0.5 * s)
    z = 2.0 ** (s + 1.0) * a ** (-1.0 - 1.5 * s - t)
    prefactor = p * (ell0 / 2.0) ** t * 2.0**s * a ** (-s) / (t + 1.0)
    return prefactor * partial_theta(z, rho)


def experiment_partial_theta_jet() -> None:
    a = 3.0
    p = 1.0 - 2.0 / a
    rng = np.random.default_rng(2718281828)
    sample_size = 1_200_000
    degree = rng.geometric(p, size=sample_size) - 1
    log_jet = 0.5 * (degree + 1.0) * (degree + 2.0) * math.log(a) - (degree + 1.0) * math.log(2.0)
    ell0 = 2.0 * (a - 2.0) / (a * (a - 1.0))
    V = rng.random(sample_size)
    distance = 0.5 * ell0 * a ** (-degree) * V

    s_values = np.linspace(0.08, 2.0, 49)
    exact = np.array([reciprocal_highest_jet_moment(a, float(s)) for s in s_values])
    sample_indices = np.arange(0, len(s_values), 4)
    empirical = np.array([float(np.mean(np.exp(-s_values[i] * log_jet))) for i in sample_indices])
    write_csv(
        DATA / "highest_jet_partial_theta.csv",
        ["s", "exact_reciprocal_moment", "monte_carlo_reciprocal_moment"],
        ((float(s_values[i]), float(exact[i]), float(np.mean(np.exp(-s_values[i] * log_jet)))) for i in range(len(s_values))),
    )

    joint_rows = []
    for s, t in ((0.25, 0.5), (0.5, 1.0), (1.0, 0.5), (1.5, 2.0)):
        exact_joint = reciprocal_highest_jet_moment(a, s, t)
        empirical_joint = float(np.mean(np.exp(-s * log_jet) * distance**t))
        joint_rows.append((s, t, exact_joint, empirical_joint, abs(exact_joint - empirical_joint)))
    write_csv(
        DATA / "joint_jet_distance_partial_theta.csv",
        ["s", "t", "exact", "monte_carlo", "absolute_error"],
        joint_rows,
    )

    plt.figure(figsize=(8.6, 5.0))
    plt.plot(s_values, exact, linewidth=1.7, label="exact partial-theta transform")
    plt.scatter(s_values[sample_indices], empirical, s=24, label="deterministic Monte Carlo")
    plt.xlabel("reciprocal-moment order s")
    plt.ylabel(r"$\mathbb{E}\,J_a^{-s}$")
    plt.title(r"Highest local jet of $h_3$: partial-theta Mellin law")
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIGURES / "highest_jet_partial_theta.png", dpi=200)
    plt.close()

    # Exact staircase tail at its support values.
    n = np.arange(0, 18)
    J = highest_jet(a, n)
    tail = (2.0 / a) ** n
    write_csv(DATA / "highest_jet_tail_a3.csv", ["degree", "jet_level", "tail_probability"], zip(n, J, tail))
    plt.figure(figsize=(8.6, 5.0))
    plt.step(J, tail, where="post", linewidth=1.5)
    plt.xscale("log")
    plt.yscale("log")
    plt.xlabel("highest nonzero local derivative magnitude")
    plt.ylabel("tail probability")
    plt.title(r"Exact staircase tail of the highest local jet for $h_3$")
    plt.tight_layout()
    plt.savefig(FIGURES / "highest_jet_tail.png", dpi=200)
    plt.close()


def main() -> None:
    experiment_h3()
    experiment_local_degree()
    experiment_fup_clt()
    experiment_gram_spectrum()
    experiment_edgeworth()
    experiment_q_binomial_factorization()
    experiment_total_positivity()
    experiment_partial_theta_jet()
    print(f"Figures written to {FIGURES}")
    print(f"Data tables written to {DATA}")


if __name__ == "__main__":
    main()
