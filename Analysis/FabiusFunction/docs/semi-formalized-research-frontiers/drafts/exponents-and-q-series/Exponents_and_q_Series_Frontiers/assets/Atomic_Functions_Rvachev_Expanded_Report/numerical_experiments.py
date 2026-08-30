#!/usr/bin/env python3
"""Reproducible numerical experiments for the Rvachev atomic-function report.

The script is intentionally self-contained.  It produces the figures and CSV
files referenced by the LaTeX report and, more importantly, checks several
closed formulae by numerically independent computations.

Mathematical conventions
------------------------
For a > 1, h_a is the probability density with characteristic function

    hhat_a(t) = product_{j>=1} sinc(t a^{-j}),  sinc(z) = sin(z)/z.

Its support is [-b,b], b = 1/(a-1), and it obeys

    h_a(x) = (a/2) integral_{a x-1}^{a x+1} h_a(u) du.

For a >= 2 the normalized derivative vectors

    e_n = h_a^{(n)} / ||h_a^{(n)}||_2

have the exact Gram matrix

    <e_m,e_n> = 0                                      if m+n is odd,
              = (-1)^((n-m)/2) a^{-(n-m)^2/4}         otherwise.

The even and odd parity blocks are therefore Toeplitz matrices with entries
(-1)^(j-k) q^((j-k)^2), q=1/a.  Their symbol is a Jacobi theta function and
their exact q-binomial Gram-Schmidt factorization is verified below.

Requirements: Python 3.10+, NumPy, SciPy, Matplotlib.
"""

from __future__ import annotations

import csv
import math
from pathlib import Path
from typing import Iterable

import matplotlib.pyplot as plt
import numpy as np
from numpy.typing import NDArray
from scipy.integrate import cumulative_trapezoid
from scipy.special import ndtr

OUTPUT = Path(__file__).resolve().parent
RNG = np.random.default_rng(20260828)


def q_pochhammer(q: float, n: int | None = None, *, tol: float = 1e-18) -> float:
    """Return (q;q)_n, or (q;q)_infinity when n is None.

    The infinite product is truncated only after q^k is below ``tol``.  All
    q's used here lie in (0,1), so this direct product is stable.
    """

    product = 1.0
    if n is not None:
        for k in range(1, n + 1):
            product *= 1.0 - q**k
        return product

    k = 1
    while q**k > tol:
        product *= 1.0 - q**k
        k += 1
    return product


def theta_bounds(a: float, *, tol: float = 1e-18) -> tuple[float, float]:
    """Exact optimal Riesz bounds A_a and B_a from theta products.

    With q=1/a,

        A_a = theta_4(0,q) = (q^2;q^2)_inf (q;q^2)_inf^2,
        B_a = theta_3(0,q) = (q^2;q^2)_inf (-q;q^2)_inf^2.
    """

    q = 1.0 / a
    even = 1.0
    odd_minus = 1.0
    odd_plus = 1.0
    k = 1
    while q ** (2 * k - 1) > tol:
        even *= 1.0 - q ** (2 * k)
        odd_minus *= 1.0 - q ** (2 * k - 1)
        odd_plus *= 1.0 + q ** (2 * k - 1)
        k += 1
    return even * odd_minus**2, even * odd_plus**2


def theta_symbol(theta: NDArray[np.float64], a: float, cutoff: int = 120) -> NDArray[np.float64]:
    """Evaluate Theta_a(theta)=sum_l (-1)^l a^{-l^2} exp(i l theta)."""

    q = 1.0 / a
    result = np.ones_like(theta)
    for ell in range(1, cutoff + 1):
        term = 2.0 * ((-1.0) ** ell) * q ** (ell * ell) * np.cos(ell * theta)
        result += term
        if np.max(np.abs(term)) < 1e-17:
            break
    return result


def signed_gram(a: float, n: int) -> NDArray[np.float64]:
    """N-by-N Gram matrix for one parity tower of normalized derivatives."""

    j = np.arange(n)
    d = j[:, None] - j[None, :]
    q = 1.0 / a
    return ((-1.0) ** d) * q ** (d * d)


def gaussian_binomial(n: int, k: int, q: float) -> float:
    """Numerically evaluate the Gaussian binomial [n choose k]_q."""

    if k < 0 or k > n:
        return 0.0
    k = min(k, n - k)
    value = 1.0
    for j in range(1, k + 1):
        value *= (1.0 - q ** (n - k + j)) / (1.0 - q**j)
    return value


def q_binomial_cholesky(a: float, n: int) -> NDArray[np.float64]:
    """Lower triangular matrix C with C G C^T diagonal.

    C_{r,j} = q^(r-j) [r choose j]_{q^2}, 0 <= j <= r.
    """

    q = 1.0 / a
    c = np.zeros((n, n), dtype=float)
    for r in range(n):
        for j in range(r + 1):
            c[r, j] = q ** (r - j) * gaussian_binomial(r, j, q * q)
    return c


def validate_derivative_gram_geometry() -> None:
    """Check determinant, theta bounds, and q-binomial factorization."""

    rows: list[dict[str, float | int]] = []
    for a in (2.0, 3.0, 4.0, 10.0):
        lower, upper = theta_bounds(a)
        for n in (4, 8, 16, 32):
            g = signed_gram(a, n)
            eig = np.linalg.eigvalsh(g)

            # Closed leading-principal-minor determinant.
            q = 1.0 / a
            det_closed = 1.0
            for d in range(1, n):
                det_closed *= (1.0 - q ** (2 * d)) ** (n - d)
            sign, logdet_num = np.linalg.slogdet(g)
            det_num = sign * math.exp(logdet_num)

            # Exact q-binomial Gram-Schmidt/Cholesky identity.
            c = q_binomial_cholesky(a, n)
            diagonalized = c @ g @ c.T
            target = np.diag([q_pochhammer(q * q, r) for r in range(n)])
            max_factor_error = float(np.max(np.abs(diagonalized - target)))

            rows.append(
                {
                    "a": a,
                    "N": n,
                    "theta_lower_A": lower,
                    "finite_min_eigenvalue": float(eig[0]),
                    "finite_max_eigenvalue": float(eig[-1]),
                    "theta_upper_B": upper,
                    "condition_number": float(eig[-1] / eig[0]),
                    "determinant_numeric": det_num,
                    "determinant_closed": det_closed,
                    "relative_det_error": abs(det_num - det_closed) / det_closed,
                    "max_q_cholesky_error": max_factor_error,
                }
            )

            if eig[0] < lower - 5e-12 or eig[-1] > upper + 5e-12:
                raise RuntimeError("Finite Gram spectrum escaped the exact theta bounds")
            if abs(det_num - det_closed) > 5e-10 * det_closed:
                raise RuntimeError("Gram determinant validation failed")
            if max_factor_error > 5e-12:
                raise RuntimeError("q-binomial Gram-Schmidt validation failed")

    with (OUTPUT / "derivative_gram_validation.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    with (OUTPUT / "theta_riesz_bounds.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(["a", "A_a", "B_a", "B_a/A_a"])
        for a in (2.0, 3.0, 4.0, 10.0):
            lower, upper = theta_bounds(a)
            writer.writerow([a, lower, upper, upper / lower])


def plot_derivative_gram_spectrum() -> None:
    """Plot the exact theta symbols and finite Toeplitz eigenvalue ranges."""

    theta = np.linspace(-math.pi, math.pi, 2400)
    fig, ax = plt.subplots(figsize=(8.4, 4.9))
    for a in (2.0, 3.0, 4.0):
        values = theta_symbol(theta, a)
        line = ax.plot(theta, values, label=fr"$a={a:g}$")[0]

        # Show a finite-N spectrum at a separate x position near the right edge.
        eig = np.linalg.eigvalsh(signed_gram(a, 64))
        x = np.full_like(eig, math.pi + 0.12 * (a - 3.0))
        ax.scatter(x, eig, s=5, alpha=0.35, color=line.get_color())

    ax.axvline(math.pi, linewidth=0.8, linestyle="--")
    ax.text(math.pi + 0.04, 0.03, "finite $N=64$ eigenvalues", rotation=90,
            va="bottom", fontsize=8)
    ax.set_xlim(-math.pi, math.pi + 0.35)
    ax.set_xlabel(r"frequency $\theta$")
    ax.set_ylabel(r"$\Theta_a(\theta)=\vartheta_4(\theta/2,1/a)$")
    ax.set_title("Theta symbols governing the normalized derivative Gram matrices")
    ax.grid(alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(OUTPUT / "derivative_gram_theta.png", dpi=220)
    plt.close(fig)


def iterate_density(a: float, grid_size: int = 65537, iterations: int = 70) -> tuple[NDArray[np.float64], NDArray[np.float64]]:
    """Iterate the exact refinement operator on a uniform support grid.

    The mathematical operator is exact; cumulative trapezoidal quadrature and
    linear interpolation are the only discretizations.  Renormalization removes
    the tiny accumulated mass drift without changing the fixed point.
    """

    b = 1.0 / (a - 1.0)
    x = np.linspace(-b, b, grid_size)
    f = np.full_like(x, 1.0 / (2.0 * b))

    for _ in range(iterations):
        primitive = np.concatenate(([0.0], cumulative_trapezoid(f, x)))
        lo = np.clip(a * x - 1.0, -b, b)
        hi = np.clip(a * x + 1.0, -b, b)
        int_hi = np.interp(hi, x, primitive)
        int_lo = np.interp(lo, x, primitive)
        new_f = 0.5 * a * (int_hi - int_lo)
        new_f[(a * x + 1.0 <= -b) | (a * x - 1.0 >= b)] = 0.0
        mass = np.trapezoid(new_f, x)
        f = new_f / mass

    return x, f


def h3_experiment() -> None:
    """Compute and plot h_3 and write basic fixed-point diagnostics."""

    a = 3.0
    b = 1.0 / (a - 1.0)
    b1 = (a - 2.0) / (a * (a - 1.0))
    x, f = iterate_density(a)

    mass = float(np.trapezoid(f, x))
    symmetry = float(np.max(np.abs(f - f[::-1])))
    central = np.abs(x) <= 0.92 * b1  # stay away from the grid-level endpoints
    plateau_error = float(np.max(np.abs(f[central] - a / 2.0)))

    # Check the fixed-point equation once more using the converged density.
    primitive = np.concatenate(([0.0], cumulative_trapezoid(f, x)))
    lo = np.clip(a * x - 1.0, -b, b)
    hi = np.clip(a * x + 1.0, -b, b)
    tf = 0.5 * a * (np.interp(hi, x, primitive) - np.interp(lo, x, primitive))
    fixed_point_error = float(np.max(np.abs(tf - f)))

    with (OUTPUT / "ha_a3_diagnostics.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(["quantity", "value"])
        writer.writerow(["mass", mass])
        writer.writerow(["maximum_symmetry_error", symmetry])
        writer.writerow(["central_plateau_value", a / 2.0])
        writer.writerow(["maximum_central_plateau_error", plateau_error])
        writer.writerow(["maximum_fixed_point_residual", fixed_point_error])

    fig, ax = plt.subplots(figsize=(8.4, 4.8))
    ax.plot(x, f, linewidth=1.25)
    ax.axvspan(-b1, b1, alpha=0.13, label=r"central degree-$0$ gap")
    ax.set_xlabel(r"$x$")
    ax.set_ylabel(r"$h_3(x)$")
    ax.set_title(r"The smooth Cantor spline $h_3$")
    ax.grid(alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(OUTPUT / "ha_a3_density.png", dpi=220)
    plt.close(fig)


def local_degree(x: float, a: float, maximum_generation: int = 1000) -> int:
    """Return the gap generation containing x for a>2.

    Points on the Cantor set never enter the central gap, but a continuously
    sampled floating-point number does so with probability one.
    """

    b1 = (a - 2.0) / (a * (a - 1.0))
    y = x
    for generation in range(maximum_generation):
        if -b1 < y < b1:
            return generation
        y = a * y + 1.0 if y < 0.0 else a * y - 1.0
    raise RuntimeError("Sample behaved like a Cantor-set point beyond the safety limit")


def local_degree_experiment(samples: int = 400_000) -> None:
    """Verify the exact geometric law for the local polynomial degree."""

    a = 3.0
    b = 1.0 / (a - 1.0)
    sample = RNG.uniform(-b, b, size=samples)
    degree = np.fromiter((local_degree(float(x), a) for x in sample), dtype=np.int64)

    maximum = int(np.quantile(degree, 0.9997))
    k = np.arange(maximum + 1)
    empirical = np.bincount(degree, minlength=maximum + 1)[: maximum + 1] / samples
    exact = (1.0 - 2.0 / a) * (2.0 / a) ** k

    with (OUTPUT / "local_degree_monte_carlo.txt").open("w", encoding="utf-8") as stream:
        stream.write(f"samples={samples}\n")
        stream.write(f"empirical_mean={degree.mean():.12g}\n")
        stream.write(f"exact_mean={2.0/(a-2.0):.12g}\n")
        stream.write(f"empirical_variance={degree.var():.12g}\n")
        stream.write(f"exact_variance={2.0*a/(a-2.0)**2:.12g}\n")

    fig, ax = plt.subplots(figsize=(8.4, 4.8))
    width = 0.38
    ax.bar(k - width / 2, exact, width=width, label="exact geometric law")
    ax.bar(k + width / 2, empirical, width=width, label="fixed-seed experiment")
    ax.set_yscale("log")
    ax.set_xlabel("local polynomial degree")
    ax.set_ylabel("probability")
    ax.set_title(r"Local degree distribution for $h_3$")
    ax.grid(axis="y", alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(OUTPUT / "local_degree_distribution.png", dpi=220)
    plt.close(fig)


def sample_standardized_fup(n: int, samples: int) -> NDArray[np.float64]:
    """Sample the standardized Fup_n law without Fourier inversion.

    Multiplying Z_n by 2^(n+1) does not affect standardization.  We therefore
    sample S_n = 2 X + U_1+...+U_n, where X has the Up density and can itself
    be generated as sum_{j>=1} 2^{-j} V_j with uniform digits V_j.
    """

    # Forty-eight binary scales make the omitted tail smaller than 2^-48.
    x = np.zeros(samples)
    for j in range(1, 49):
        x += (2.0 ** -j) * RNG.uniform(-1.0, 1.0, size=samples)

    s = 2.0 * x
    # Generate the n extra uniforms in modest blocks to keep memory bounded.
    for _ in range(n):
        s += RNG.uniform(-1.0, 1.0, size=samples)

    variance = (3.0 * n + 4.0) / 9.0
    return s / math.sqrt(variance)


def fup_clt_experiment(samples: int = 260_000) -> None:
    """Plot the standardized Fup_n hierarchy and validate its cumulants."""

    rows: list[dict[str, float | int]] = []
    fig, ax = plt.subplots(figsize=(8.4, 4.9))
    bins = np.linspace(-4.2, 4.2, 170)

    for n in (1, 4, 16, 64):
        w = sample_standardized_fup(n, samples)
        hist, edges = np.histogram(w, bins=bins, density=True)
        centers = 0.5 * (edges[:-1] + edges[1:])
        ax.plot(centers, hist, linewidth=1.0, label=fr"$n={n}$")

        empirical_k4 = float(np.mean(w**4) - 3.0 * np.mean(w**2) ** 2)
        # kappa_4(2X+sum U) = 16 kappa_4(X) + n kappa_4(U).
        # For X~Up: kappa_4(X)=-2/225; for U~Unif[-1,1]: -2/15.
        exact_k4_unscaled = -32.0 / 225.0 - 2.0 * n / 15.0
        variance_unscaled = (3.0 * n + 4.0) / 9.0
        exact_k4 = exact_k4_unscaled / variance_unscaled**2
        rows.append(
            {
                "n": n,
                "samples": samples,
                "exact_standardized_kappa4": exact_k4,
                "empirical_standardized_kappa4": empirical_k4,
            }
        )

    z = np.linspace(-4.2, 4.2, 800)
    normal = np.exp(-0.5 * z * z) / math.sqrt(2.0 * math.pi)
    ax.plot(z, normal, linestyle="--", linewidth=1.4, label="standard Gaussian")
    ax.set_xlabel("standardized coordinate")
    ax.set_ylabel("density")
    ax.set_title(r"Gaussian scaling limit of the $\operatorname{Fup}_n$ hierarchy")
    ax.grid(alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(OUTPUT / "fup_clt.png", dpi=220)
    plt.close(fig)

    with (OUTPUT / "fup_clt_cumulants.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def write_general_parameters() -> None:
    """Write exact elementary parameters for representative a values."""

    with (OUTPUT / "generalized_ha_parameters.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(
            ["a", "support_halfwidth_b", "central_half_gap_b1", "Cantor_dimension",
             "mean_local_degree", "variance_local_degree", "variance_Xa"]
        )
        for a in (2.05, 2.2, 2.5, 3.0, 4.0, 8.0):
            writer.writerow(
                [
                    a,
                    1.0 / (a - 1.0),
                    (a - 2.0) / (a * (a - 1.0)),
                    math.log(2.0) / math.log(a),
                    2.0 / (a - 2.0),
                    2.0 * a / (a - 2.0) ** 2,
                    1.0 / (3.0 * (a * a - 1.0)),
                ]
            )


def main() -> None:
    validate_derivative_gram_geometry()
    plot_derivative_gram_spectrum()
    h3_experiment()
    local_degree_experiment()
    fup_clt_experiment()
    write_general_parameters()
    print(f"Wrote experiments to {OUTPUT}")


if __name__ == "__main__":
    main()
