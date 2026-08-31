#!/usr/bin/env python3
"""Reproducible numerical experiments for matrix-dilated Fabius--Rvachev laws.

The report studies random series

    X = sum_{n>=1} A^{-n} v_j U_{n,j},

where the U_{n,j} are independent Uniform[-1,1] variables.  The main numerical
example is the genuinely planar one-generator rotating family

    g_n = q^n R_{n theta} v,       X = sum_{n>=1} g_n U_n.

This program checks exact formulas used in the report and produces all figures
and data tables shipped with the archive.  Numerical checks are diagnostics,
not substitutes for the proofs in the LaTeX source.

No network access is used.  The random seed and all parameters are fixed.

Requirements
------------
Python >= 3.10, NumPy, SciPy, Matplotlib, mpmath.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import Iterable

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

# Embed scalable TrueType fonts in vector-PDF figures.  Matplotlib's
# default Type-3 glyphs are harder to search and archive reliably.
matplotlib.rcParams["pdf.fonttype"] = 42
matplotlib.rcParams["ps.fonttype"] = 42
import mpmath as mp
import numpy as np
from numpy.polynomial import Polynomial
from numpy.polynomial.legendre import Legendre
from scipy.linalg import solve_discrete_lyapunov

SEED = 20260830


def rotation(theta: float) -> np.ndarray:
    """Return the 2x2 counterclockwise rotation matrix R_theta."""
    c = math.cos(theta)
    s = math.sin(theta)
    return np.array([[c, -s], [s, c]], dtype=float)


def sinc(z: np.ndarray | complex | float) -> np.ndarray | complex | float:
    """Unnormalized sinc, sin(z)/z, with the removable value 1 at z=0."""
    z_arr = np.asarray(z)
    with np.errstate(divide="ignore", invalid="ignore", over="ignore"):
        value = np.sin(z_arr) / z_arr
    value = np.where(z_arr == 0, 1.0, value)
    if np.ndim(z) == 0:
        return value.item()
    return value


def rotating_generators(q: float, theta: float, n_terms: int,
                        v: np.ndarray | None = None) -> np.ndarray:
    """Return rows g_n = q^n R_{n theta} v for n=1,...,n_terms."""
    if not 0.0 < q < 1.0:
        raise ValueError("q must lie strictly between 0 and 1")
    if n_terms < 1:
        raise ValueError("n_terms must be positive")
    if v is None:
        v = np.array([1.0, 0.0])
    v = np.asarray(v, dtype=float)
    out = np.empty((n_terms, 2), dtype=float)
    for n in range(1, n_terms + 1):
        out[n - 1] = (q ** n) * (rotation(n * theta) @ v)
    return out


def orient_to_half_plane(generators: np.ndarray) -> np.ndarray:
    """Orient each undirected generator so its angle lies in [0, pi)."""
    oriented = np.array(generators, dtype=float, copy=True)
    for i, g in enumerate(oriented):
        angle = math.atan2(g[1], g[0])
        if angle < 0.0:
            angle += 2.0 * math.pi
        if angle >= math.pi:
            oriented[i] = -g
    angles = np.arctan2(oriented[:, 1], oriented[:, 0])
    angles = np.where(angles < 0.0, angles + math.pi, angles)
    return oriented[np.argsort(angles)]


def zonotope_polygon(generators: np.ndarray) -> np.ndarray:
    """Construct the boundary polygon of sum_i [-g_i,g_i].

    For a planar zonotope, orient all generators into one half-plane, sort them
    by angle, start at -sum g_i, traverse edges 2g_i, and then traverse their
    negatives in the same order.  The returned first vertex is repeated last.
    """
    h = orient_to_half_plane(generators)
    point = -np.sum(h, axis=0)
    vertices = [point.copy()]
    for g in h:
        point = point + 2.0 * g
        vertices.append(point.copy())
    for g in h:
        point = point - 2.0 * g
        vertices.append(point.copy())
    vertices.append(vertices[0].copy())
    return np.asarray(vertices)


def polygon_area(vertices: np.ndarray) -> float:
    """Shoelace area of a closed polygonal chain."""
    x = vertices[:, 0]
    y = vertices[:, 1]
    return 0.5 * abs(float(np.dot(x[:-1], y[1:]) - np.dot(y[:-1], x[1:])))


def polygon_perimeter(vertices: np.ndarray) -> float:
    """Euclidean perimeter of a closed polygonal chain."""
    return float(np.linalg.norm(np.diff(vertices, axis=0), axis=1).sum())


def finite_area_formula(q: float, theta: float, n_terms: int,
                        v_norm: float = 1.0) -> float:
    """Exact finite-zonotope area grouped by the index gap m-n."""
    total = 0.0
    for gap in range(1, n_terms):
        geometric_sum = q * q * (1.0 - q ** (2 * (n_terms - gap))) / (1.0 - q * q)
        total += abs(math.sin(gap * theta)) * (q ** gap) * geometric_sum
    return 4.0 * v_norm * v_norm * total


def infinite_area_formula(q: float, theta: float, v_norm: float = 1.0,
                          tol: float = 1e-16) -> tuple[float, int]:
    """Evaluate the exact infinite area series to a certified geometric tail.

    Since |sin(m theta)| <= 1, the omitted support-series tail after M is at
    most q^(M+1)/(1-q).  We choose M so the resulting area error is below tol.
    """
    prefactor = 4.0 * v_norm * v_norm * q * q / (1.0 - q * q)
    m = 1
    total = 0.0
    while True:
        total += (q ** m) * abs(math.sin(m * theta))
        tail_bound = prefactor * (q ** (m + 1)) / (1.0 - q)
        if tail_bound < tol:
            return prefactor * total, m
        m += 1
        if m > 1_000_000:
            raise RuntimeError("area series did not meet tolerance")


def sample_rotating_law(rng: np.random.Generator, generators: np.ndarray,
                        n_samples: int, chunk_size: int = 50_000) -> np.ndarray:
    """Monte Carlo samples of sum_n g_n U_n, generated in bounded chunks."""
    samples = np.empty((n_samples, 2), dtype=float)
    for start in range(0, n_samples, chunk_size):
        stop = min(start + chunk_size, n_samples)
        u = rng.uniform(-1.0, 1.0, size=(stop - start, len(generators)))
        samples[start:stop] = u @ generators
    return samples


def characteristic_product(xi: np.ndarray, generators: np.ndarray) -> complex:
    """Finite characteristic product prod_n sinc(<xi,g_n>)."""
    return complex(np.prod(sinc(generators @ xi)))


def uniform_cumulant(order: int) -> mp.mpf:
    """Cumulant kappa_order of Uniform[-1,1]."""
    if order % 2 == 1:
        return mp.mpf("0")
    m = order // 2
    return mp.power(2, 2 * m - 1) * mp.bernoulli(2 * m) / m


def projection_cumulant_closed(q: float, theta: float, delta: float,
                               order: int) -> float:
    """Closed cyclotomic-resolvent cumulant of a rotating projection.

    The projected generator is q^n cos(n theta + delta).  For order 2m,
    expand cos^(2m) into its finite Fourier series and sum each geometric mode.
    """
    if order % 2 == 1:
        return 0.0
    m = order // 2
    Q = q ** (2 * m)
    power_sum = (math.comb(2 * m, m) / (2.0 ** (2 * m))) * Q / (1.0 - Q)
    for ell in range(1, m + 1):
        coeff = (2.0 ** (1 - 2 * m)) * math.comb(2 * m, m - ell)
        z = Q * np.exp(2j * ell * theta)
        geometric_mode = np.exp(2j * ell * delta) * z / (1.0 - z)
        power_sum += coeff * float(np.real(geometric_mode))
    return float(uniform_cumulant(order)) * power_sum


def moments_from_cumulants(cumulants: list[float]) -> list[float]:
    """Convert scalar cumulants to moments using the complete Bell recurrence."""
    max_order = len(cumulants) - 1
    moments = [0.0] * (max_order + 1)
    moments[0] = 1.0
    for n in range(1, max_order + 1):
        moments[n] = sum(
            math.comb(n - 1, k - 1) * cumulants[k] * moments[n - k]
            for k in range(1, n + 1)
        )
    return moments


def support_half_width(q: float, theta: float, delta: float,
                       tol: float = 1e-15) -> tuple[float, int]:
    """h = sum q^n |cos(n theta + delta)| with geometric tail control."""
    total = 0.0
    n = 1
    while True:
        total += (q ** n) * abs(math.cos(n * theta + delta))
        if q ** (n + 1) / (1.0 - q) < tol:
            return total, n
        n += 1


def legendre_coefficients_from_moments(moments: list[float], max_degree: int) -> list[float]:
    """Coefficients a_l=(2l+1)/2 E[P_l(Y)] for a density on [-1,1]."""
    coeffs: list[float] = []
    for ell in range(max_degree + 1):
        poly = Legendre.basis(ell).convert(kind=Polynomial)
        expectation = sum(float(c) * moments[k] for k, c in enumerate(poly.coef))
        coeffs.append(0.5 * (2 * ell + 1) * expectation)
    return coeffs


def abel_coefficient(m: int) -> float:
    """Complex Fourier coefficient c_m of |sin x| at frequency 2m."""
    if m == 0:
        return 2.0 / math.pi
    return -2.0 / (math.pi * (4.0 * m * m - 1.0))


def abel_residue(theta: float, m: int, r: float, n_terms: int) -> complex:
    """Compute (1-r) sum_{n>=1}|sin(n theta)|(r e^{-2im theta})^n."""
    n = np.arange(1, n_terms + 1, dtype=float)
    coefficients = np.abs(np.sin(n * theta))
    z = r * np.exp(-2j * m * theta)
    return complex((1.0 - r) * np.sum(coefficients * np.power(z, n)))


def write_csv(path: Path, header: Iterable[str], rows: Iterable[Iterable[object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(list(header))
        writer.writerows(rows)


def save_current_figure(base_path: Path) -> None:
    """Save the current standalone figure as both PNG and vector PDF."""
    plt.tight_layout()
    plt.savefig(base_path.with_suffix(".png"), dpi=180, bbox_inches="tight")
    plt.savefig(base_path.with_suffix(".pdf"), bbox_inches="tight")
    plt.close()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent,
                        help="directory receiving figures/, data/, and results/")
    parser.add_argument("--samples", type=int, default=180_000,
                        help="Monte Carlo sample count (default: 180000)")
    args = parser.parse_args()

    out = args.output_dir.resolve()
    figures = out / "figures"
    data = out / "data"
    results = out / "results"
    figures.mkdir(parents=True, exist_ok=True)
    data.mkdir(parents=True, exist_ok=True)
    results.mkdir(parents=True, exist_ok=True)

    rng = np.random.default_rng(SEED)

    # A bounded-type irrational rotation gives a visually well-distributed zonoid
    # and avoids accidental phase locking.  The theorem itself holds for every
    # irrational theta/pi.
    q = 0.68
    theta = math.pi * (math.sqrt(5.0) - 1.0) / 2.0
    v = np.array([1.0, 0.0])
    n_generator = 28
    generators = rotating_generators(q, theta, n_generator, v)

    # ------------------------------------------------------------------
    # Zonoid geometry: polygon construction, area, perimeter, convergence.
    # ------------------------------------------------------------------
    polygon = zonotope_polygon(generators[:18])
    polygon_area_value = polygon_area(polygon)
    polygon_perimeter_value = polygon_perimeter(polygon)
    formula_area_18 = finite_area_formula(q, theta, 18, np.linalg.norm(v))
    formula_perimeter_18 = 4.0 * np.linalg.norm(v) * q * (1.0 - q ** 18) / (1.0 - q)
    area_infinite, area_terms = infinite_area_formula(q, theta, np.linalg.norm(v))
    perimeter_infinite = 4.0 * np.linalg.norm(v) * q / (1.0 - q)

    area_rows = []
    for n_terms in range(2, 41):
        a_n = finite_area_formula(q, theta, n_terms, np.linalg.norm(v))
        p_n = 4.0 * np.linalg.norm(v) * q * (1.0 - q ** n_terms) / (1.0 - q)
        area_rows.append((n_terms, f"{a_n:.17g}", f"{area_infinite-a_n:.17g}",
                          f"{p_n:.17g}", f"{perimeter_infinite-p_n:.17g}"))
    write_csv(data / "area_convergence.csv",
              ["N", "area_N", "area_error", "perimeter_N", "perimeter_error"],
              area_rows)

    plt.figure(figsize=(7.0, 4.5))
    plt.plot([r[0] for r in area_rows], [float(r[2]) for r in area_rows], marker="o", markersize=3)
    plt.yscale("log")
    plt.xlabel("number N of retained rotating segments")
    plt.ylabel("infinite area minus finite area")
    plt.title("Geometric convergence of rotating-zonotope area")
    plt.grid(True, which="both", alpha=0.25)
    save_current_figure(figures / "area_convergence")

    plt.figure(figsize=(6.4, 6.4))
    plt.plot(polygon[:, 0], polygon[:, 1], linewidth=1.4)
    plt.axis("equal")
    plt.xlabel("x")
    plt.ylabel("y")
    plt.title("Eighteen-stage rotating zonotope")
    plt.grid(True, alpha=0.2)
    save_current_figure(figures / "rotating_zonoid")


    # ------------------------------------------------------------------
    # Abel-shape theorem: after multiplying by (1-q)/q, irrationally
    # rotating supports converge in Hausdorff distance to the disk of
    # radius 2||v||/pi.  The plot overlays several finite approximants.
    # ------------------------------------------------------------------
    shape_q_values = [0.50, 0.68, 0.82, 0.92, 0.97]
    phi_grid = np.linspace(0.0, 2.0 * math.pi, 4001)
    target_radius = 2.0 * np.linalg.norm(v) / math.pi
    shape_rows = []
    plt.figure(figsize=(6.6, 6.6))
    for shape_q in shape_q_values:
        # Choose N so the rescaled Hausdorff tail is below 2e-8.
        n_shape = max(2, int(math.ceil(math.log(2e-8 / (1.0 - shape_q) * (1.0 - shape_q), shape_q))))
        # The expression above simplifies algebraically; use a direct loop
        # to avoid relying on cancellation near q=1.
        n_shape = 1
        while shape_q ** (n_shape + 1) >= 2e-8:
            n_shape += 1
        shape_generators = rotating_generators(shape_q, theta, n_shape, v)
        shape_polygon = zonotope_polygon(shape_generators) * ((1.0 - shape_q) / shape_q)
        plt.plot(shape_polygon[:, 0], shape_polygon[:, 1], linewidth=1.0,
                 label=f"q={shape_q:.2f}")
        directions = np.column_stack((np.cos(phi_grid), np.sin(phi_grid)))
        support_values = np.sum(np.abs(directions @ shape_generators.T), axis=1)
        support_values *= (1.0 - shape_q) / shape_q
        max_error = float(np.max(np.abs(support_values - target_radius)))
        shape_rows.append((f"{shape_q:.9g}", n_shape, f"{max_error:.17g}"))
    circle_x = target_radius * np.cos(phi_grid)
    circle_y = target_radius * np.sin(phi_grid)
    plt.plot(circle_x, circle_y, linestyle="--", linewidth=1.5, label="limiting disk")
    plt.axis("equal")
    plt.xlabel("rescaled x")
    plt.ylabel("rescaled y")
    plt.title("Abel rescaling of irrational rotating zonoids")
    plt.legend(loc="best")
    plt.grid(True, alpha=0.2)
    save_current_figure(figures / "abel_shape_limit")
    write_csv(data / "abel_shape_limit.csv",
              ["q", "generator_terms", "max_support_error_to_disk"], shape_rows)

    # ------------------------------------------------------------------
    # Monte Carlo density and covariance against the exact covariance sum.
    # ------------------------------------------------------------------
    samples = sample_rotating_law(rng, generators, args.samples)
    sample_covariance = np.cov(samples, rowvar=False, bias=True)
    covariance_sum = generators.T @ generators / 3.0

    # Solve the exact infinite discrete Lyapunov equation
    # Sigma = B Sigma B^T + B(vv^T/3)B^T, B=q R_theta.
    B = q * rotation(theta)
    innovation_covariance = B @ np.outer(v, v) @ B.T / 3.0
    covariance_lyapunov = solve_discrete_lyapunov(B, innovation_covariance)

    covariance_rows = []
    for i in range(2):
        for j in range(2):
            covariance_rows.append((i, j,
                                    f"{sample_covariance[i,j]:.17g}",
                                    f"{covariance_sum[i,j]:.17g}",
                                    f"{covariance_lyapunov[i,j]:.17g}",
                                    f"{sample_covariance[i,j]-covariance_lyapunov[i,j]:.17g}"))
    write_csv(data / "covariance_check.csv",
              ["row", "column", "sample", "finite_sum_N28", "lyapunov_infinite", "sample_error"],
              covariance_rows)

    plt.figure(figsize=(6.5, 5.4))
    plt.hist2d(samples[:, 0], samples[:, 1], bins=180, density=True)
    plt.colorbar(label="estimated density")
    plt.xlabel("x")
    plt.ylabel("y")
    plt.title("Monte Carlo density of the irrationally rotating law")
    plt.axis("equal")
    save_current_figure(figures / "sample_density")

    # ------------------------------------------------------------------
    # Matrix Mahler equation.  The finite identity is exact up to rounding:
    # Phi_N(A^T xi) = sinc(<xi,v>) Phi_{N-1}(xi),
    # A=q^{-1}R_{-theta}.
    # ------------------------------------------------------------------
    A = (1.0 / q) * rotation(-theta)
    mahler_rows = []
    for test_index in range(12):
        xi = rng.normal(size=2) * (0.5 + test_index)
        lhs = characteristic_product(A.T @ xi, generators)
        rhs = sinc(float(np.dot(xi, v))) * characteristic_product(xi, generators[:-1])
        mahler_rows.append((test_index, f"{xi[0]:.17g}", f"{xi[1]:.17g}",
                            f"{lhs.real:.17g}", f"{rhs.real:.17g}",
                            f"{abs(lhs-rhs):.17g}"))
    write_csv(data / "mahler_checks.csv",
              ["test", "xi_1", "xi_2", "lhs", "rhs", "absolute_error"],
              mahler_rows)

    # ------------------------------------------------------------------
    # Thue--Morse/Prouhet cube for a finite generator family.
    # ------------------------------------------------------------------
    M = 6
    g_small = generators[:M]
    direction = np.array([0.7, -0.4])
    points = []
    signs = []
    for mask in range(1 << M):
        bits = np.array([(mask >> k) & 1 for k in range(M)], dtype=int)
        eps = 2 * bits - 1
        points.append(eps @ g_small)
        signs.append(-1.0 if int(bits.sum()) % 2 else 1.0)
    points_arr = np.asarray(points)
    signs_arr = np.asarray(signs)
    projected = points_arr @ direction
    prouhet_rows = []
    predicted_M = ((-2.0) ** M) * math.factorial(M) * float(np.prod(g_small @ direction))
    for degree in range(0, M + 3):
        observed = float(np.sum(signs_arr * projected ** degree))
        predicted = predicted_M if degree == M else (0.0 if degree < M else float("nan"))
        prouhet_rows.append((degree, f"{observed:.17g}",
                             "" if math.isnan(predicted) else f"{predicted:.17g}",
                             "" if math.isnan(predicted) else f"{observed-predicted:.17g}"))
    write_csv(data / "prouhet_checks.csv",
              ["degree", "signed_directional_moment", "predicted_when_applicable", "residual"],
              prouhet_rows)

    # ------------------------------------------------------------------
    # Rotation-orbit natural boundary: Abel residues at the dense candidate
    # singularities zeta_m=exp(-2 i m theta).
    # ------------------------------------------------------------------
    r_values = [0.80, 0.90, 0.95, 0.975, 0.9875, 0.99375, 0.996875]
    modes = [0, 1, 2, 4]
    max_terms = max(int(math.ceil(55.0 / (1.0 - r))) for r in r_values)
    abel_rows = []
    errors_by_mode: dict[int, list[float]] = {m: [] for m in modes}
    for m in modes:
        target = abel_coefficient(m)
        for r in r_values:
            n_terms = int(math.ceil(55.0 / (1.0 - r)))
            value = abel_residue(theta, m, r, n_terms)
            error = abs(value - target)
            errors_by_mode[m].append(error)
            abel_rows.append((m, f"{r:.9g}", n_terms,
                              f"{value.real:.17g}", f"{value.imag:.17g}",
                              f"{target:.17g}", f"{error:.17g}"))
    write_csv(data / "abel_residues.csv",
              ["mode_m", "r", "terms", "real_residue", "imag_residue", "target_c_m", "absolute_error"],
              abel_rows)

    plt.figure(figsize=(7.0, 4.8))
    x_values = [1.0 - r for r in r_values]
    for m in modes:
        plt.plot(x_values, errors_by_mode[m], marker="o", label=f"m={m}")
    plt.xscale("log")
    plt.yscale("log")
    plt.xlabel("1-r")
    plt.ylabel("absolute Abel-residue error")
    plt.title("Convergence to Fourier residues at boundary singularities")
    plt.legend()
    plt.grid(True, which="both", alpha=0.25)
    save_current_figure(figures / "abel_residue_convergence")

    # ------------------------------------------------------------------
    # Bell--Bernoulli moments and the exact Legendre projection bridge.
    # ------------------------------------------------------------------
    phi_w = 0.37
    delta = -phi_w  # v has angle 0, so <w,R_{n theta}v>=cos(n theta-phi_w)
    max_degree = 14
    cumulants = [0.0] * (max_degree + 1)
    for order in range(1, max_degree + 1):
        cumulants[order] = projection_cumulant_closed(q, theta, delta, order)
    raw_moments = moments_from_cumulants(cumulants)
    half_width, width_terms = support_half_width(q, theta, delta)
    normalized_moments = [raw_moments[k] / (half_width ** k) for k in range(max_degree + 1)]
    legendre_coeffs = legendre_coefficients_from_moments(normalized_moments, max_degree)
    legendre_rows = []
    for ell, coeff in enumerate(legendre_coeffs):
        legendre_rows.append((ell, f"{coeff:.17g}",
                              f"{normalized_moments[ell]:.17g}" if ell < len(normalized_moments) else ""))
    write_csv(data / "projection_legendre_coefficients.csv",
              ["degree", "legendre_density_coefficient", "normalized_raw_moment_same_degree"],
              legendre_rows)

    w = np.array([math.cos(phi_w), math.sin(phi_w)])
    projected_samples = (samples @ w) / half_width
    x_grid = np.linspace(-1.0, 1.0, 900)
    approximation = np.zeros_like(x_grid)
    for ell, coeff in enumerate(legendre_coeffs):
        approximation += coeff * Legendre.basis(ell)(x_grid)

    plt.figure(figsize=(7.0, 4.8))
    plt.hist(projected_samples, bins=150, density=True, alpha=0.45, label="Monte Carlo projection")
    plt.plot(x_grid, approximation, linewidth=1.6, label=f"Legendre degrees 0--{max_degree}")
    plt.xlabel("normalized projection y")
    plt.ylabel("density")
    plt.title("Projection density and Bell--Bernoulli Legendre reconstruction")
    plt.legend()
    plt.grid(True, alpha=0.2)
    save_current_figure(figures / "projection_legendre")

    # ------------------------------------------------------------------
    # Plain-text audit trail.
    # ------------------------------------------------------------------
    summary_lines = [
        "Matrix-dilated Fabius--Rvachev numerical audit",
        "================================================",
        f"seed = {SEED}",
        f"q = {q:.17g}",
        f"theta/pi = {theta/math.pi:.17g}",
        f"generator truncation = {n_generator}",
        f"Monte Carlo samples = {args.samples}",
        "",
        "Planar zonotope checks",
        f"polygon area (N=18) = {polygon_area_value:.17g}",
        f"determinant formula area (N=18) = {formula_area_18:.17g}",
        f"absolute area discrepancy = {abs(polygon_area_value-formula_area_18):.17g}",
        f"polygon perimeter (N=18) = {polygon_perimeter_value:.17g}",
        f"generator formula perimeter (N=18) = {formula_perimeter_18:.17g}",
        f"absolute perimeter discrepancy = {abs(polygon_perimeter_value-formula_perimeter_18):.17g}",
        f"infinite area = {area_infinite:.17g} (series terms {area_terms})",
        f"infinite perimeter = {perimeter_infinite:.17g}",
        "",
        "Covariance checks",
        f"sample covariance =\n{sample_covariance}",
        f"N=28 direct generator covariance =\n{covariance_sum}",
        f"infinite Lyapunov covariance =\n{covariance_lyapunov}",
        f"max sample/Lyapunov discrepancy = {np.max(np.abs(sample_covariance-covariance_lyapunov)):.17g}",
        "",
        "Mahler equation",
        f"maximum finite-product residual = {max(float(row[-1]) for row in mahler_rows):.17g}",
        "",
        "Thue--Morse/Prouhet cube",
        f"M = {M}",
        f"max residual below degree M = {max(abs(float(row[1])) for row in prouhet_rows[:M]):.17g}",
        f"degree-M residual = {abs(float(prouhet_rows[M][3])):.17g}",
        "",
        "Natural-boundary Abel experiment",
        f"maximum truncation used = {max_terms}",
    ]
    for m in modes:
        summary_lines.append(
            f"mode {m}: last error at r={r_values[-1]} is {errors_by_mode[m][-1]:.17g}"
        )
    summary_lines.extend([
        "",
        "Projection/Legendre bridge",
        f"projection angle = {phi_w:.17g}",
        f"support half-width = {half_width:.17g} (tail-controlled after {width_terms} terms)",
        f"odd coefficient max = {max(abs(legendre_coeffs[k]) for k in range(1,max_degree+1,2)):.17g}",
        "",
        "All CSV tables and figures were regenerated by this run.",
    ])
    (results / "numerical_summary.txt").write_text("\n".join(summary_lines) + "\n", encoding="utf-8")

    print("\n".join(summary_lines))


if __name__ == "__main__":
    main()
