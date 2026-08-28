#!/usr/bin/env python3
"""Reproducible experiments for the Fabius/up integral-frontiers report.

The program has two independent parts.

1. Exact arithmetic: Bernoulli cumulants give moments of
   X = sum_{n>=0} U_n/2^(n+1) and Y = 2X-1, whose density is Rvachev's
   up-function.  Exact Gram--Schmidt then gives the Jacobi coefficients of
   the up measure as rational numbers.

2. Floating-point checks: the density is reconstructed by iterating the
   probability/refinement operator

       (T f)(x) = integral_{2x-1}^{2x+1} f(t) dt.

   The grid approximation is used only to test identities proved in the
   report: moment normalization, the Cauchy-transform differential equation,
   the fractional-primitive refinement equation, the quantile fractional
   integral formula, and order-statistic/power-integral identities.

No numerical output is used as a substitute for proof.  The script writes a
plain-text summary, a small LaTeX table, and three diagnostic figures.
"""

from __future__ import annotations

import argparse
import math
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import cumulative_trapezoid, quad, trapezoid


# ---------------------------------------------------------------------------
# Exact Bernoulli/cumulant/moment engine
# ---------------------------------------------------------------------------


def bernoulli_numbers(n_max: int) -> list[Fraction]:
    """Return B_0,...,B_n with the standard convention B_1=-1/2."""
    if n_max < 0:
        raise ValueError("n_max must be nonnegative")
    values = [Fraction(0) for _ in range(n_max + 1)]
    values[0] = Fraction(1)
    for n in range(1, n_max + 1):
        values[n] = -sum(
            Fraction(math.comb(n + 1, k)) * values[k]
            for k in range(n)
        ) / Fraction(n + 1)
    return values


def cumulants_x(n_max: int) -> list[Fraction]:
    """Cumulants of X=sum U_n/2^(n+1)."""
    b = bernoulli_numbers(n_max)
    kappa = [Fraction(0) for _ in range(n_max + 1)]
    if n_max >= 1:
        kappa[1] = Fraction(1, 2)
    for n in range(2, n_max + 1):
        kappa[n] = b[n] / Fraction(n * (2**n - 1))
    return kappa


def cumulants_y(n_max: int) -> list[Fraction]:
    """Cumulants of Y=2X-1, whose density is the up-function."""
    b = bernoulli_numbers(n_max)
    kappa = [Fraction(0) for _ in range(n_max + 1)]
    for n in range(2, n_max + 1):
        kappa[n] = Fraction(2**n) * b[n] / Fraction(n * (2**n - 1))
    return kappa


def moments_from_cumulants(kappa: Sequence[Fraction]) -> list[Fraction]:
    """Use the complete-Bell recurrence to convert cumulants to moments."""
    n_max = len(kappa) - 1
    moment = [Fraction(0) for _ in range(n_max + 1)]
    moment[0] = Fraction(1)
    for n in range(1, n_max + 1):
        moment[n] = sum(
            Fraction(math.comb(n - 1, j - 1)) * kappa[j] * moment[n - j]
            for j in range(1, n + 1)
        )
    return moment


def polynomial_add(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    """Add coefficient arrays in ascending powers."""
    size = max(len(a), len(b))
    out = [Fraction(0) for _ in range(size)]
    for i, value in enumerate(a):
        out[i] += value
    for i, value in enumerate(b):
        out[i] += value
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def polynomial_scale(a: Sequence[Fraction], c: Fraction) -> list[Fraction]:
    return [c * value for value in a]


def moment_inner_product(
    a: Sequence[Fraction], b: Sequence[Fraction], moments: Sequence[Fraction]
) -> Fraction:
    """Compute integral p(x)q(x) up(x) dx exactly from the moment list."""
    return sum(
        ai * bj * moments[i + j]
        for i, ai in enumerate(a)
        for j, bj in enumerate(b)
    )


def jacobi_coefficients(
    moments: Sequence[Fraction], degree: int
) -> tuple[list[list[Fraction]], list[Fraction], list[Fraction | None]]:
    """Monic Gram--Schmidt and recurrence coefficients for a symmetric law.

    If P_n is monic and h_n=<P_n,P_n>, then
        P_{n+1}(x)=xP_n(x)-a_n P_{n-1}(x),  a_n=h_n/h_{n-1}.
    """
    polynomials: list[list[Fraction]] = []
    norms: list[Fraction] = []
    for n in range(degree + 1):
        p = [Fraction(0)] * n + [Fraction(1)]
        for k in range(n):
            projection = moment_inner_product(p, polynomials[k], moments) / norms[k]
            p = polynomial_add(p, polynomial_scale(polynomials[k], -projection))
        norm = moment_inner_product(p, p, moments)
        if norm <= 0:
            raise ArithmeticError("nonpositive Gram norm; insufficient/incorrect moments")
        polynomials.append(p)
        norms.append(norm)
    coeffs: list[Fraction | None] = [None]
    coeffs.extend(norms[n] / norms[n - 1] for n in range(1, degree + 1))
    return polynomials, norms, coeffs


# ---------------------------------------------------------------------------
# Numerical up-density and derived transforms
# ---------------------------------------------------------------------------


def reconstruct_up(points: int, iterations: int) -> tuple[np.ndarray, np.ndarray]:
    """Iterate the positive refinement operator on a uniform grid."""
    if points < 1001 or points % 2 == 0:
        raise ValueError("points must be an odd integer at least 1001")
    x = np.linspace(-1.0, 1.0, points)
    dx = x[1] - x[0]
    density = np.full(points, 0.5)  # normalized uniform starting density
    for _ in range(iterations):
        cumulative = np.concatenate(
            ([0.0], cumulative_trapezoid(density, x))
        )
        lower = np.clip(2.0 * x - 1.0, -1.0, 1.0)
        upper = np.clip(2.0 * x + 1.0, -1.0, 1.0)
        next_density = np.interp(upper, x, cumulative) - np.interp(
            lower, x, cumulative
        )
        next_density[0] = 0.0
        next_density[-1] = 0.0
        mass = trapezoid(next_density, x)
        if not np.isfinite(mass) or mass <= 0:
            raise ArithmeticError("refinement iteration lost positivity or mass")
        density = next_density / mass
    return x, density


def make_cdf_and_quantile(
    x: np.ndarray, density: np.ndarray
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return grids for F on [0,1] and a monotone inverse interpolation table."""
    mask = x >= 0.0
    xp = x[mask]
    up = density[mask]
    # On [0,1], up(x)=1-F(x).  Clipping and monotone accumulation suppress
    # tiny floating-point violations near the flat endpoints.
    f = np.clip(1.0 - up, 0.0, 1.0)
    f = np.maximum.accumulate(f)
    f[-1] = 1.0

    # np.interp requires strictly increasing abscissas.  Flat machine-zero
    # sections are harmless for integrals; retain their last x representative.
    unique_f, first_indices = np.unique(f, return_index=True)
    unique_x = xp[first_indices]
    if unique_f[0] > 0.0:
        unique_f = np.insert(unique_f, 0, 0.0)
        unique_x = np.insert(unique_x, 0, 0.0)
    if unique_f[-1] < 1.0:
        unique_f = np.append(unique_f, 1.0)
        unique_x = np.append(unique_x, 1.0)
    return xp, f, np.vstack((unique_f, unique_x))


def quantile(values: np.ndarray | float, table: np.ndarray) -> np.ndarray | float:
    return np.interp(values, table[0], table[1])


def cauchy_transform(z: complex, x: np.ndarray, density: np.ndarray) -> complex:
    return complex(trapezoid(density / (z - x), x))


def cauchy_derivative(z: complex, x: np.ndarray, density: np.ndarray) -> complex:
    return complex(-trapezoid(density / (z - x) ** 2, x))


def fractional_left_primitive(
    alpha: float, evaluation_point: float, x: np.ndarray, density: np.ndarray
) -> float:
    """H_alpha(x)=I_{-1+}^alpha up(x), evaluated by a grid quadrature."""
    if alpha <= 0:
        raise ValueError("alpha must be positive")
    active = x < evaluation_point
    # For alpha<1 the endpoint kernel is integrably singular.  Excluding the
    # endpoint and using a fine grid is adequate for diagnostics, not proof.
    kernel = np.maximum(evaluation_point - x[active], 0.0) ** (alpha - 1.0)
    return float(trapezoid(kernel * density[active], x[active]) / math.gamma(alpha))


def quantile_fractional_identity(
    alpha: float,
    u_value: float,
    xp: np.ndarray,
    f: np.ndarray,
    q_table: np.ndarray,
) -> tuple[float, float]:
    """Compute both sides of I^alpha Q(u) identity by adaptive quadrature."""
    if not (alpha > 0 and 0 < u_value < 1):
        raise ValueError("need alpha>0 and 0<u<1")

    def q_scalar(v: float) -> float:
        return float(quantile(v, q_table))

    lhs_integral, _ = quad(
        lambda v: (u_value - v) ** (alpha - 1.0) * q_scalar(v),
        0.0,
        u_value,
        points=[u_value],
        epsabs=2e-10,
        epsrel=2e-10,
        limit=300,
    )
    lhs = lhs_integral / math.gamma(alpha)

    q_u = q_scalar(u_value)
    right_mask = xp <= q_u
    rhs = trapezoid(
        np.maximum(u_value - f[right_mask], 0.0) ** alpha,
        xp[right_mask],
    ) / math.gamma(alpha + 1.0)
    return float(lhs), float(rhs)


def fraction_string(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def latex_fraction(value: Fraction) -> str:
    return (
        str(value.numerator)
        if value.denominator == 1
        else rf"\frac{{{value.numerator}}}{{{value.denominator}}}"
    )


def write_exact_table(path: Path, coeffs: Sequence[Fraction | None], rows: int) -> None:
    with path.open("w", encoding="utf-8") as handle:
        handle.write("% Generated by numerical_experiments.py; exact rational arithmetic.\n")
        handle.write("\\begin{tabular}{rll}\n\\toprule\n")
        handle.write("$n$ & $a_n$ (exact) & decimal " + "\\\\" + "\n\\midrule\n")
        for n in range(1, min(rows, len(coeffs) - 1) + 1):
            value = coeffs[n]
            assert isinstance(value, Fraction)
            handle.write(
                f"{n} & ${latex_fraction(value)}$ & ${float(value):.12f}$ "
                + "\\\\"
                + "\n"
            )
        handle.write("\\bottomrule\n\\end{tabular}\n")


def run(output_dir: Path, points: int, iterations: int, jacobi_degree: int) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)

    # Exact Jacobi data need moments through degree 2N.  We compute a
    # longer X-moment table as well, because its rational entries furnish a
    # rapidly convergent Newton series for generalized (including negative)
    # moments E[X^s].
    generalized_degree = max(160, 2 * jacobi_degree + 4)
    x_moments = moments_from_cumulants(cumulants_x(generalized_degree))
    y_moments = moments_from_cumulants(cumulants_y(2 * jacobi_degree + 4))
    _, _, jacobi = jacobi_coefficients(y_moments, jacobi_degree)
    write_exact_table(output_dir / "jacobi_coefficients.tex", jacobi, rows=5)

    grid, up_density = reconstruct_up(points=points, iterations=iterations)
    xp, f_grid, q_table = make_cdf_and_quantile(grid, up_density)
    up_positive = up_density[grid >= 0.0]

    diagnostics: list[str] = []
    diagnostics.append("Exact moments of X (the Fabius probability law):")
    for n in range(0, 11):
        diagnostics.append(f"  E[X^{n}] = {fraction_string(x_moments[n])}")
    diagnostics.append("")
    diagnostics.append("Exact even moments of Y=2X-1 (density up):")
    for n in range(0, 11, 2):
        diagnostics.append(f"  E[Y^{n}] = {fraction_string(y_moments[n])}")
    diagnostics.append("")
    diagnostics.append("Exact Jacobi coefficients for the monic up-polynomials:")
    for n in range(1, jacobi_degree + 1):
        value = jacobi[n]
        assert isinstance(value, Fraction)
        diagnostics.append(
            f"  a_{n} = {fraction_string(value)} = {float(value):.15g}"
        )

    mass = trapezoid(up_density, grid)
    mean = trapezoid(grid * up_density, grid)
    variance = trapezoid(grid**2 * up_density, grid)
    symmetry_error = float(np.max(np.abs(up_density - up_density[::-1])))
    diagnostics.extend(
        [
            "",
            "Grid reconstruction diagnostics:",
            f"  points = {points}",
            f"  refinement iterations = {iterations}",
            f"  mass = {mass:.16e}",
            f"  mean = {mean:.16e}",
            f"  variance = {variance:.16e}",
            f"  exact variance = {float(Fraction(1, 9)):.16e}",
            f"  absolute variance error = {abs(variance - 1/9):.3e}",
            f"  max symmetry error = {symmetry_error:.3e}",
            f"  up(0) = {up_density[len(up_density)//2]:.16e}",
        ]
    )

    diagnostics.append("")
    diagnostics.append("Cauchy-transform equation S'(z)=2[S(2z+1)-S(2z-1)]:")
    for z in (1.4 + 0.7j, -1.6 + 1.1j, 0.3 + 1.8j):
        left = cauchy_derivative(z, grid, up_density)
        right = 2.0 * (
            cauchy_transform(2.0 * z + 1.0, grid, up_density)
            - cauchy_transform(2.0 * z - 1.0, grid, up_density)
        )
        diagnostics.append(
            f"  z={z!s:>12}: residual={abs(left-right):.3e}, "
            f"relative={abs(left-right)/max(abs(left),1e-30):.3e}"
        )

    diagnostics.append("")
    diagnostics.append(
        "Fractional refinement H_a(x)=2^{-a}[H_{a+1}(2x+1)-H_{a+1}(2x-1)]:"
    )
    for alpha, x0 in ((1.3, -0.21), (1.7, 0.18), (2.2, 0.42)):
        left = fractional_left_primitive(alpha, x0, grid, up_density)
        right = 2.0 ** (-alpha) * (
            fractional_left_primitive(alpha + 1.0, 2.0 * x0 + 1.0, grid, up_density)
            - fractional_left_primitive(alpha + 1.0, 2.0 * x0 - 1.0, grid, up_density)
        )
        diagnostics.append(
            f"  alpha={alpha:.1f}, x={x0:+.2f}: residual={abs(left-right):.3e}, "
            f"relative={abs(left-right)/max(abs(left),1e-30):.3e}"
        )

    diagnostics.append("")
    diagnostics.append("Quantile fractional-integral identity:")
    for alpha, u_value in ((0.75, 0.35), (1.4, 0.62), (2.25, 0.81)):
        lhs, rhs = quantile_fractional_identity(alpha, u_value, xp, f_grid, q_table)
        diagnostics.append(
            f"  alpha={alpha:.2f}, u={u_value:.2f}: lhs={lhs:.12e}, "
            f"rhs={rhs:.12e}, residual={abs(lhs-rhs):.3e}"
        )

    diagnostics.append("")
    diagnostics.append("Power integrals and order-statistic/quantile representation:")
    p_values = [1, 2, 3, 4, 8, 16, 32, 64, 128, 256]
    ratios: list[float] = []
    for p in p_values:
        direct = trapezoid(up_positive**p, xp)
        v = np.linspace(0.0, 1.0, points)
        qv = quantile(v, q_table)
        beta_form = trapezoid(p * qv * (1.0 - v) ** (p - 1), v)
        q_scale = float(quantile(1.0 / p, q_table)) if p > 1 else 1.0
        ratio = direct / q_scale if p > 1 and q_scale > 0 else float("nan")
        ratios.append(ratio)
        diagnostics.append(
            f"  p={p:3d}: int up^p={direct:.12e}, beta-quantile={beta_form:.12e}, "
            f"difference={abs(direct-beta_form):.3e}, ratio/Q(1/p)={ratio:.8f}"
        )

    # Check the exact integral moments of Q against Bernoulli/Bell moments.
    diagnostics.append("")
    diagnostics.append("Quantile moments int_0^1 Q(u)^n du = E[X^n]:")
    v = np.linspace(0.0, 1.0, points)
    qv = quantile(v, q_table)
    for n in range(1, 7):
        numeric = trapezoid(qv**n, v)
        exact = float(x_moments[n])
        diagnostics.append(
            f"  n={n}: numeric={numeric:.12e}, exact={exact:.12e}, "
            f"error={abs(numeric-exact):.3e}"
        )

    # Reflection X =_d 1-X gives the entire Newton interpolation
    #   E[X^s] = sum_{n>=0} (-1)^n binom(s,n) E[X^n].
    # The endpoint flatness makes the integer moments super-polynomially
    # small, so truncation at 160 terms is already useful even for s<0.
    diagnostics.append("")
    diagnostics.append("Generalized-moment Newton series:")
    x_law_grid = (grid + 1.0) / 2.0
    x_law_density = 2.0 * up_density
    for exponent in (-1.0, -0.5, 0.5, 1.5):
        coefficient = 1.0
        series_value = float(x_moments[0])
        for n in range(1, generalized_degree + 1):
            coefficient *= (n - 1.0 - exponent) / n
            series_value += coefficient * float(x_moments[n])
        integrand = np.zeros_like(x_law_grid)
        positive = x_law_grid > 0.0
        integrand[positive] = (x_law_grid[positive] ** exponent) * x_law_density[positive]
        numerical_value = trapezoid(integrand, x_law_grid)
        diagnostics.append(
            f"  s={exponent:+.1f}: Newton={series_value:.12e}, "
            f"density integral={numerical_value:.12e}, "
            f"difference={abs(series_value-numerical_value):.3e}"
        )

    logarithmic_series = sum(
        float(x_moments[n]) / n for n in range(1, generalized_degree + 1)
    )
    logarithmic_integrand = np.zeros_like(xp)
    positive_xp = xp > 0.0
    logarithmic_integrand[positive_xp] = f_grid[positive_xp] / xp[positive_xp]
    logarithmic_numeric = trapezoid(logarithmic_integrand, xp)
    diagnostics.append(
        "  int_0^1 F(x)/x dx = -m'(0): "
        f"series={logarithmic_series:.12e}, grid={logarithmic_numeric:.12e}, "
        f"difference={abs(logarithmic_series-logarithmic_numeric):.3e}"
    )

    (output_dir / "experiments_summary.txt").write_text(
        "\n".join(diagnostics) + "\n", encoding="utf-8"
    )

    # Figures use Matplotlib defaults intentionally: no hand-picked color/style.
    fig, ax = plt.subplots(figsize=(7.0, 4.2))
    ax.plot(grid, up_density, linewidth=1.4)
    ax.set_xlabel(r"$x$")
    ax.set_ylabel(r"$\operatorname{up}(x)$")
    ax.set_title("Numerical fixed-point reconstruction of Rvachev's up-function")
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(output_dir / "up_reconstruction.png", dpi=180)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(7.0, 4.2))
    n_axis = np.arange(1, jacobi_degree + 1)
    a_values = [float(jacobi[n]) for n in n_axis]
    ax.plot(n_axis, a_values, marker="o", linewidth=1.2)
    ax.axhline(0.25, linestyle="--", linewidth=1.0, label=r"Nevai limit $1/4$")
    ax.set_xlabel(r"$n$")
    ax.set_ylabel(r"$a_n$")
    ax.set_title("Jacobi coefficients of the up measure")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(output_dir / "jacobi_coefficients.png", dpi=180)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(7.0, 4.2))
    p_plot = np.array(p_values[1:], dtype=float)
    ratio_plot = np.array(ratios[1:], dtype=float)
    ax.semilogx(p_plot, ratio_plot, marker="o", linewidth=1.2)
    ax.axhline(1.0, linestyle="--", linewidth=1.0)
    ax.set_xlabel(r"$p$")
    ax.set_ylabel(r"$\int_0^1\!\operatorname{up}(x)^p\,dx\,/\,Q(1/p)$")
    ax.set_title("Power-integral scale predicted by the inverse Fabius function")
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(output_dir / "power_quantile_ratio.png", dpi=180)
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory for tables, figures, and the text summary",
    )
    parser.add_argument(
        "--points",
        type=int,
        default=65537,
        help="odd number of grid points on [-1,1]",
    )
    parser.add_argument(
        "--iterations",
        type=int,
        default=25,
        help="number of refinement-operator iterations",
    )
    parser.add_argument(
        "--jacobi-degree",
        type=int,
        default=12,
        help="maximum exact Jacobi coefficient",
    )
    args = parser.parse_args()
    run(args.output_dir, args.points, args.iterations, args.jacobi_degree)
