#!/usr/bin/env python3
"""Numerical checks for the derivative-norm and spectral-moment report.

This script reproduces all numerical tables and figures used in
``Fabius_Derivative_Norm_Spectrum.tex``.  It intentionally does not treat
floating-point evidence as proof: every central identity in the report is
proved analytically.  The computations serve four narrower purposes:

1. reconstruct Rvachev's up-function from its infinite sinc product;
2. verify the exact Thue--Morse derivative tiling and all-L^p norm law at
   machine precision;
3. test the Euler--Gamma differential-operator expansion that converts the
   inverse Fabius function into the large-p norm spectrum;
4. verify the shifted Stieltjes--Wigert moment and Hankel-determinant formulas.

Fourier normalization
---------------------
We use

    f_hat(xi) = integral f(x) exp(-2*pi*i*x*xi) dx,

so that

    Phi(xi) = product_{j>=0} sinc(pi*xi/2^j)
            = product_{j>=0} numpy.sinc(xi/2^j).

The inverse FFT is performed on a periodic box of length 4.  Since up is
supported on [-1,1], this leaves a full unit of zero padding on both sides and
prevents periodic wrap-around from contaminating the support.

Dependencies: numpy, scipy, sympy, matplotlib.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import matplotlib.pyplot as plt
# Embed TrueType outlines in generated PDF figures.  This avoids Type 3
# bitmap-like glyphs while preserving Matplotlib's default color cycle.
plt.rcParams["pdf.fonttype"] = 42
plt.rcParams["ps.fonttype"] = 42
import numpy as np
import sympy as sp
from scipy.interpolate import PchipInterpolator

EULER_GAMMA = 0.577215664901532860606512090082402431
ZETA_3 = 1.202056903159594285399738161511449991


@dataclass(frozen=True)
class UpGrid:
    """Uniform real-space and Fourier-space grids for the up-function."""

    x: np.ndarray
    up: np.ndarray
    frequency: np.ndarray
    phi: np.ndarray
    dx: float
    df: float


def reconstruct_up(grid_power: int = 19, sinc_factors: int = 55) -> UpGrid:
    """Reconstruct ``up`` by inverse FFT of the truncated sinc product.

    Parameters
    ----------
    grid_power:
        Number of samples is ``2**grid_power``.  The report uses 19.
    sinc_factors:
        Number of dyadic sinc factors.  Once ``j`` is well above the binary
        logarithm of the Nyquist frequency, omitted factors differ from 1 by
        much less than double precision.  The report uses 55.
    """

    sample_count = 2**grid_power
    box_length = 4.0
    dx = box_length / sample_count
    df = 1.0 / box_length

    frequency = np.fft.fftfreq(sample_count, d=dx)
    phi = np.ones(sample_count, dtype=np.float64)
    for j in range(sinc_factors):
        # numpy.sinc(t) = sin(pi*t)/(pi*t), exactly our normalized factor.
        phi *= np.sinc(frequency / (2.0**j))

    # For the stated Fourier convention, inverse Riemann summation is
    # ifft(phi)/dx.  fftshift centers x=0 in the array.
    up = np.fft.fftshift(np.fft.ifft(phi).real / dx)
    x = (np.arange(sample_count) - sample_count // 2) * dx

    # FFT roundoff produces values of order 1e-16 just outside [0,1].
    up = np.clip(up, 0.0, 1.0)
    return UpGrid(x=x, up=up, frequency=frequency, phi=phi, dx=dx, df=df)


def thue_morse_sign(indices: np.ndarray) -> np.ndarray:
    """Return (-1)^s_2(k) for every integer in ``indices``."""

    # Python's integer.bit_count is exact and avoids floating logarithms.
    return np.fromiter(
        (1.0 if int(k).bit_count() % 2 == 0 else -1.0 for k in indices),
        dtype=np.float64,
        count=len(indices),
    )


def support_grid(grid: UpGrid) -> tuple[np.ndarray, np.ndarray]:
    """Extract samples on the exact support [-1,1]."""

    mask = (grid.x >= -1.0) & (grid.x <= 1.0)
    return grid.x[mask], grid.up[mask]


def derivative_from_tiling(
    x: np.ndarray, base_interpolant: PchipInterpolator, order: int
) -> np.ndarray:
    r"""Evaluate the exact cell-tiling formula for ``up^(order)``.

    The analytic formula is

      up^(n)(x) = 2^(n(n+1)/2) sum_{k=0}^{2^n-1}
                  eps_k up(2^n x + 2^n - 1 - 2k).

    Exactly one summand is nonzero in the interior of each dyadic cell.
    We exploit that fact rather than summing all cells.
    """

    if order == 0:
        return base_interpolant(x)

    cell_count = 2**order
    cell_index = np.floor((x + 1.0) * cell_count / 2.0).astype(np.int64)
    cell_index = np.clip(cell_index, 0, cell_count - 1)
    local_coordinate = (
        (2.0**order) * x + (2.0**order) - 1.0 - 2.0 * cell_index
    )
    local_coordinate = np.clip(local_coordinate, -1.0, 1.0)

    scale = 2.0 ** (order * (order + 1) / 2.0)
    return (
        scale
        * thue_morse_sign(cell_index)
        * base_interpolant(local_coordinate)
    )


def lp_norm(values: np.ndarray, dx: float, p: float) -> float:
    """Discrete L^p norm on the support; ``p=inf`` is supported."""

    if math.isinf(p):
        return float(np.max(np.abs(values)))
    return float(np.sum(np.abs(values) ** p) * dx) ** (1.0 / p)


def build_inverse_interpolant(grid: UpGrid) -> PchipInterpolator:
    r"""Build a monotone interpolant for G=F^{-1} on the useful range.

    On 0 <= x <= 1, symmetry gives up(x)=1-F(x), hence the pairs
    ``(1-up(x), x)`` sample the inverse Fabius function directly.  Repeated
    values caused by roundoff in the extremely flat endpoint region are
    removed before constructing a shape-preserving PCHIP interpolant.
    """

    positive_mask = (grid.x >= 0.0) & (grid.x <= 1.0)
    x_positive = grid.x[positive_mask]
    y = 1.0 - grid.up[positive_mask]

    # Keep only numerically distinct ordinates.  The threshold is far below
    # any y=1/p used in the report.
    keep = np.concatenate(([True], np.diff(y) > 5.0e-16))
    return PchipInterpolator(y[keep], x_positive[keep], extrapolate=False)


def logarithmic_derivatives(
    inverse: PchipInterpolator, y: float, step: float = 0.005
) -> tuple[float, float, float, float]:
    r"""Estimate G, D G, D^2 G, D^3 G for D=y*d/dy.

    Writing t=log y turns D into ordinary differentiation with respect to t.
    Centered finite differences are therefore taken at y*exp(k*step).
    """

    gm2 = float(inverse(y * math.exp(-2.0 * step)))
    gm1 = float(inverse(y * math.exp(-step)))
    g0 = float(inverse(y))
    gp1 = float(inverse(y * math.exp(step)))
    gp2 = float(inverse(y * math.exp(2.0 * step)))

    d1 = (gp1 - gm1) / (2.0 * step)
    d2 = (gp1 - 2.0 * g0 + gm1) / (step**2)
    d3 = (gp2 - 2.0 * gp1 + 2.0 * gm1 - gm2) / (2.0 * step**3)
    return g0, d1, d2, d3


def stable_half_power_integral(up: np.ndarray, dx: float, p: int) -> float:
    """Return (1/2)*integral up(x)^p dx without spurious underflow warnings."""

    safe = np.maximum(up, 1.0e-300)
    return 0.5 * float(np.sum(np.exp(p * np.log(safe))) * dx)


def write_csv(path: Path, fieldnames: list[str], rows: Iterable[dict[str, object]]) -> None:
    """Write a deterministic UTF-8 CSV file."""

    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def derivative_norm_table(grid: UpGrid, output_dir: Path, max_order: int) -> list[dict[str, object]]:
    """Check the exact all-L^p norm scaling numerically."""

    x, up = support_grid(grid)
    interpolant = PchipInterpolator(x, up)
    p_values = [1.0, 2.0, 4.0, 8.0, math.inf]
    base_norms = {p: lp_norm(up, grid.dx, p) for p in p_values}

    rows: list[dict[str, object]] = []
    for order in range(max_order + 1):
        derivative = derivative_from_tiling(x, interpolant, order)
        scale = 2.0 ** (order * (order + 1) / 2.0)
        for p in p_values:
            ratio = lp_norm(derivative, grid.dx, p) / (scale * base_norms[p])
            rows.append(
                {
                    "order": order,
                    "p": "inf" if math.isinf(p) else int(p),
                    "computed_ratio": f"{ratio:.17g}",
                    "absolute_error_from_1": f"{abs(ratio - 1.0):.3e}",
                }
            )

    write_csv(
        output_dir / "derivative_norm_ratios.csv",
        ["order", "p", "computed_ratio", "absolute_error_from_1"],
        rows,
    )
    return rows


def spectral_moment_table(grid: UpGrid, output_dir: Path, max_order: int = 7) -> list[dict[str, object]]:
    """Check Parseval's exact shifted Stieltjes--Wigert moments."""

    x, up = support_grid(grid)
    up_l2_squared = float(np.sum(up * up) * grid.dx)
    rows: list[dict[str, object]] = []
    for order in range(max_order + 1):
        computed = float(
            np.sum(
                (2.0 * math.pi * grid.frequency) ** (2 * order)
                * grid.phi
                * grid.phi
            )
            * grid.df
        )
        exact = (2.0 ** (order * (order + 1))) * up_l2_squared
        rows.append(
            {
                "order": order,
                "computed_moment": f"{computed:.17g}",
                "predicted_moment": f"{exact:.17g}",
                "relative_error": f"{computed / exact - 1.0:.3e}",
            }
        )

    write_csv(
        output_dir / "spectral_moment_checks.csv",
        ["order", "computed_moment", "predicted_moment", "relative_error"],
        rows,
    )
    return rows


def beta_operator_table(grid: UpGrid, output_dir: Path) -> list[dict[str, object]]:
    r"""Test the Gamma(D+1) expansion of the inverse-Fabius beta transform.

    Put A_p=(1/2)||up||_p^p.  The report proves

      A_p = G(1/p) - gamma D G(1/p)
            + (gamma^2+pi^2/6)/2 D^2 G(1/p)
            - (gamma^3+gamma*pi^2/2+2*zeta(3))/6 D^3 G(1/p) + ... .

    The table compares successive truncations.  D-derivatives are estimated
    from the monotone inverse interpolant on a logarithmic stencil.
    """

    inverse = build_inverse_interpolant(grid)
    mu2 = EULER_GAMMA**2 + math.pi**2 / 6.0
    mu3 = -(
        EULER_GAMMA**3
        + EULER_GAMMA * math.pi**2 / 2.0
        + 2.0 * ZETA_3
    )

    p_values = [2**k for k in range(8, 17)]
    rows: list[dict[str, object]] = []
    for p in p_values:
        a_exact = stable_half_power_integral(grid.up, grid.dx, p)
        g0, d1, d2, d3 = logarithmic_derivatives(inverse, 1.0 / p)
        approximation_0 = g0
        approximation_1 = approximation_0 - EULER_GAMMA * d1
        approximation_2 = approximation_1 + 0.5 * mu2 * d2
        approximation_3 = approximation_2 + (mu3 / 6.0) * d3

        rows.append(
            {
                "p": p,
                "G(1/p)": f"{g0:.15g}",
                "A_p/G": f"{a_exact / g0:.12g}",
                "relative_error_order_0": f"{a_exact / approximation_0 - 1.0:.6e}",
                "relative_error_order_1": f"{a_exact / approximation_1 - 1.0:.6e}",
                "relative_error_order_2": f"{a_exact / approximation_2 - 1.0:.6e}",
                "relative_error_order_3": f"{a_exact / approximation_3 - 1.0:.6e}",
            }
        )

    write_csv(
        output_dir / "beta_operator_checks.csv",
        [
            "p",
            "G(1/p)",
            "A_p/G",
            "relative_error_order_0",
            "relative_error_order_1",
            "relative_error_order_2",
            "relative_error_order_3",
        ],
        rows,
    )
    return rows


def hankel_determinant_table(output_dir: Path, max_size: int = 6) -> list[dict[str, object]]:
    """Verify the exact q=1/4 Hankel determinant identity symbolically."""

    q = sp.Rational(1, 4)
    rows: list[dict[str, object]] = []
    for n in range(max_size + 1):
        matrix = sp.Matrix(
            [
                [
                    q ** (-sp.Rational((i + j) * (i + j + 1), 2))
                    for j in range(n + 1)
                ]
                for i in range(n + 1)
            ]
        )
        determinant = sp.factor(matrix.det())
        closed_form = q ** (-sp.Rational(n * (n + 1) * (4 * n + 5), 6))
        closed_form *= sp.prod(
            sp.prod(1 - q**r for r in range(1, k + 1))
            for k in range(1, n + 1)
        )
        quotient = sp.simplify(determinant / closed_form)
        rows.append(
            {
                "N": n,
                "determinant_equals_closed_form": str(quotient == 1),
                "quotient": str(quotient),
                "decimal_log10_determinant": (
                    "0" if n == 0 else f"{float(sp.log(determinant, 10).evalf()):.8f}"
                ),
            }
        )

    write_csv(
        output_dir / "hankel_determinant_checks.csv",
        ["N", "determinant_equals_closed_form", "quotient", "decimal_log10_determinant"],
        rows,
    )
    return rows


def plot_derivative_tiling(grid: UpGrid, figure_dir: Path, max_order: int = 4) -> None:
    """Plot normalized derivatives, exposing their Thue--Morse cell signs."""

    x, up = support_grid(grid)
    interpolant = PchipInterpolator(x, up)

    fig, ax = plt.subplots(figsize=(8.8, 4.8))
    for order in range(max_order + 1):
        derivative = derivative_from_tiling(x, interpolant, order)
        scale = 2.0 ** (order * (order + 1) / 2.0)
        # Offset the curves vertically so all tilings remain readable.
        ax.plot(x, derivative / scale + 2.15 * order, linewidth=0.9, label=f"n={order}")
    ax.set_xlabel("x")
    ax.set_ylabel(r"$2^{-n(n+1)/2}\,\mathrm{up}^{(n)}(x)$ (vertically offset)")
    ax.set_title("Exact derivative tiling: copies of up with Thue--Morse signs")
    ax.legend(ncol=max_order + 1, loc="upper center", fontsize=8)
    ax.grid(True, linewidth=0.3, alpha=0.5)
    fig.tight_layout()
    fig.savefig(figure_dir / "derivative_tiling.pdf")
    fig.savefig(figure_dir / "derivative_tiling.png", dpi=180)
    plt.close(fig)


def plot_beta_errors(rows: list[dict[str, object]], figure_dir: Path) -> None:
    """Plot convergence of successive Euler--Gamma operator truncations."""

    p_values = np.array([int(row["p"]) for row in rows], dtype=float)
    fig, ax = plt.subplots(figsize=(7.7, 4.6))
    for order in range(4):
        key = f"relative_error_order_{order}"
        errors = np.abs(np.array([float(row[key]) for row in rows]))
        ax.loglog(p_values, errors, marker="o", linewidth=1.0, label=f"through D^{order}")
    ax.set_xlabel("p")
    ax.set_ylabel("absolute relative error")
    ax.set_title("Inverse-Fabius beta transform: Euler--Gamma operator truncations")
    ax.grid(True, which="both", linewidth=0.3, alpha=0.5)
    ax.legend()
    fig.tight_layout()
    fig.savefig(figure_dir / "beta_operator_errors.pdf")
    fig.savefig(figure_dir / "beta_operator_errors.png", dpi=180)
    plt.close(fig)


def plot_spectral_measures(grid: UpGrid, figure_dir: Path) -> None:
    r"""Compare the sinc-square spectral density with its lognormal moment twin.

    The two curves have exactly the same nonnegative integer moments after the
    change z=(2*pi*xi)^2, but are visibly different and therefore demonstrate
    moment indeterminacy.  The plot uses a logarithmic z-axis and omits z=0.
    """

    x, up = support_grid(grid)
    l2_squared = float(np.sum(up * up) * grid.dx)
    log_two = math.log(2.0)

    z = np.logspace(-3.0, 5.0, 3000)
    xi = np.sqrt(z) / (2.0 * math.pi)

    # Evaluate Phi directly.  A vectorized product is stable on this range.
    phi = np.ones_like(xi)
    for j in range(45):
        phi *= np.sinc(xi / (2.0**j))
    spectral_density = phi * phi / (2.0 * math.pi * l2_squared * np.sqrt(z))
    lognormal_density = np.exp(-((np.log(z) - log_two) ** 2) / (4.0 * log_two))
    lognormal_density /= z * math.sqrt(4.0 * math.pi * log_two)

    fig, ax = plt.subplots(figsize=(8.0, 4.7))
    ax.loglog(z, spectral_density, linewidth=1.0, label="sinc-square spectral measure")
    ax.loglog(z, lognormal_density, linewidth=1.0, label="lognormal representing measure")
    ax.set_xlabel("z")
    ax.set_ylabel("density")
    ax.set_title("Distinct measures with moments 2^{n(n+1)}")
    ax.grid(True, which="both", linewidth=0.3, alpha=0.5)
    ax.legend()
    fig.tight_layout()
    fig.savefig(figure_dir / "spectral_vs_lognormal.pdf")
    fig.savefig(figure_dir / "spectral_vs_lognormal.png", dpi=180)
    plt.close(fig)


def write_summary(
    grid: UpGrid,
    derivative_rows: list[dict[str, object]],
    spectral_rows: list[dict[str, object]],
    beta_rows: list[dict[str, object]],
    hankel_rows: list[dict[str, object]],
    output_dir: Path,
) -> None:
    """Write a plain-text run summary useful for reproducibility audits."""

    x, up = support_grid(grid)
    support_leakage = float(np.max(np.abs(grid.up[np.abs(grid.x) > 1.0001])))
    normalization = float(np.sum(grid.up) * grid.dx)
    l2_squared = float(np.sum(up * up) * grid.dx)
    max_norm_error = max(float(row["absolute_error_from_1"]) for row in derivative_rows)
    max_spectral_error = max(abs(float(row["relative_error"])) for row in spectral_rows)

    lines = [
        "Numerical experiment summary",
        "============================",
        f"sample_count = {len(grid.x)}",
        f"dx = {grid.dx:.17g}",
        f"df = {grid.df:.17g}",
        f"integral(up) = {normalization:.17g}",
        f"up(0) = {grid.up[len(grid.up)//2]:.17g}",
        f"max support leakage = {support_leakage:.3e}",
        f"||up||_2^2 = {l2_squared:.17g}",
        f"max derivative norm-ratio error = {max_norm_error:.3e}",
        f"max spectral-moment relative error = {max_spectral_error:.3e}",
        f"beta rows = {len(beta_rows)}",
        f"symbolic Hankel checks = {len(hankel_rows)}",
        "",
        "All central statements are proved in the report; these numbers are checks only.",
    ]
    (output_dir / "run_summary.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--grid-power", type=int, default=19)
    parser.add_argument("--sinc-factors", type=int, default=55)
    parser.add_argument("--max-derivative", type=int, default=6)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="Directory containing figures/ and data/ subdirectories.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    figure_dir = args.output_dir / "figures"
    data_dir = args.output_dir / "data"
    figure_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)

    grid = reconstruct_up(args.grid_power, args.sinc_factors)
    derivative_rows = derivative_norm_table(grid, data_dir, args.max_derivative)
    spectral_rows = spectral_moment_table(grid, data_dir)
    beta_rows = beta_operator_table(grid, data_dir)
    hankel_rows = hankel_determinant_table(data_dir)

    plot_derivative_tiling(grid, figure_dir)
    plot_beta_errors(beta_rows, figure_dir)
    plot_spectral_measures(grid, figure_dir)
    write_summary(
        grid,
        derivative_rows,
        spectral_rows,
        beta_rows,
        hankel_rows,
        data_dir,
    )

    print((data_dir / "run_summary.txt").read_text(encoding="utf-8"))


if __name__ == "__main__":
    main()
