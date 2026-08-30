#!/usr/bin/env python3
"""Numerical experiments for finite dyadic sinc products.

The angular-frequency Fourier convention is

    Phi(xi) = integral_R u(x) exp(-i xi x) dx,

and

    Phi_N(xi) = product_{j=1}^N sinc(xi / 2^j),
    sinc(t) = sin(t) / t.

The inverse transform u_N is the density of

    X_N = sum_{j=1}^N 2^{-j} V_j,   V_j ~ Uniform[-1, 1].

The limiting density u is Rvachev's up-function.  On [-1,1], both u and
u_N equal their period-two Fourier series, whose coefficients are
(1/2) Phi(pi*n) and (1/2) Phi_N(pi*n).  This gives a stable and very fast
FFT reconstruction.  The program:

* verifies the exact W_1, Kolmogorov, total-variation, stop-loss, and
  Zolotarev formulas from the report;
* checks the scaled physical-space expansion
      4^N (u_N-u) -> -u''/18;
* checks the scaled stop-loss expansion
      4^N K_N -> u/18;
* measures entropy, Fisher information, forward KL divergence, and W_2,
  providing evidence for the information/transport conjectures;
* writes CSV data, LaTeX table fragments, and publication-quality figures.

No network access and no hidden input files are used.

Typical use:

    python finite_sinc_experiments.py --output . --grid-power 18

Dependencies: NumPy, SciPy, Matplotlib.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import cumulative_trapezoid


@dataclass(frozen=True)
class FourierGrid:
    """Period-two FFT grid and its integer Fourier modes."""

    size: int
    x: np.ndarray
    dx: float
    modes: np.ndarray
    phase: np.ndarray

    @staticmethod
    def create(grid_power: int) -> "FourierGrid":  # noqa: D401
        """Create M=2**grid_power samples x_k=-1+2k/M."""
        if grid_power < 14:
            raise ValueError("grid_power should be at least 14")
        size = 1 << grid_power
        x = -1.0 + 2.0 * np.arange(size, dtype=float) / size
        dx = 2.0 / size
        # np.fft.fftfreq(M, d=1/M) gives the signed integer modes.
        modes = np.fft.fftfreq(size, d=1.0 / size).astype(np.int64)
        # At x_k=-1+2k/M, exp(i*pi*n*x_k)=(-1)^n exp(2*pi*i*n*k/M).
        phase = np.where(np.abs(modes) % 2 == 0, 1.0, -1.0)
        return FourierGrid(size=size, x=x, dx=dx, modes=modes, phase=phase)


def sinc_product_on_integer_lattice(
    grid: FourierGrid, stage: int | None, infinite_factors: int = 52
) -> np.ndarray:
    """Return Phi_N(pi*n), or Phi(pi*n) when stage is None.

    NumPy's normalized sinc is np.sinc(y)=sin(pi*y)/(pi*y), hence the
    j-th factor at xi=pi*n is np.sinc(n/2**j).  For the infinite product,
    52 factors make the omitted logarithmic tail much smaller than double
    precision on the grid sizes used here.  Every nonzero even integer is
    an exact zero of Phi; it is set to zero explicitly to avoid residual
    argument-reduction noise.
    """

    factors = infinite_factors if stage is None else stage
    if factors < 1:
        raise ValueError("stage must be a positive integer")

    values = np.ones(grid.size, dtype=float)
    for j in range(1, factors + 1):
        values *= np.sinc(grid.modes / (2.0**j))

    if stage is None:
        even_nonzero = (grid.modes != 0) & (np.abs(grid.modes) % 2 == 0)
        values[even_nonzero] = 0.0
    return values


def reconstruct_period_two(
    grid: FourierGrid, coefficients: np.ndarray, derivative_order: int = 0
) -> np.ndarray:
    """Reconstruct a function or derivative from Phi(pi*n).

    For a density f supported in [-1,1], the period-two Fourier series is

        f(x) = (1/2) sum_{n in Z} Phi(pi*n) exp(i*pi*n*x).

    Multiplication by (i*pi*n)^r differentiates r times.  The factor M is
    needed because NumPy's inverse FFT includes 1/M.
    """

    multiplier = (1j * math.pi * grid.modes) ** derivative_order
    spectrum = (
        grid.size
        * 0.5
        * coefficients
        * multiplier
        * grid.phase
    )
    return np.fft.ifft(spectrum).real


def normalize_nonnegative_density(values: np.ndarray, dx: float) -> np.ndarray:
    """Remove roundoff-level negative values and renormalize to unit mass."""

    result = np.maximum(values, 0.0)
    mass = float(result.sum() * dx)
    if not math.isfinite(mass) or mass <= 0.0:
        raise RuntimeError("density reconstruction has invalid mass")
    return result / mass


def cdf_from_density(grid: FourierGrid, density: np.ndarray) -> np.ndarray:
    """Cumulative trapezoidal integral, normalized and made monotone."""

    cdf = np.concatenate(
        ([0.0], cumulative_trapezoid(density, grid.x))
    )[: grid.size]
    cdf = np.maximum.accumulate(cdf)
    if cdf[-1] <= 0.0:
        raise RuntimeError("CDF reconstruction has zero mass")
    cdf /= cdf[-1]
    return np.clip(cdf, 0.0, 1.0)


def cumulative_integral(grid: FourierGrid, values: np.ndarray) -> np.ndarray:
    """Integral from -1 to x on the FFT grid."""

    return np.concatenate(
        ([0.0], cumulative_trapezoid(values, grid.x))
    )[: grid.size]


def inverse_cdf_data(grid: FourierGrid, cdf: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Compress flat roundoff plateaus into data suitable for np.interp."""

    monotone = np.maximum.accumulate(cdf)
    keep = np.concatenate(([True], np.diff(monotone) > 1.0e-15))
    return monotone[keep], grid.x[keep]


def exact_metric_values(stage: int) -> dict[str, float]:
    """Exact formulas proved in the report.

    The first-stage Kolmogorov/TV constants are exceptional because X_1 is
    a single uniform box.  All other displayed formulas hold for every
    stage >= 1.
    """

    eps2 = 4.0 ** (-stage)
    w1 = eps2 / 9.0
    stop_loss = eps2 / 18.0
    if stage == 1:
        kolmogorov = 5.0 / 72.0
        l1_density = 5.0 / 18.0
    else:
        kolmogorov = eps2 / 9.0
        l1_density = 4.0 * eps2 / 9.0
    return {
        "W1": w1,
        "Kolmogorov": kolmogorov,
        "L1_density": l1_density,
        "TV": 0.5 * l1_density,
        "stop_loss": stop_loss,
        "Zolotarev2": stop_loss,
        "Winfinity": 2.0 ** (-stage),
    }


def entropy(density: np.ndarray, dx: float) -> float:
    """Differential entropy -integral f log f, with 0 log 0 = 0."""

    mask = density > 1.0e-280
    return float(-np.sum(density[mask] * np.log(density[mask])) * dx)


def fisher_information(
    density: np.ndarray, derivative: np.ndarray, dx: float, threshold: float = 1.0e-250
) -> float:
    """Compute integral f'^2/f where f is numerically resolved."""

    mask = density > threshold
    return float(np.sum(derivative[mask] ** 2 / density[mask]) * dx)


def forward_kl(
    approximant: np.ndarray, limit: np.ndarray, dx: float
) -> float:
    """D(approximant || limit); the reverse divergence is exactly infinite."""

    mask = (approximant > 1.0e-280) & (limit > 1.0e-280)
    return float(
        np.sum(approximant[mask] * np.log(approximant[mask] / limit[mask])) * dx
    )


def write_csv(path: Path, fieldnames: Sequence[str], rows: Iterable[dict[str, object]]) -> None:
    """Write dictionaries to CSV with a stable column order."""

    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def scientific(value: float, digits: int = 6) -> str:
    """Compact LaTeX-ready scientific notation."""

    if value == 0.0:
        return "0"
    exponent = int(math.floor(math.log10(abs(value))))
    mantissa = value / (10.0**exponent)
    return rf"{mantissa:.{digits}f}\times10^{{{exponent}}}"


def write_metric_tex(path: Path, rows: Sequence[dict[str, float]]) -> None:
    """Write rows for the exact-metric verification table."""

    with path.open("w", encoding="utf-8") as stream:
        for row in rows:
            stream.write(
                f"{int(row['N'])} & "
                f"${scientific(row['W1_numeric'])}$ & "
                f"${scientific(row['W1_exact'])}$ & "
                f"${row['W1_rel_error']:.2e}$ & "
                f"${scientific(row['K_numeric'])}$ & "
                f"${scientific(row['K_exact'])}$ & "
                f"${row['K_rel_error']:.2e}$ \\\\\n"
            )


def write_information_tex(path: Path, rows: Sequence[dict[str, float]]) -> None:
    """Write rows for entropy, KL, and W2 asymptotic ratios."""

    with path.open("w", encoding="utf-8") as stream:
        for row in rows:
            stream.write(
                f"{int(row['N'])} & "
                f"${scientific(row['entropy_gap'])}$ & "
                f"${row['entropy_ratio']:.8f}$ & "
                f"${scientific(row['forward_KL'])}$ & "
                f"${row['KL_ratio']:.8f}$ & "
                f"${scientific(row['W2'])}$ & "
                f"${row['W2_ratio']:.8f}$ \\\\\n"
            )


def save_figure(fig: plt.Figure, base: Path) -> None:
    """Save both vector PDF and a PNG preview."""

    fig.savefig(base.with_suffix(".pdf"), bbox_inches="tight")
    fig.savefig(base.with_suffix(".png"), dpi=180, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="report directory containing figures/ and data/",
    )
    parser.add_argument(
        "--grid-power",
        type=int,
        default=18,
        help="use M=2**grid_power period-two samples (default: 18)",
    )
    parser.add_argument(
        "--max-stage",
        type=int,
        default=10,
        help="largest finite product stage in tables (default: 10)",
    )
    args = parser.parse_args()

    output = args.output.resolve()
    figures = output / "figures"
    data = output / "data"
    figures.mkdir(parents=True, exist_ok=True)
    data.mkdir(parents=True, exist_ok=True)

    grid = FourierGrid.create(args.grid_power)
    phi = sinc_product_on_integer_lattice(grid, stage=None)
    up_raw = reconstruct_period_two(grid, phi, derivative_order=0)
    up = normalize_nonnegative_density(up_raw, grid.dx)
    up_prime = reconstruct_period_two(grid, phi, derivative_order=1)
    up_second = reconstruct_period_two(grid, phi, derivative_order=2)
    cdf = cdf_from_density(grid, up)

    # Reference constants used by the information/transport conjectures.
    h_limit = entropy(up, grid.dx)
    fisher_limit = fisher_information(up, up_prime, grid.dx)
    curvature_information = fisher_information(up, up_second, grid.dx)

    # The exact identities int |u'|=2 and int |u''|=8 are useful numerical
    # diagnostics.  A substantial deviation indicates insufficient resolution.
    diagnostic = {
        "mass": float(up.sum() * grid.dx),
        "maximum": float(up.max()),
        "L1_first_derivative": float(np.sum(np.abs(up_prime)) * grid.dx),
        "L1_second_derivative": float(np.sum(np.abs(up_second)) * grid.dx),
        "entropy": h_limit,
        "Fisher_information": fisher_limit,
        "curvature_information": curvature_information,
    }

    reconstructed: dict[int, tuple[np.ndarray, np.ndarray, np.ndarray]] = {}
    metric_rows: list[dict[str, float]] = []
    information_rows: list[dict[str, float]] = []

    # Inverse-CDF data for the monotone one-dimensional optimal transport map.
    for stage in range(1, args.max_stage + 1):
        phi_n = sinc_product_on_integer_lattice(grid, stage=stage)
        raw_n = reconstruct_period_two(grid, phi_n, derivative_order=0)
        # Stage 1 has a jump and therefore visible Fourier Gibbs oscillations.
        # It is retained for exact formulas but omitted from numerical density
        # norms.  Stages >=2 are accurately reconstructed on this fine grid.
        density_n = normalize_nonnegative_density(raw_n, grid.dx)
        derivative_n = reconstruct_period_two(grid, phi_n, derivative_order=1)
        cdf_n = cdf_from_density(grid, density_n)
        reconstructed[stage] = (density_n, derivative_n, cdf_n)

        exact = exact_metric_values(stage)
        cdf_error = cdf_n - cdf
        w1_numeric = float(np.sum(np.abs(cdf_error)) * grid.dx)
        k_numeric = float(np.max(cumulative_integral(grid, cdf - cdf_n)))

        metric_row = {
            "N": float(stage),
            "W1_numeric": w1_numeric,
            "W1_exact": exact["W1"],
            "W1_rel_error": abs(w1_numeric / exact["W1"] - 1.0),
            "Kolmogorov_numeric": float(np.max(np.abs(cdf_error))),
            "Kolmogorov_exact": exact["Kolmogorov"],
            "L1_density_numeric": float(np.sum(np.abs(density_n - up)) * grid.dx),
            "L1_density_exact": exact["L1_density"],
            "K_numeric": k_numeric,
            "K_exact": exact["stop_loss"],
            "K_rel_error": abs(k_numeric / exact["stop_loss"] - 1.0),
            "Zolotarev_numeric": float(
                np.sum(cumulative_integral(grid, cdf - cdf_n)) * grid.dx
            ),
            "Zolotarev_exact": exact["Zolotarev2"],
            "Winfinity_exact": exact["Winfinity"],
        }
        metric_rows.append(metric_row)

        if stage >= 3:
            h_n = entropy(density_n, grid.dx)
            entropy_gap = h_limit - h_n
            entropy_prediction = (4.0 ** (-stage) / 18.0) * fisher_limit
            kl = forward_kl(density_n, up, grid.dx)
            kl_prediction = (
                16.0 ** (-stage) * curvature_information / 648.0
            )

            # Compute W2 through the monotone rearrangement T_N=Q_N o H.
            h_values, x_values = inverse_cdf_data(grid, cdf_n)
            transport = np.interp(cdf, h_values, x_values)
            w2 = float(
                math.sqrt(
                    np.sum((transport - grid.x) ** 2 * up) * grid.dx
                )
            )
            w2_prediction = (
                4.0 ** (-stage) * math.sqrt(fisher_limit) / 18.0
            )

            support = 1.0 - 2.0 ** (-stage)
            fisher_mask = (
                (np.abs(grid.x) < support - 10.0 * grid.dx)
                & (density_n > 1.0e-20)
            )
            fisher_n = float(
                np.sum(
                    derivative_n[fisher_mask] ** 2
                    / density_n[fisher_mask]
                )
                * grid.dx
            )

            information_rows.append(
                {
                    "N": float(stage),
                    "entropy_gap": entropy_gap,
                    "entropy_prediction": entropy_prediction,
                    "entropy_ratio": entropy_gap / entropy_prediction,
                    "forward_KL": kl,
                    "KL_prediction": kl_prediction,
                    "KL_ratio": kl / kl_prediction,
                    "W2": w2,
                    "W2_prediction": w2_prediction,
                    "W2_ratio": w2 / w2_prediction,
                    "Fisher_N": fisher_n,
                    "Fisher_limit": fisher_limit,
                }
            )

    # CSV files contain more digits than the typeset tables.
    write_csv(
        data / "metric_verification.csv",
        list(metric_rows[0].keys()),
        metric_rows,
    )
    write_csv(
        data / "information_transport.csv",
        list(information_rows[0].keys()),
        information_rows,
    )
    write_csv(
        data / "reference_constants.csv",
        ["quantity", "value"],
        ({"quantity": key, "value": value} for key, value in diagnostic.items()),
    )
    write_metric_tex(data / "metric_table_rows.tex", metric_rows[1:])
    write_information_tex(data / "information_table_rows.tex", information_rows)

    # Figure 1: the finite inverse transforms as splines.
    fig, ax = plt.subplots(figsize=(7.2, 4.4))
    for stage in (2, 3, 4, 6):
        ax.plot(grid.x, reconstructed[stage][0], label=rf"$u_{{{stage}}}$")
    ax.plot(grid.x, up, linewidth=2.0, label=r"$u=\operatorname{up}$")
    ax.set_xlim(-1.02, 1.02)
    ax.set_ylim(-0.02, 1.05)
    ax.set_xlabel(r"$x$")
    ax.set_ylabel("density")
    ax.set_title("Inverse transforms of finite dyadic sinc products")
    ax.legend(ncol=3)
    ax.grid(True, alpha=0.25)
    save_figure(fig, figures / "finite_spline_approximants")

    # Figure 2: leading all-orders physical-space term.
    fig, ax = plt.subplots(figsize=(7.2, 4.4))
    for stage in (4, 6, 8):
        scaled = (4.0**stage) * (reconstructed[stage][0] - up)
        ax.plot(grid.x, scaled, label=rf"$4^{{{stage}}}(u_{{{stage}}}-u)$")
    ax.plot(grid.x, -up_second / 18.0, linestyle="--", linewidth=2.0, label=r"$-u''/18$")
    ax.set_xlim(-0.98, 0.98)
    ax.set_xlabel(r"$x$")
    ax.set_ylabel("scaled error")
    ax.set_title("Leading physical-space deconvolution error")
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.25)
    save_figure(fig, figures / "scaled_density_error")

    # Figure 3: stop-loss potential and its leading term.
    fig, ax = plt.subplots(figsize=(7.2, 4.4))
    for stage in (3, 5, 7):
        cdf_n = reconstructed[stage][2]
        potential = cumulative_integral(grid, cdf - cdf_n)
        ax.plot(grid.x, (4.0**stage) * potential, label=rf"$4^{{{stage}}}K_{{{stage}}}$")
    ax.plot(grid.x, up / 18.0, linestyle="--", linewidth=2.0, label=r"$u/18$")
    ax.set_xlim(-1.0, 1.0)
    ax.set_xlabel(r"threshold $t$")
    ax.set_ylabel("scaled stop-loss gap")
    ax.set_title("Stop-loss potential: exact height and asymptotic profile")
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.25)
    save_figure(fig, figures / "scaled_stop_loss")

    # Figure 4: exact metric collapse.  Curves are offset only where their
    # constants differ; all have slope log(1/4) per stage.
    stages = np.array([int(row["N"]) for row in metric_rows if row["N"] >= 2])
    eps2 = 4.0 ** (-stages)
    fig, ax = plt.subplots(figsize=(7.2, 4.4))
    ax.semilogy(stages, eps2 / 9.0, marker="o", label=r"$W_1=d_{\rm K}$")
    ax.semilogy(stages, 2.0 * eps2 / 9.0, marker="s", label=r"$d_{\rm TV}$")
    ax.semilogy(stages, eps2 / 18.0, marker="^", label=r"$d_{\rm SL}=\zeta_2$")
    ax.semilogy(stages, 2.0 ** (-stages), marker="d", label=r"$W_\infty$")
    ax.set_xlabel(r"number of sinc factors $N$")
    ax.set_ylabel("exact error")
    ax.set_title(r"Exact metric rates and the finite-$p$ / $p=\infty$ split")
    ax.legend()
    ax.grid(True, which="both", alpha=0.25)
    save_figure(fig, figures / "exact_metric_rates")

    # Figure 5: information and W2 ratios.  Values approaching one support the
    # weighted endpoint expansions formulated as conjectures in the report.
    stages_i = np.array([int(row["N"]) for row in information_rows])
    fig, ax = plt.subplots(figsize=(7.2, 4.4))
    ax.plot(stages_i, [row["entropy_ratio"] for row in information_rows], marker="o", label="entropy ratio")
    ax.plot(stages_i, [row["KL_ratio"] for row in information_rows], marker="s", label="forward-KL ratio")
    ax.plot(stages_i, [row["W2_ratio"] for row in information_rows], marker="^", label=r"$W_2$ ratio")
    ax.axhline(1.0, linestyle="--", linewidth=1.2)
    ax.set_xlabel(r"stage $N$")
    ax.set_ylabel("measured / predicted leading term")
    ax.set_title("Information and finite-$p$ transport asymptotics")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, figures / "information_transport_ratios")

    # Figure 6: monotone Fisher-information convergence (numerical).
    fig, ax = plt.subplots(figsize=(7.2, 4.4))
    ax.plot(stages_i, [row["Fisher_N"] for row in information_rows], marker="o", label=r"$I(u_N)$")
    ax.axhline(fisher_limit, linestyle="--", linewidth=1.5, label=r"$I(u)$")
    ax.set_xlabel(r"stage $N$")
    ax.set_ylabel("Fisher information")
    ax.set_title("Fisher information under successive uniform convolutions")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, figures / "fisher_information")

    # A compact human-readable log is convenient when inspecting the archive.
    with (data / "verification_log.txt").open("w", encoding="utf-8") as stream:
        stream.write(f"grid_size={grid.size}\n")
        for key, value in diagnostic.items():
            stream.write(f"{key}={value:.17g}\n")
        stream.write("\nmaximum_relative_errors_for_N_ge_2\n")
        rows_ge2 = metric_rows[1:]
        stream.write(
            "W1="
            + f"{max(row['W1_rel_error'] for row in rows_ge2):.6e}\n"
        )
        stream.write(
            "stop_loss="
            + f"{max(row['K_rel_error'] for row in rows_ge2):.6e}\n"
        )
        stream.write("\ninformation_ratios_at_last_stage\n")
        last = information_rows[-1]
        for key in ("entropy_ratio", "KL_ratio", "W2_ratio"):
            stream.write(f"{key}={last[key]:.12f}\n")

    print(f"Wrote data to {data}")
    print(f"Wrote figures to {figures}")
    print(
        "Reference constants: "
        f"h(u)={h_limit:.12f}, I(u)={fisher_limit:.12f}, "
        f"J_2(u)={curvature_information:.12f}"
    )


if __name__ == "__main__":
    main()
