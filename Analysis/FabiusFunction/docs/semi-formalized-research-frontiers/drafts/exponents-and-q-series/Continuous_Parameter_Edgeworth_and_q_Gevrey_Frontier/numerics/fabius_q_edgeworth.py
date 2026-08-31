#!/usr/bin/env python3
"""Numerical experiments for the geometric-uniform/Fabius q-family.

This script supports the report

    Continuous-Parameter Edgeworth Theory, Large Deviations, and
    Quadratic q-Gevrey Regularity at the Fabius--Rvachev Frontier.

It performs three independent checks.

1. It computes the exact standardized density of

       X_r = (1-r) * sum_{n>=0} r^n U_n,   U_n ~ Uniform(0,1),

   by FFT inversion of its infinite sinc-product characteristic function.
   It compares that density with the Gaussian and the first three explicit
   Edgeworth corrections in h=-log(r).

2. It numerically inverts the CDF and checks the first two central
   Cornish--Fisher corrections for the quantile function.

3. It evaluates the limiting compact-scale large-deviation rate function in
   its exact saddle parametrization and checks its Lambert-W support-edge
   asymptotic, including the renormalized Stieltjes-constant term.

The infinite product is truncated only after the largest remaining sinc
argument is below PRODUCT_TOL.  The FFT box is much wider than the support for
all default h values, and the density integral is reported as a diagnostic.
No random sampling is used, so all outputs are deterministic.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import Iterable

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
from scipy.integrate import cumulative_trapezoid
from scipy.special import eval_hermitenorm, ndtri


PRODUCT_TOL = 1.0e-14
DEFAULT_H = (0.30, 0.20, 0.15, 0.10, 0.07, 0.05)
DEFAULT_N = 2**15
DEFAULT_DX = 0.002


def normal_density(x: np.ndarray) -> np.ndarray:
    """Standard normal density."""
    return np.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)


def standardized_characteristic(t: np.ndarray, h: float) -> tuple[np.ndarray, int]:
    """Evaluate the exact standardized characteristic function.

    With r=exp(-h), the standardized variable Z_h has

        Psi_h(t) = product_{n>=0} sinc(a_h r^n t),
        a_h = sqrt(3(1-r^2)),

    where sinc(x)=sin(x)/x.  NumPy's ``sinc`` uses sin(pi*x)/(pi*x), hence the
    explicit division by pi below.

    Returns the product and the number of retained factors.
    """
    if h <= 0.0:
        raise ValueError("h must be positive")
    r = math.exp(-h)
    a = math.sqrt(3.0 * (1.0 - r * r))
    max_t = float(np.max(np.abs(t)))
    psi = np.ones_like(t, dtype=float)

    n = 0
    scale = a
    while scale * max_t > PRODUCT_TOL:
        psi *= np.sinc((scale * t) / math.pi)
        scale *= r
        n += 1
    return psi, n


def density_by_fft(h: float, n_grid: int = DEFAULT_N, dx: float = DEFAULT_DX) -> tuple[np.ndarray, np.ndarray, int]:
    """Invert the exact characteristic function on a centered FFT grid."""
    if n_grid <= 0 or (n_grid & (n_grid - 1)):
        raise ValueError("n_grid must be a positive power of two")
    if dx <= 0:
        raise ValueError("dx must be positive")

    frequencies = 2.0 * math.pi * np.fft.fftshift(np.fft.fftfreq(n_grid, d=dx))
    dt = float(frequencies[1] - frequencies[0])
    psi, factors = standardized_characteristic(frequencies, h)

    # Our convention is f(x)=(2*pi)^(-1) int exp(-itx) Psi(t) dt.
    density = (
        np.fft.fftshift(np.fft.fft(np.fft.ifftshift(psi))).real
        * dt
        / (2.0 * math.pi)
    )
    x = (np.arange(n_grid) - n_grid // 2) * dx
    return x, density, factors


def edgeworth_density(x: np.ndarray, h: float, order: int) -> np.ndarray:
    """Explicit h-expansion through order 0, 1, 2, or 3.

    H_n denotes the probabilists' Hermite polynomial.
    """
    if order not in (0, 1, 2, 3):
        raise ValueError("order must be 0, 1, 2, or 3")

    p = np.ones_like(x)
    if order >= 1:
        p += -h * eval_hermitenorm(4, x) / 20.0
    if order >= 2:
        p += h**2 * (
            4.0 * eval_hermitenorm(6, x) / 315.0
            + eval_hermitenorm(8, x) / 800.0
        )
    if order >= 3:
        p += h**3 * (
            eval_hermitenorm(4, x) / 60.0
            - 3.0 * eval_hermitenorm(8, x) / 700.0
            - eval_hermitenorm(10, x) / 1575.0
            - eval_hermitenorm(12, x) / 48000.0
        )
    return normal_density(x) * p


def cornish_fisher_quantile(u: np.ndarray, h: float, order: int) -> np.ndarray:
    """Central quantile expansion through first or second order."""
    if np.any((u <= 0.0) | (u >= 1.0)):
        raise ValueError("quantile levels must lie strictly between zero and one")
    if order not in (0, 1, 2):
        raise ValueError("order must be 0, 1, or 2")

    z = ndtri(u)
    q = z.copy()
    h3 = eval_hermitenorm(3, z)
    if order >= 1:
        q -= h * h3 / 20.0
    if order >= 2:
        h4 = eval_hermitenorm(4, z)
        h5 = eval_hermitenorm(5, z)
        h7 = eval_hermitenorm(7, z)
        q2 = (
            z * h3 * h3 / 800.0
            - h4 * h3 / 400.0
            + 4.0 * h5 / 315.0
            + h7 / 800.0
        )
        q += h * h * q2
    return q


def stable_ell(a: mp.mpf) -> mp.mpf:
    """ell(a)=log(sinh(a)/a), evaluated stably for positive a."""
    if a == 0:
        return mp.mpf("0")
    if a < 1:
        return mp.log(mp.sinh(a) / a)
    return a - mp.log(2 * a) + mp.log1p(-mp.e ** (-2 * a))


def rate_parametric(a: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    """Return (y(a), I(y(a))) for the limiting large-deviation rate.

        y(a) = sqrt(6) ell(a)/a,
        I(y(a)) = ell(a) - int_0^a ell(v)/v dv.
    """
    if a <= 0:
        raise ValueError("a must be positive")
    if a <= 1:
        integral = mp.quad(lambda v: mp.log(mp.sinh(v) / v) / v, [0, a])
    else:
        integral = mp.quad(lambda v: mp.log(mp.sinh(v) / v) / v, [0, 1, a])
    ell = stable_ell(a)
    y = mp.sqrt(6) * ell / a
    return y, ell - integral


def stieltjes_edge_constant() -> mp.mpf:
    """C_0 = gamma_1 + gamma^2/2 - pi^2/12."""
    return mp.stieltjes(1) + mp.euler**2 / 2 - mp.pi**2 / 12


def write_csv(path: Path, fieldnames: Iterable[str], rows: list[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(fieldnames))
        writer.writeheader()
        writer.writerows(rows)


def latex_scientific(value: float, digits_after_decimal: int = 4) -> str:
    """Format a positive or signed float as a compact LaTeX scientific number.

    Example: ``2.0332e-02`` becomes ``$2.0332\\times10^{-2}$``.  Keeping this
    formatter in the numerical script makes the report tables reproducible from
    the CSV-level values rather than relying on hand-edited LaTeX.
    """
    if not math.isfinite(value):
        raise ValueError("LaTeX table values must be finite")
    if value == 0.0:
        return "$0$"
    mantissa, exponent_text = f"{value:.{digits_after_decimal}e}".split("e")
    exponent = int(exponent_text)
    return rf"${mantissa}\times 10^{{{exponent}}}$"


def write_text(path: Path, text: str) -> None:
    """Write UTF-8 text, creating the parent directory when necessary."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def write_density_latex_table(path: Path, rows: list[dict[str, object]]) -> None:
    """Generate the density-error table included by the LaTeX report."""
    lines = [
        r"\begin{tabular}{@{}rrrrr@{}}",
        r"\toprule",
        r"$h$ & Gaussian error & first order & second order & third order\\",
        r"\midrule",
    ]
    for row in rows:
        h = float(row["h"])
        entries = [latex_scientific(float(row[f"E{order}_sup"])) for order in range(4)]
        lines.append(rf"${h:.2f}$ & " + " & ".join(entries) + r"\\")
    lines.extend([r"\bottomrule", r"\end{tabular}", ""])
    write_text(path, "\n".join(lines))


def write_quantile_latex_table(path: Path, rows: list[dict[str, object]]) -> None:
    """Generate the central-quantile error table included by the report."""
    lines = [
        r"\begin{tabular}{@{}rrrr@{}}",
        r"\toprule",
        r"$h$ & Gaussian quantile & first order & second order\\",
        r"\midrule",
    ]
    for row in rows:
        h = float(row["h"])
        entries = [latex_scientific(float(row[f"Q{order}_sup"])) for order in range(3)]
        lines.append(rf"${h:.2f}$ & " + " & ".join(entries) + r"\\")
    lines.extend([r"\bottomrule", r"\end{tabular}", ""])
    write_text(path, "\n".join(lines))


def write_ldp_latex_table(path: Path, rows: list[dict[str, object]]) -> None:
    """Generate the selected Lambert-W edge-comparison rows used in the report.

    The explicit completeness check prevents a formatting mismatch in the CSV
    representation of ``a`` (for example, ``"2.0"`` versus ``"2"``) from
    silently producing a partially empty LaTeX table.
    """
    selected = {2, 3, 5, 8, 10, 20}
    seen: set[int] = set()
    lines = [
        r"\begin{tabular}{@{}rrrr@{}}",
        r"\toprule",
        r"$a$ & $\delta=1-y/\sqrt6$ & exact $I(y)$ & exact minus Lambert--$W$ form\\",
        r"\midrule",
    ]
    for row in rows:
        a_value = float(row["a"])
        a_integer = int(round(a_value))
        if a_integer not in selected or not math.isclose(a_value, a_integer):
            continue
        seen.add(a_integer)
        delta = float(row["delta=1-y/sqrt(6)"])
        rate = float(row["I(y(a))"])
        difference = float(row["difference"])
        lines.append(
            rf"${a_integer}$ & ${delta:.7f}$ & ${rate:.7f}$ & "
            + latex_scientific(difference, digits_after_decimal=3)
            + r"\\"
        )

    missing = selected - seen
    if missing:
        raise RuntimeError(f"missing selected LDP table rows: {sorted(missing)}")
    lines.extend([r"\bottomrule", r"\end{tabular}", ""])
    write_text(path, "\n".join(lines))


def run_density_and_quantile_experiments(out_dir: Path, h_values: tuple[float, ...], n_grid: int, dx: float) -> None:
    density_rows: list[dict[str, object]] = []
    quantile_rows: list[dict[str, object]] = []
    quantile_levels = np.array([0.05, 0.10, 0.25, 0.50, 0.75, 0.90, 0.95])

    # Save two representative density curves.
    representative: dict[float, tuple[np.ndarray, np.ndarray]] = {}

    for h in h_values:
        x, exact, factors = density_by_fft(h, n_grid=n_grid, dx=dx)
        mass = float(np.trapezoid(exact, x))
        central = np.abs(x) <= 8.0

        row: dict[str, object] = {
            "h": f"{h:.8f}",
            "r=exp(-h)": f"{math.exp(-h):.12f}",
            "sinc_factors": factors,
            "fft_mass": f"{mass:.14f}",
        }
        for order in range(4):
            err = float(np.max(np.abs(exact[central] - edgeworth_density(x[central], h, order))))
            row[f"E{order}_sup"] = f"{err:.12e}"
            row[f"E{order}/h^{order+1}"] = f"{err / h ** (order + 1):.12e}"
        density_rows.append(row)

        cdf = cumulative_trapezoid(exact, x, initial=0.0)
        cdf = (cdf - cdf[0]) / (cdf[-1] - cdf[0])
        exact_q = np.interp(quantile_levels, cdf, x)
        qrow: dict[str, object] = {
            "h": f"{h:.8f}",
            "r=exp(-h)": f"{math.exp(-h):.12f}",
        }
        for order in range(3):
            err = float(
                np.max(
                    np.abs(
                        exact_q
                        - cornish_fisher_quantile(quantile_levels, h, order)
                    )
                )
            )
            qrow[f"Q{order}_sup"] = f"{err:.12e}"
            qrow[f"Q{order}/h^{order+1}"] = f"{err / h ** (order + 1):.12e}"
        quantile_rows.append(qrow)

        if min(abs(h - 0.20), abs(h - 0.07)) < 1.0e-12:
            representative[h] = (x, exact)

    write_csv(
        out_dir / "data" / "edgeworth_errors.csv",
        [
            "h",
            "r=exp(-h)",
            "sinc_factors",
            "fft_mass",
            "E0_sup",
            "E0/h^1",
            "E1_sup",
            "E1/h^2",
            "E2_sup",
            "E2/h^3",
            "E3_sup",
            "E3/h^4",
        ],
        density_rows,
    )
    write_csv(
        out_dir / "data" / "quantile_errors.csv",
        [
            "h",
            "r=exp(-h)",
            "Q0_sup",
            "Q0/h^1",
            "Q1_sup",
            "Q1/h^2",
            "Q2_sup",
            "Q2/h^3",
        ],
        quantile_rows,
    )

    write_density_latex_table(out_dir / "data" / "edgeworth_table.tex", density_rows)
    write_quantile_latex_table(out_dir / "data" / "quantile_table.tex", quantile_rows)

    # Error scaling plot.  No fitted slopes are imposed; the theorem-predicted
    # normalizations are displayed directly.
    hs = np.array([float(row["h"]) for row in density_rows])
    fig, ax = plt.subplots(figsize=(7.2, 4.7))
    for order in range(4):
        errors = np.array([float(row[f"E{order}_sup"]) for row in density_rows])
        ax.loglog(hs, errors, marker="o", label=f"through order $h^{order}$")
    ax.set_xlabel(r"$h=-\log r$")
    ax.set_ylabel(r"maximum density error on $|x|\leq 8$")
    ax.set_title("Successive continuous-parameter Edgeworth corrections")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "figures" / "edgeworth_error_scaling.pdf")
    fig.savefig(out_dir / "figures" / "edgeworth_error_scaling.png", dpi=180)
    plt.close(fig)

    # Representative exact densities and their second-order approximations.
    fig, ax = plt.subplots(figsize=(7.2, 4.7))
    for h in sorted(representative):
        x, exact = representative[h]
        mask = np.abs(x) <= 4.5
        ax.plot(x[mask], exact[mask], label=fr"exact, $h={h:g}$")
        ax.plot(
            x[mask],
            edgeworth_density(x[mask], h, 2),
            linestyle="--",
            label=fr"second order, $h={h:g}$",
        )
    ax.set_xlabel(r"standardized coordinate $x$")
    ax.set_ylabel("density")
    ax.set_title("Exact sinc-product densities and second-order approximation")
    ax.grid(True, alpha=0.25)
    ax.legend(ncol=2, fontsize=9)
    fig.tight_layout()
    fig.savefig(out_dir / "figures" / "density_edgeworth_comparison.pdf")
    fig.savefig(out_dir / "figures" / "density_edgeworth_comparison.png", dpi=180)
    plt.close(fig)


def run_large_deviation_experiments(out_dir: Path) -> None:
    mp.mp.dps = 60
    constant = stieltjes_edge_constant()
    a_values = [mp.mpf(v) for v in (2, 3, 5, 8, 10, 15, 20, 30, 50)]
    rows: list[dict[str, object]] = []
    for a in a_values:
        y, rate = rate_parametric(a)
        delta = 1 - y / mp.sqrt(6)
        w = -mp.lambertw(-delta / 2, -1)
        edge = w * w / 2 - w - constant
        rows.append(
            {
                "a": mp.nstr(a, 12),
                "y(a)": mp.nstr(y, 18),
                "delta=1-y/sqrt(6)": mp.nstr(delta, 18),
                "I(y(a))": mp.nstr(rate, 18),
                "LambertW_edge": mp.nstr(edge, 18),
                "difference": mp.nstr(rate - edge, 12),
            }
        )
    write_csv(
        out_dir / "data" / "large_deviation_edge.csv",
        [
            "a",
            "y(a)",
            "delta=1-y/sqrt(6)",
            "I(y(a))",
            "LambertW_edge",
            "difference",
        ],
        rows,
    )

    write_ldp_latex_table(out_dir / "data" / "ldp_edge_table.tex", rows)

    # Parametric plot of the exact limiting rate.  A nonuniform a-grid gives
    # resolution both near the Gaussian center and near the compact edge.
    a_grid = np.concatenate(
        [
            np.linspace(1.0e-4, 2.0, 220),
            np.geomspace(2.01, 80.0, 280),
        ]
    )
    y_pos: list[float] = []
    i_pos: list[float] = []
    for a_float in a_grid:
        y, rate = rate_parametric(mp.mpf(str(a_float)))
        y_pos.append(float(y))
        i_pos.append(float(rate))

    y_full = np.concatenate((-np.array(y_pos[:0:-1]), np.array(y_pos)))
    i_full = np.concatenate((np.array(i_pos[:0:-1]), np.array(i_pos)))
    fig, ax = plt.subplots(figsize=(7.2, 4.7))
    ax.plot(y_full, i_full, label="exact limiting rate")
    yy = np.linspace(-1.3, 1.3, 300)
    ax.plot(yy, yy * yy / 2.0, linestyle="--", label=r"quadratic center $y^2/2$")
    ax.axvline(math.sqrt(6.0), linestyle=":", linewidth=1)
    ax.axvline(-math.sqrt(6.0), linestyle=":", linewidth=1)
    ax.set_xlim(-math.sqrt(6.0) * 1.02, math.sqrt(6.0) * 1.02)
    ax.set_ylim(0, 8)
    ax.set_xlabel(r"compact-scale coordinate $y$")
    ax.set_ylabel(r"rate $I(y)$")
    ax.set_title("Large-deviation bridge from the Gaussian center to compact support")
    ax.grid(True, alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "figures" / "large_deviation_rate.pdf")
    fig.savefig(out_dir / "figures" / "large_deviation_rate.png", dpi=180)
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="report project directory (default: parent of numerics/)",
    )
    parser.add_argument("--n-grid", type=int, default=DEFAULT_N)
    parser.add_argument("--dx", type=float, default=DEFAULT_DX)
    parser.add_argument(
        "--h",
        type=float,
        nargs="*",
        default=list(DEFAULT_H),
        help="positive h values used in FFT tests",
    )
    args = parser.parse_args()

    out_dir = args.output_dir.resolve()
    (out_dir / "figures").mkdir(parents=True, exist_ok=True)
    (out_dir / "data").mkdir(parents=True, exist_ok=True)

    h_values = tuple(float(v) for v in args.h)
    if not h_values or any(v <= 0.0 for v in h_values):
        raise SystemExit("all h values must be positive")

    run_density_and_quantile_experiments(out_dir, h_values, args.n_grid, args.dx)
    run_large_deviation_experiments(out_dir)
    print(f"Wrote numerical outputs under {out_dir}")


if __name__ == "__main__":
    main()
