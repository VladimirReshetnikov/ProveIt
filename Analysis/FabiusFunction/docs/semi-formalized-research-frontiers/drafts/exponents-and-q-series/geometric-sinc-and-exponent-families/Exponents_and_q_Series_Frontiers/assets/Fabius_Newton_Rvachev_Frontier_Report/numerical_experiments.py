#!/usr/bin/env python3
"""Numerical experiments for the Newton--Rvachev frontier report.

This script is intentionally self-contained and reproducible.  It checks the
exact algebraic identities proved in the accompanying LaTeX report and creates
two figures:

1. ``richardson_tomography.png``: geometric q-Richardson recovery of the first
   exponent a_0 from normalized even cumulants for the new family

       a_h = binom(h - 1, d),  d even.

   The transformed errors alternate in sign and decay like q^((r+1)m), where
   q = 1/4 and r is the interpolation order.

2. ``boundary_layers.png``: the standardized Pascal--Rvachev variables that
   control the boundary layers of the same family, compared with the standard
   Gaussian distribution.  Densities are obtained by deterministic FFT
   inversion of the exact characteristic product; no Monte Carlo sampling is
   used.

The script also writes CSV tables and a text verification log.  It needs only
NumPy, SciPy, Matplotlib, and mpmath.

Fourier normalization used below:
    numpy.sinc(x) = sin(pi*x)/(pi*x).
Thus the factor numpy.sinc(xi/2**h) is the Fourier transform (with kernel
exp(-2*pi*i*xi*x)) of a uniform variable on [-2**(-h-1), 2**(-h-1)].
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
from scipy.special import ndtr


# High precision is useful for the extrapolation table: the highest-order
# errors are much smaller than IEEE double precision at modest m.
mp.mp.dps = 100


def q_pochhammer(q: mp.mpf, n: int) -> mp.mpf:
    """Return (q;q)_n = product_{k=1}^n (1-q^k)."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    result = mp.mpf(1)
    for k in range(1, n + 1):
        result *= 1 - q**k
    return result


def gaussian_q_binomial(n: int, k: int, q: mp.mpf) -> mp.mpf:
    """Return the Gaussian binomial coefficient [n choose k]_q."""
    if k < 0 or k > n:
        return mp.mpf(0)
    return q_pochhammer(q, n) / (q_pochhammer(q, k) * q_pochhammer(q, n - k))


def richardson_weights(order: int, q: mp.mpf) -> list[mp.mpf]:
    r"""Lagrange weights at 0 for the nodes 1,q,...,q^order.

    The exact closed form proved in the report is

      w_{r,j} = (-1)^(r-j) q^((r-j)(r-j+1)/2)
                / ((q;q)_j (q;q)_{r-j}).

    Multiplying every node by q^m does not change these weights, so the same
    vector acts on A(q^m),...,A(q^(m+r)).
    """
    r = order
    if r < 0:
        raise ValueError("order must be nonnegative")
    return [
        (-1) ** (r - j)
        * q ** ((r - j) * (r - j + 1) // 2)
        / (q_pochhammer(q, j) * q_pochhammer(q, r - j))
        for j in range(r + 1)
    ]


def alternating_newton_exponent(h: int, d: int) -> int:
    r"""Return a_h = binom(h-1,d) for even d, with binom(-1,d)=1.

    For even d this sequence is nonnegative on all h >= 0:
      a_0 = 1,
      a_1 = ... = a_d = 0,
      a_h = binom(h-1,d) for h >= d+1.
    """
    if h < 0 or d < 0 or d % 2 != 0:
        raise ValueError("require h >= 0 and even d >= 0")
    if h == 0:
        return 1
    if h <= d:
        return 0
    return math.comb(h - 1, d)


def alternating_newton_A(x: mp.mpf, d: int) -> mp.mpf:
    r"""Closed generating function A_d(x)=1+(x/(1-x))^(d+1)."""
    if d < 0 or d % 2 != 0:
        raise ValueError("d must be a nonnegative even integer")
    return 1 + (x / (1 - x)) ** (d + 1)


def cumulative_zero_multiplicity(n: int, d: int) -> int:
    r"""Multiplicity of the zero at n for the alternating Newton family.

    The theorem gives 1 + binom(v_2(n), d+1), with the convention that the
    binomial coefficient is zero when v_2(n) < d+1.
    """
    if n <= 0:
        raise ValueError("n must be positive")
    v = (n & -n).bit_length() - 1
    return 1 + (math.comb(v, d + 1) if v >= d + 1 else 0)


def normalized_cumulant_sample(m: int, d: int, q: mp.mpf = mp.mpf(1) / 4) -> mp.mpf:
    r"""Return c_m=(2m/B_{2m}) kappa_{2m}=A_d(q^m)."""
    if m <= 0:
        raise ValueError("m must be positive")
    return alternating_newton_A(q**m, d)


def richardson_estimate(d: int, order: int, m: int, q: mp.mpf) -> mp.mpf:
    """Recover a_0 from the normalized cumulants at m,...,m+order."""
    weights = richardson_weights(order, q)
    return mp.fsum(
        weights[j] * normalized_cumulant_sample(m + j, d, q)
        for j in range(order + 1)
    )


def complete_homogeneous_q_grid(n: int, r: int, q: mp.mpf) -> mp.mpf:
    r"""h_n(1,q,...,q^r)=[n+r choose r]_q."""
    if n < 0:
        return mp.mpf(0)
    return gaussian_q_binomial(n + r, r, q)


def verify_algebra(log_lines: list[str]) -> None:
    """Run high-precision assertions for the report's exact identities."""
    q = mp.mpf(1) / 4

    # 1. Lagrange weights reproduce constants and annihilate x,...,x^r.
    for r in range(0, 8):
        weights = richardson_weights(r, q)
        for h in range(0, r + 1):
            value = mp.fsum(weights[j] * q ** (j * h) for j in range(r + 1))
            target = mp.mpf(1) if h == 0 else mp.mpf(0)
            assert mp.almosteq(value, target, rel_eps=mp.mpf("1e-80"), abs_eps=mp.mpf("1e-80"))

        # For h>r, compare with the exact q-binomial remainder formula.
        for h in range(r + 1, r + 8):
            lhs = mp.fsum(weights[j] * q ** (j * h) for j in range(r + 1))
            rhs = (
                (-1) ** r
                * q ** (r * (r + 1) // 2)
                * gaussian_q_binomial(h - 1, r, q)
            )
            assert mp.almosteq(lhs, rhs, rel_eps=mp.mpf("1e-75"), abs_eps=mp.mpf("1e-75"))

    # 2. Verify the generating-function formula by direct coefficient summation.
    for d in (0, 2, 4, 6):
        for x in (mp.mpf("0.03"), mp.mpf("0.17"), mp.mpf("0.41")):
            direct = mp.fsum(
                alternating_newton_exponent(h, d) * x**h for h in range(250)
            )
            closed = alternating_newton_A(x, d)
            assert mp.almosteq(direct, closed, rel_eps=mp.mpf("1e-70"), abs_eps=mp.mpf("1e-70"))

    # 3. Verify the zero-multiplicity formula by summing the exponent prefix.
    for d in (0, 2, 4, 6):
        for v in range(0, 18):
            direct = sum(alternating_newton_exponent(h, d) for h in range(v + 1))
            closed = 1 + (math.comb(v, d + 1) if v >= d + 1 else 0)
            assert direct == closed

    # 4. Verify the exact transformed-series formula for A_d.
    for d in (2, 4):
        for r in range(0, 6):
            for m in range(1, 5):
                estimate = richardson_estimate(d, r, m, q)
                # A finite but very long coefficient sum is enough at 100 digits.
                remainder = mp.fsum(
                    alternating_newton_exponent(h, d)
                    * gaussian_q_binomial(h - 1, r, q)
                    * q ** (m * h)
                    for h in range(r + 1, 300)
                )
                predicted = 1 + (-1) ** r * q ** (r * (r + 1) // 2) * remainder
                assert mp.almosteq(
                    estimate,
                    predicted,
                    rel_eps=mp.mpf("1e-65"),
                    abs_eps=mp.mpf("1e-65"),
                )

    # 5. Condition number: the l1 norm equals (-q;q)_r/(q;q)_r.
    for r in range(0, 12):
        weights = richardson_weights(r, q)
        lhs = mp.fsum(abs(w) for w in weights)
        rhs = mp.fprod((1 + q**k) / (1 - q**k) for k in range(1, r + 1))
        assert mp.almosteq(lhs, rhs, rel_eps=mp.mpf("1e-75"), abs_eps=mp.mpf("1e-75"))

    infinite_condition = mp.fprod((1 + q**k) / (1 - q**k) for k in range(1, 200))
    log_lines.append("All exact symbolic/numeric identity checks passed.")
    log_lines.append(f"Limiting l1 condition number at q=1/4: {mp.nstr(infinite_condition, 30)}")


def write_richardson_table(output_dir: Path, d: int = 2) -> None:
    """Write the high-precision extrapolation table and its convergence plot."""
    q = mp.mpf(1) / 4
    csv_path = output_dir / "richardson_tomography.csv"
    rows: list[dict[str, str | int]] = []

    for m in range(1, 11):
        row: dict[str, str | int] = {"m": m}
        for r in range(0, 7):
            error = richardson_estimate(d, r, m, q) - 1
            row[f"error_r{r}"] = mp.nstr(error, 45)
        rows.append(row)

    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    # Plot absolute errors.  The exact signs are recorded in the CSV and table;
    # a log plot is more informative for the many decades of convergence.
    ms = np.arange(1, 11)
    plt.figure(figsize=(7.2, 4.6))
    for r in range(0, 7):
        errors = np.array(
            [float(abs(richardson_estimate(d, r, int(m), q) - 1)) for m in ms]
        )
        plt.semilogy(ms, errors, marker="o", label=f"order r={r}")
    plt.xlabel("cumulant index m")
    plt.ylabel(r"absolute error in recovered $a_0$")
    plt.title(r"Certified $q$-Richardson cumulant tomography ($q=1/4$, $d=2$)")
    plt.grid(True, which="both", linewidth=0.4)
    plt.legend(ncol=2, fontsize=8)
    plt.tight_layout()
    plt.savefig(output_dir / "richardson_tomography.png", dpi=220)
    plt.close()


def pascal_characteristic(freq: np.ndarray, rank: int, h_max: int = 76) -> np.ndarray:
    r"""Evaluate Phi_rank(freq)=prod_h sinc(freq/2^h)^binom(h,rank-1).

    The omitted tail is far below the FFT discretization error for the grids
    used here.  Underflow at high frequencies is harmless: the exact transform
    is already extremely small there.
    """
    if rank < 1:
        raise ValueError("rank must be at least 1")
    phi = np.ones(freq.shape, dtype=np.float64)
    for h in range(rank - 1, h_max + 1):
        exponent = math.comb(h, rank - 1)
        phi *= np.power(np.sinc(freq / (2.0**h)), exponent)
    return phi


def pascal_density_fft(
    rank: int,
    n_grid: int = 2**18,
    domain_length: float = 2.4,
    h_max: int = 76,
) -> tuple[np.ndarray, np.ndarray]:
    r"""Invert the exact characteristic product on a non-aliasing FFT box.

    Every Pascal--Rvachev variable is supported on [-1,1].  A periodic FFT box
    of length 2.4 leaves a gap of 0.4 between adjacent copies, so no support
    overlap occurs.  The density is C-infinity, making Fourier truncation very
    accurate.
    """
    dx = domain_length / n_grid
    frequencies = np.fft.fftfreq(n_grid, d=dx)
    transform = pascal_characteristic(frequencies, rank, h_max=h_max)
    density = np.fft.fftshift(np.fft.ifft(transform).real) / dx
    x = (np.arange(n_grid) - n_grid // 2) * dx

    # Remove roundoff-level negative ripples and renormalize.
    density[density < 0] = np.maximum(density[density < 0], -1e-7)
    density = np.maximum(density, 0.0)
    density /= np.trapezoid(density, x)
    return x, density


def boundary_layer_data(
    ranks: Sequence[int],
    y_grid: np.ndarray,
    n_grid: int = 2**18,
) -> dict[int, np.ndarray]:
    """Return CDFs of variance-normalized Pascal variables on y_grid."""
    output: dict[int, np.ndarray] = {}
    for rank in ranks:
        x, density = pascal_density_fft(rank, n_grid=n_grid)
        dx = x[1] - x[0]
        cdf = np.cumsum(density) * dx
        cdf = np.clip(cdf, 0.0, 1.0)
        sigma = 3.0 ** (-(rank + 1) / 2.0)
        output[rank] = np.interp(y_grid * sigma, x, cdf)
    return output


def write_boundary_layer_figure(output_dir: Path) -> None:
    """Create deterministic boundary-layer curves and an error table."""
    ranks = (3, 5, 7, 9)  # Correspond to d=2,4,6,8 in the new family.
    y = np.linspace(-4.0, 4.0, 401)
    cdfs = boundary_layer_data(ranks, y)
    gaussian_survival = 1.0 - ndtr(y)

    csv_path = output_dir / "boundary_layer_errors.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(["rank", "d", "max_cdf_error_on_-4_4", "berry_esseen_rate_factor"])
        for rank in ranks:
            max_error = float(np.max(np.abs(cdfs[rank] - ndtr(y))))
            rate = (3.0 * math.sqrt(3.0) / 7.0) ** rank
            writer.writerow([rank, rank - 1, f"{max_error:.12e}", f"{rate:.12e}"])

    plt.figure(figsize=(7.2, 4.8))
    plt.plot(y, gaussian_survival, linewidth=2.0, label="Gaussian survival")
    for rank in ranks:
        # The right boundary profile of the new density is the survival
        # function of the standardized rank-r Pascal variable.
        plt.plot(y, 1.0 - cdfs[rank], label=f"d={rank-1} (rank {rank})")
    plt.xlabel(r"boundary coordinate $y$")
    plt.ylabel(r"$f_d(1/2+\sigma_d y)$")
    plt.title("Gaussian boundary layers of alternating Newton--Rvachev densities")
    plt.grid(True, linewidth=0.4)
    plt.legend(fontsize=8)
    plt.tight_layout()
    plt.savefig(output_dir / "boundary_layers.png", dpi=220)
    plt.close()


def write_zero_multiplicity_table(output_dir: Path, d: int = 2) -> None:
    """Tabulate the sparse extra zero multiplicities for the headline d=2 case."""
    path = output_dir / "zero_multiplicities_d2.csv"
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(["n", "v2_n", "multiplicity"])
        for n in range(1, 257):
            v = (n & -n).bit_length() - 1
            writer.writerow([n, v, cumulative_zero_multiplicity(n, d)])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory for figures, tables, and verification log",
    )
    args = parser.parse_args()
    output_dir: Path = args.output_dir
    output_dir.mkdir(parents=True, exist_ok=True)

    log_lines: list[str] = []
    verify_algebra(log_lines)
    write_richardson_table(output_dir)
    write_boundary_layer_figure(output_dir)
    write_zero_multiplicity_table(output_dir)

    q = mp.mpf(1) / 4
    log_lines.append("")
    log_lines.append("Headline q-Richardson errors for d=2 (estimate minus a_0=1):")
    for r in range(0, 7):
        errors = [richardson_estimate(2, r, m, q) - 1 for m in range(1, 5)]
        log_lines.append(
            f"  r={r}: " + ", ".join(mp.nstr(value, 16) for value in errors)
        )

    (output_dir / "verification_log.txt").write_text("\n".join(log_lines) + "\n", encoding="utf-8")
    print("\n".join(log_lines))
    print(f"\nArtifacts written to {output_dir}")


if __name__ == "__main__":
    main()
