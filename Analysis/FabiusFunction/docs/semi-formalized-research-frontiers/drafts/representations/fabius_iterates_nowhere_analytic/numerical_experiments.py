#!/usr/bin/env python3
r"""Numerical diagnostics for compositional iterates of the Fabius function.

This script is supplementary only: no numerical calculation is used in the proof.
It constructs the Rvachev up-function from a truncated infinite sinc product,
recovers the bounded Fabius function on [0,1], composes truncated Taylor series,
and compares high derivatives of F^{\circ n} with the finite ``spine sum'' that
appears in the report.

Fourier convention
------------------
For independent random variables X_k uniformly distributed on
[-2^{-k},2^{-k}] (k >= 1), the sum has density up(x), supported on [-1,1].
Its Fourier transform in cycles/unit is

    prod_{j>=0} sinc(f / 2^j),

where numpy.sinc(t) = sin(pi t)/(pi t).  An inverse FFT of a truncated product
therefore gives an accurate, smooth approximation away from tiny endpoint
roundoff effects.

The global signed Fabius extension Theta is reconstructed block by block:

    Theta(t) = (-1)^{s_2(k)} up(t-(2k+1)),   2k <= t <= 2k+2,

where s_2(k) is the binary digit sum.  The exact derivative identity used by
the experiment is

    F^{(m)}(x) = 2^{m(m+1)/2} Theta(2^m x),   m >= 1.

Run, for example:

    python numerical_experiments.py --output-dir numerical_output

The generated CSV uses an explicit LF line terminator.  Exact PNG bytes require
the pinned platform and dependency stack recorded in REPOSITORY_AUDIT.md; other
supported environments should be compared numerically rather than by file hash.
"""

from __future__ import annotations

import argparse
import csv
import math
import shutil
from pathlib import Path
from typing import Iterable

import matplotlib.pyplot as plt
import numpy as np
from scipy.interpolate import PchipInterpolator


FIGURE_FILENAMES = (
    "fabius_iterates.png",
    "spine_comparison.png",
    "spine_remainder.png",
    "taylor_root_diagnostic.png",
)


def build_up_interpolant(
    fft_power: int = 17,
    sinc_factors: int = 24,
    spatial_period: float = 4.0,
) -> PchipInterpolator:
    """Return a shape-preserving interpolant for Rvachev's up-function.

    The spatial period is chosen larger than the support length 2, so periodic
    copies introduced by the FFT do not overlap.  Values below tiny negative
    roundoff are clipped to zero, and the result is normalized by up(0)=1.
    """

    if fft_power < 12:
        raise ValueError("fft_power should be at least 12 for a useful grid")
    if sinc_factors < 8:
        raise ValueError("sinc_factors should be at least 8")
    if spatial_period <= 2.0:
        raise ValueError("spatial_period must exceed the support length 2")

    n_grid = 1 << fft_power
    dx = spatial_period / n_grid
    frequencies = np.fft.fftfreq(n_grid, d=dx)

    transform = np.ones(n_grid, dtype=np.float64)
    for j in range(sinc_factors):
        transform *= np.sinc(frequencies / (2.0**j))

    density = np.fft.fftshift(np.fft.ifft(transform).real / dx)
    x_grid = (np.arange(n_grid) - n_grid // 2) * dx

    support_mask = np.abs(x_grid) <= 1.0
    support_x = x_grid[support_mask]
    support_y = np.maximum(density[support_mask], 0.0)

    center_index = int(np.argmin(np.abs(support_x)))
    center_value = float(support_y[center_index])
    if not math.isfinite(center_value) or center_value <= 0.0:
        raise RuntimeError("failed to normalize the FFT approximation at x=0")
    support_y /= center_value

    # Pin the exact endpoint and center values to suppress interpolation noise.
    support_y[0] = 0.0
    support_y[-1] = 0.0
    support_y[center_index] = 1.0
    return PchipInterpolator(support_x, support_y, extrapolate=False)


class FabiusNumerics:
    """Numerical access to up, the bounded Fabius function, and Theta."""

    def __init__(self, up_interpolant: PchipInterpolator):
        self._up = up_interpolant

    def up(self, x: np.ndarray | float) -> np.ndarray | float:
        array = np.asarray(x, dtype=np.float64)
        result = np.zeros_like(array)
        mask = np.abs(array) <= 1.0
        if np.any(mask):
            values = np.asarray(self._up(array[mask]), dtype=np.float64)
            result[mask] = np.nan_to_num(values, nan=0.0)
        if np.isscalar(x):
            return float(result)
        return result

    def fabius(self, x: np.ndarray | float) -> np.ndarray | float:
        """Bounded Fabius function, extended constantly outside [0,1]."""

        array = np.asarray(x, dtype=np.float64)
        result = np.empty_like(array)
        result[array <= 0.0] = 0.0
        result[array >= 1.0] = 1.0
        mask = (array > 0.0) & (array < 1.0)
        if np.any(mask):
            result[mask] = self.up(array[mask] - 1.0)
        if np.isscalar(x):
            return float(result)
        return result

    @staticmethod
    def thue_morse_sign(k: int) -> int:
        return -1 if k.bit_count() % 2 else 1

    def theta(self, t: float) -> float:
        """Global signed Fabius extension Theta at a nonnegative argument."""

        if t < 0.0:
            return 0.0
        # At a positive even boundary either neighboring block gives up(+-1)=0.
        k = int(math.floor(t / 2.0))
        centered = t - (2.0 * k + 1.0)
        if centered > 1.0 and centered < 1.0 + 1e-12:
            centered = 1.0
        if centered < -1.0 and centered > -1.0 - 1e-12:
            centered = -1.0
        return float(self.thue_morse_sign(k) * self.up(centered))

    def derivative(self, order: int, x: float) -> np.longdouble:
        """Approximate the order-th derivative of bounded F at x in (0,1)."""

        if order == 0:
            return np.longdouble(self.fabius(x))
        exponent = order * (order + 1) // 2
        return np.longdouble(2.0) ** exponent * np.longdouble(
            self.theta(math.ldexp(x, order))
        )

    def first_derivative(self, x: float) -> float:
        return float(2.0 * self.theta(2.0 * x))


def truncated_convolution(
    a: np.ndarray, b: np.ndarray, degree: int
) -> np.ndarray:
    """Multiply two coefficient arrays and discard powers above ``degree``."""

    out = np.zeros(degree + 1, dtype=np.longdouble)
    for i in range(min(len(a), degree + 1)):
        if a[i] == 0:
            continue
        upper = min(len(b) - 1, degree - i)
        for j in range(upper + 1):
            out[i + j] += a[i] * b[j]
    return out


def compose_local_taylor(
    fab: FabiusNumerics, x: float, iterate_count: int, degree: int
) -> np.ndarray:
    r"""Taylor coefficients of F^{\circ iterate_count}(x+z) through z^degree."""

    if not (0.0 < x < 1.0):
        raise ValueError("x must lie strictly inside (0,1)")
    if iterate_count < 1:
        raise ValueError("iterate_count must be positive")

    series = np.zeros(degree + 1, dtype=np.longdouble)
    series[0] = np.longdouble(x)
    series[1] = np.longdouble(1.0)

    factorials = [math.factorial(k) for k in range(degree + 1)]

    for _ in range(iterate_count):
        center = float(series[0])
        outer = np.zeros(degree + 1, dtype=np.longdouble)
        for k in range(degree + 1):
            outer[k] = fab.derivative(k, center) / np.longdouble(factorials[k])

        delta = series.copy()
        delta[0] = np.longdouble(0.0)
        result = np.zeros(degree + 1, dtype=np.longdouble)
        result[0] = outer[0]
        power = np.zeros(degree + 1, dtype=np.longdouble)
        power[0] = np.longdouble(1.0)
        for k in range(1, degree + 1):
            power = truncated_convolution(power, delta, degree)
            result += outer[k] * power
        series = result

    return series


def orbit_and_weights(
    fab: FabiusNumerics, x: float, iterate_count: int
) -> tuple[list[float], list[float], list[float], list[float]]:
    """Return orbit x_j, slopes a_j, prefixes B_j, and suffixes A_{j,n}."""

    orbit = [x]
    for _ in range(iterate_count - 1):
        orbit.append(float(fab.fabius(orbit[-1])))

    slopes = [fab.first_derivative(y) for y in orbit]
    prefixes = [1.0]
    for j in range(1, iterate_count):
        prefixes.append(prefixes[-1] * slopes[j - 1])

    suffixes = []
    for j in range(iterate_count):
        product = 1.0
        for r in range(j + 1, iterate_count):
            product *= slopes[r]
        suffixes.append(product)
    return orbit, slopes, prefixes, suffixes


def spine_sum(
    fab: FabiusNumerics,
    order: int,
    orbit: Iterable[float],
    prefixes: Iterable[float],
    suffixes: Iterable[float],
) -> np.longdouble:
    q_order = np.longdouble(2.0) ** (order * (order + 1) // 2)
    total = np.longdouble(0.0)
    for y, prefix, suffix in zip(orbit, prefixes, suffixes):
        total += (
            np.longdouble(suffix)
            * np.longdouble(prefix) ** order
            * np.longdouble(fab.theta(math.ldexp(y, order)))
        )
    return q_order * total


def iterate_values(
    fab: FabiusNumerics, x: np.ndarray, iterate_count: int
) -> np.ndarray:
    values = np.asarray(x, dtype=np.float64)
    for _ in range(iterate_count):
        values = np.asarray(fab.fabius(values), dtype=np.float64)
    return values


def write_diagnostics(
    output_dir: Path,
    figure_dir: Path,
    fab: FabiusNumerics,
    x0: float,
    iterate_count: int,
    max_order: int,
) -> None:
    """Create CSV and plots used as reproducible diagnostics in the report."""

    coefficients = compose_local_taylor(fab, x0, iterate_count, max_order)
    orbit, slopes, prefixes, suffixes = orbit_and_weights(fab, x0, iterate_count)
    dominant = max(prefixes)

    rows: list[dict[str, str | int]] = []
    # The two extreme Faà di Bruno partitions coincide at m=1, so the
    # asymptotic spine formula is intentionally diagnosed only for m >= 2.
    for m in range(2, max_order + 1):
        derivative = coefficients[m] * np.longdouble(math.factorial(m))
        spine = spine_sum(fab, m, orbit, prefixes, suffixes)
        q_m = np.longdouble(2.0) ** (m * (m + 1) // 2)
        scale = q_m * np.longdouble(dominant) ** m
        normalized_derivative = derivative / scale if scale else np.longdouble("nan")
        normalized_spine = spine / scale if scale else np.longdouble("nan")
        relative_gap = (
            abs(derivative - spine) / max(abs(derivative), abs(spine), np.longdouble(1e-300))
        )
        coefficient_root = (
            abs(coefficients[m]) ** (np.longdouble(1.0) / m)
            if coefficients[m] != 0
            else np.longdouble(0.0)
        )
        rows.append(
            {
                "order_m": m,
                "derivative": f"{derivative:.18e}",
                "spine_sum": f"{spine:.18e}",
                "normalized_derivative": f"{normalized_derivative:.18e}",
                "normalized_spine": f"{normalized_spine:.18e}",
                "relative_gap": f"{relative_gap:.18e}",
                "taylor_coefficient_mth_root": f"{coefficient_root:.18e}",
            }
        )

    csv_path = output_dir / "spine_diagnostic.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(rows[0].keys()),
            lineterminator="\n",
        )
        writer.writeheader()
        writer.writerows(rows)

    x_grid = np.linspace(0.0, 1.0, 1201)
    plt.figure(figsize=(7.2, 4.5))
    for n in range(1, 4):
        plt.plot(x_grid, iterate_values(fab, x_grid, n), label=rf"$F^{{\circ {n}}}$")
    plt.plot(x_grid, x_grid, linestyle="--", linewidth=1.0, label=r"identity")
    plt.xlabel(r"$x$")
    plt.ylabel("value")
    plt.title("The first three compositional iterates")
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "fabius_iterates.png", dpi=180)
    plt.close()

    orders = np.array([int(row["order_m"]) for row in rows])
    exact_norm = np.array([float(row["normalized_derivative"]) for row in rows])
    spine_norm = np.array([float(row["normalized_spine"]) for row in rows])
    roots = np.array([float(row["taylor_coefficient_mth_root"]) for row in rows])
    normalized_gap = np.abs(exact_norm - spine_norm)

    plt.figure(figsize=(7.2, 4.5))
    plt.plot(orders, exact_norm, marker="o", label="full Faà di Bruno derivative")
    plt.plot(orders, spine_norm, marker="s", linestyle="--", label="spine sum")
    plt.axhline(0.0, linewidth=0.8)
    plt.xlabel(r"derivative order $m$")
    plt.ylabel(r"value divided by $Q_m H_n^m$")
    plt.title(rf"Spine comparison at $x={x0}$ for $F^{{\circ {iterate_count}}}$")
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "spine_comparison.png", dpi=180)
    plt.close()

    plt.figure(figsize=(7.2, 4.5))
    plt.semilogy(orders, np.maximum(normalized_gap, 1e-20), marker="o")
    plt.xlabel(r"derivative order $m$")
    plt.ylabel(r"$|D_m-S_m|/(Q_m H_n^m)$")
    plt.title("Normalized non-spine remainder")
    plt.tight_layout()
    plt.savefig(output_dir / "spine_remainder.png", dpi=180)
    plt.close()

    plt.figure(figsize=(7.2, 4.5))
    plt.plot(orders, roots, marker="o")
    plt.xlabel(r"Taylor order $m$")
    plt.ylabel(r"$|[z^m]F^{\circ n}(x_0+z)|^{1/m}$")
    plt.title("Finite-order Taylor-root diagnostic")
    plt.tight_layout()
    plt.savefig(output_dir / "taylor_root_diagnostic.png", dpi=180)
    plt.close()

    metadata_path = output_dir / "numerical_metadata.txt"
    with metadata_path.open("w", encoding="utf-8") as handle:
        handle.write("Numerical diagnostic parameters\n")
        handle.write("===============================\n")
        handle.write(f"x0 = {x0}\n")
        handle.write(f"iterate_count = {iterate_count}\n")
        handle.write(f"max_order = {max_order}\n")
        handle.write("orbit x_j:\n")
        for j, y in enumerate(orbit):
            handle.write(f"  x_{j} = {y:.17g}\n")
        handle.write("slopes a_j = F'(x_j):\n")
        for j, a in enumerate(slopes):
            handle.write(f"  a_{j} = {a:.17g}\n")
        handle.write("prefix weights B_j:\n")
        for j, b in enumerate(prefixes):
            handle.write(f"  B_{j} = {b:.17g}\n")
        handle.write("suffix weights A_{j,n}:\n")
        for j, a in enumerate(suffixes):
            handle.write(f"  A_{j},{iterate_count} = {a:.17g}\n")
        handle.write(f"dominant prefix H_n = {dominant:.17g}\n")
        handle.write("\nNo numerical output is used as a premise of the proof.\n")

    figure_dir.mkdir(parents=True, exist_ok=True)
    for filename in FIGURE_FILENAMES:
        source = output_dir / filename
        destination = figure_dir / filename
        if source.resolve() != destination.resolve():
            shutil.copyfile(source, destination)


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("numerical_output"),
        help="directory for CSV, metadata, and plots",
    )
    parser.add_argument(
        "--figure-dir",
        type=Path,
        default=Path("figures"),
        help="directory synchronized with the four generated plots",
    )
    parser.add_argument("--x0", type=float, default=0.437123456789)
    parser.add_argument("--iterate-count", type=int, default=4)
    parser.add_argument("--max-order", type=int, default=18)
    parser.add_argument("--fft-power", type=int, default=17)
    parser.add_argument("--sinc-factors", type=int, default=24)
    return parser.parse_args()


def main() -> None:
    args = parse_arguments()
    if not (0.0 < args.x0 < 1.0):
        raise SystemExit("--x0 must lie strictly between 0 and 1")
    if args.iterate_count < 1:
        raise SystemExit("--iterate-count must be positive")
    if args.max_order < 2:
        raise SystemExit("--max-order must be at least 2")

    args.output_dir.mkdir(parents=True, exist_ok=True)
    up_interpolant = build_up_interpolant(args.fft_power, args.sinc_factors)
    fab = FabiusNumerics(up_interpolant)

    # Basic consistency checks catch FFT-scaling or convention errors early.
    checks = {
        "up(0)": fab.up(0.0),
        "up(1/2)": fab.up(0.5),
        "F(0)": fab.fabius(0.0),
        "F(1/2)": fab.fabius(0.5),
        "F(1)": fab.fabius(1.0),
    }
    if abs(checks["up(0)"] - 1.0) > 5e-6:
        raise RuntimeError(f"unexpected normalization: {checks}")
    if abs(checks["F(1/2)"] - 0.5) > 2e-4:
        raise RuntimeError(f"midpoint check failed: {checks}")

    write_diagnostics(
        args.output_dir,
        args.figure_dir,
        fab,
        args.x0,
        args.iterate_count,
        args.max_order,
    )
    print("Generated numerical diagnostics in", args.output_dir)
    print("Synchronized report figures in", args.figure_dir)
    for key, value in checks.items():
        print(f"  {key} = {value:.12g}")


if __name__ == "__main__":
    main()
