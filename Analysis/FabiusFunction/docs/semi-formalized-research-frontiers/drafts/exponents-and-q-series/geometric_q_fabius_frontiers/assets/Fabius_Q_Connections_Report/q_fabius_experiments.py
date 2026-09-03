#!/usr/bin/env python3
"""Numerical experiments for the q-Fabius/Rvachev report.

The script verifies, to high numerical or exact rational precision, the main
identities developed in the accompanying report:

1. affine sign conjugacy between q=r and q=-r;
2. q-power (residue-class) decimation q -> q**m;
3. the sinc--q-Pochhammer logarithmic identity;
4. reciprocal q-Lagrange weights under q -> 1/q;
5. the digit-position refinement of the Thue--Morse/q-binomial product;
6. the centered positive/negative radix conjugacy;
7. density normalization, plateau heights, and standardized profile collapse.

It also creates two publication-ready figures. The implementation is fully
deterministic; no random numbers are used.
"""

from __future__ import annotations

import csv
import math
import platform
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

HERE = Path(__file__).resolve().parent


def centered_characteristic(q: float, t: np.ndarray, tol: float = 1e-15) -> np.ndarray:
    """Return psi_q(t)=E exp(i t (X_q-1/2)) from its exact sinc product."""
    t = np.asarray(t, dtype=float)
    if q == 0.0:
        return np.sinc(0.5 * t / np.pi)
    out = np.ones_like(t)
    weight = 1.0 - q
    max_t = float(np.max(np.abs(t))) if t.size else 0.0
    for _ in range(10000):
        out *= np.sinc(0.5 * weight * t / np.pi)
        weight *= q
        if 0.5 * abs(weight) * max_t < tol:
            break
    else:
        raise RuntimeError("Characteristic product did not converge")
    return out


@dataclass
class DensityGrid:
    q: float
    x: np.ndarray
    density: np.ndarray
    support_radius: float


def fft_density(q: float, n_grid: int = 2**16, pad_factor: float = 5.0) -> DensityGrid:
    """Invert the centered characteristic function on a padded FFT grid."""
    if not (-1.0 < q < 1.0) or q == 0.0:
        raise ValueError("This routine requires 0<|q|<1")
    radius = abs(1.0 - q) / (2.0 * (1.0 - abs(q)))
    length = pad_factor * 2.0 * radius
    dx = length / n_grid
    x0 = -0.5 * length
    x = x0 + dx * np.arange(n_grid)
    omega = 2.0 * np.pi * np.fft.fftfreq(n_grid, d=dx)
    phi = centered_characteristic(q, omega)
    density = np.fft.fft(phi * np.exp(-1j * omega * x0)).real / length
    return DensityGrid(q=q, x=x, density=density, support_radius=radius)


def interpolate_density(grid: DensityGrid, centered_x: np.ndarray) -> np.ndarray:
    return np.interp(centered_x, grid.x, grid.density, left=0.0, right=0.0)


def q_binomial_row(n: int, q: Fraction) -> List[Fraction]:
    """Return ([n choose k]_q)_{k=0}^n by q-Pascal recurrence."""
    row = [Fraction(1)]
    for nn in range(1, n + 1):
        new = [Fraction(0)] * (nn + 1)
        for k in range(nn + 1):
            if k <= nn - 1:
                new[k] += row[k]
            if k >= 1:
                new[k] += q ** (nn - k) * row[k - 1]
        row = new
    return row


def q_pochhammer_q(n: int, q: Fraction) -> Fraction:
    ans = Fraction(1)
    for j in range(1, n + 1):
        ans *= 1 - q**j
    return ans


def q_lagrange_weights(n: int, q: Fraction) -> List[Fraction]:
    """Weights at zero for the geometric nodes 1,q,...,q^n."""
    if q in (Fraction(0), Fraction(1), Fraction(-1)):
        raise ValueError("Nodes must be distinct and nonzero")
    row = q_binomial_row(n, q)
    denom = q_pochhammer_q(n, q)
    result = []
    for k in range(n + 1):
        exponent = (n - k) * (n - k + 1) // 2
        result.append(((-1) ** (n - k)) * q**exponent * row[k] / denom)
    return result


def popcount(n: int) -> int:
    return n.bit_count()


def position_weight(n: int) -> int:
    """pi_2(n)=sum j*b_j(n), where bit 0 has position 0."""
    total = 0
    j = 0
    while n:
        if n & 1:
            total += j
        n >>= 1
        j += 1
    return total


def product_coefficients(m: int, u: Fraction, q: Fraction) -> Dict[int, Fraction]:
    """Expand prod_{j<m}(1-u q^j z^(2^j)) as an exact sparse polynomial."""
    coeffs: Dict[int, Fraction] = {0: Fraction(1)}
    for j in range(m):
        shift = 1 << j
        factor = -u * q**j
        updated = dict(coeffs)
        for exponent, coefficient in coeffs.items():
            updated[exponent + shift] = updated.get(exponent + shift, Fraction(0)) + factor * coefficient
        coeffs = updated
    return coeffs


def finite_radix_transform(m: int, b: mp.mpf, t: mp.mpf) -> mp.mpf:
    ans = mp.mpf(1)
    for j in range(m):
        ans *= 1 - mp.e ** ((b**j) * t)
    return ans


def q_integer(m: int, b: mp.mpf) -> mp.mpf:
    if b == 1:
        return mp.mpf(m)
    return (1 - b**m) / (1 - b)


def write_figures(grids: Dict[float, DensityGrid]) -> None:
    """Create the figures embedded in the report."""
    x_plot = np.linspace(-1.08, 2.08, 5000)
    plt.figure(figsize=(8.4, 5.2))
    for q in (0.5, -0.5, 0.25, -0.25):
        grid = grids[q]
        density = interpolate_density(grid, x_plot - 0.5)
        left = 0.5 - grid.support_radius
        right = 0.5 + grid.support_radius
        density[(x_plot < left) | (x_plot > right)] = np.nan
        plt.plot(x_plot, density, label=rf"$q={q:g}$")
    plt.xlabel(r"$x$")
    plt.ylabel(r"$f_q(x)$")
    plt.title("Geometric-uniform densities for positive and negative q")
    plt.legend()
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    plt.savefig(HERE / "physical_densities.pdf", bbox_inches="tight")
    plt.savefig(HERE / "physical_densities.png", dpi=210, bbox_inches="tight")
    plt.close()

    plt.figure(figsize=(8.4, 5.2))
    x_norm = np.linspace(-1.0, 1.0, 5000)
    for q in (0.25, 0.5, 0.75, 0.9):
        grid = grids[q]
        values = grid.support_radius * interpolate_density(grid, grid.support_radius * x_norm)
        plt.plot(x_norm, values, label=rf"$q={q:g}$")
    plt.xlabel(r"support-normalized coordinate $x$")
    plt.ylabel(r"$\mathcal{U}_q(x)$")
    plt.title("Support-normalized q-Rvachev profiles")
    plt.legend()
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    plt.savefig(HERE / "normalized_profiles.pdf", bbox_inches="tight")
    plt.savefig(HERE / "normalized_profiles.png", dpi=210, bbox_inches="tight")
    plt.close()


def main() -> None:
    mp.mp.dps = 80
    checks: List[Tuple[str, str, str, str]] = []

    t = np.linspace(-180.0, 180.0, 12001)
    for r in (0.25, 0.5, 0.75):
        c = (1 + r) / (1 - r)
        residual = float(np.max(np.abs(centered_characteristic(-r, t) - centered_characteristic(r, c * t))))
        checks.append(("affine sign conjugacy", f"r={r}", f"{residual:.4e}", "max |psi_-r(t)-psi_r(c_r t)|"))

    for q, m in ((0.5, 2), (0.5, 3), (-0.5, 2), (0.25, 2), (0.75, 4)):
        q_m = q**m
        q_bracket = (1 - q**m) / (1 - q)
        lhs = centered_characteristic(q, t)
        rhs = np.ones_like(t)
        for j in range(m):
            a = q**j / q_bracket
            rhs *= centered_characteristic(q_m, a * t)
        residual = float(np.max(np.abs(lhs - rhs)))
        checks.append(("q-power decimation", f"q={q}, m={m}", f"{residual:.4e}", "max characteristic residual"))

    for q in (mp.mpf("0.5"), mp.mpf("-0.5"), mp.mpf("0.25"), mp.mpf("-0.25"), mp.mpf("0.75")):
        for tt in (mp.mpf("0.25"), mp.mpf("0.7"), mp.mpf("1.1")):
            direct = mp.mpf(1)
            weight = 1 - q
            for _ in range(500):
                z = weight * tt / 2
                direct *= mp.sin(z) / z
                weight *= q
                if abs(weight * tt) < mp.mpf("1e-70"):
                    break
            log_series = mp.mpf(0)
            for ell in range(1, 80):
                term = -mp.zeta(2 * ell) / (ell * (1 - q ** (2 * ell))) * (((1 - q) * tt) / (2 * mp.pi)) ** (2 * ell)
                log_series += term
                if abs(term) < mp.mpf("1e-70"):
                    break
            residual = abs(mp.log(direct) - log_series)
            checks.append(("sinc-Pochhammer log series", f"q={q}, t={tt}", mp.nstr(residual, 8), "|log product-zeta series|"))

    lagrange_rows: List[Tuple[str, int, int, str, str, str]] = []
    q_values = [Fraction(1, 2), Fraction(-1, 2), Fraction(2), Fraction(-2),
                Fraction(1, 4), Fraction(-1, 4), Fraction(4), Fraction(-4)]
    for q in q_values:
        for n in (3, 5, 7):
            weights = q_lagrange_weights(n, q)
            reciprocal = q_lagrange_weights(n, 1 / q)
            exact_ok = all(weights[k] == reciprocal[n - k] for k in range(n + 1))
            checks.append(("q-inversion Lagrange reversal", f"q={q}, n={n}", "0" if exact_ok else "1", "exact mismatch indicator"))
            if n == 5:
                for k, value in enumerate(weights):
                    lagrange_rows.append((str(q), n, k, str(value), str(float(value)), str(reciprocal[n - k])))

    with (HERE / "q_lagrange_weights.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["q", "n", "k", "lambda_exact", "lambda_decimal", "reciprocal_reversed_exact"])
        writer.writerows(lagrange_rows)

    m = 8
    u = Fraction(2, 3)
    q = Fraction(-1, 2)
    coeffs = product_coefficients(m, u, q)
    mismatch = 0
    for n in range(1 << m):
        predicted = (-u) ** popcount(n) * q ** position_weight(n)
        if coeffs.get(n, Fraction(0)) != predicted:
            mismatch += 1
    checks.append(("digit-position master product", f"m={m}, u={u}, q={q}", str(mismatch), "exact coefficient mismatches"))

    for k in range(m + 1):
        lhs = sum(q ** position_weight(n) for n in range(1 << m) if popcount(n) == k)
        rhs = q ** (k * (k - 1) // 2) * q_binomial_row(m, q)[k]
        if lhs != rhs:
            mismatch += 1
    checks.append(("fixed-weight Gaussian refinement", f"m={m}, q={q}", str(mismatch), "cumulative exact mismatch count"))

    for a in (mp.mpf(2), mp.mpf(4)):
        for m_radix in (3, 4, 7, 8):
            tt = mp.mpf("0.117")
            lhs = mp.e ** (-q_integer(m_radix, -a) * tt / 2) * finite_radix_transform(m_radix, -a, tt)
            rhs = ((-1) ** (m_radix * (m_radix - 1) // 2)) * mp.e ** (-q_integer(m_radix, a) * tt / 2) * finite_radix_transform(m_radix, a, tt)
            scale = max(mp.mpf(1), abs(lhs), abs(rhs))
            rel = abs(lhs - rhs) / scale
            checks.append(("centered radix sign conjugacy", f"a={a}, m={m_radix}", mp.nstr(rel, 8), "relative residual"))

    all_q = (-0.75, -0.5, -0.25, 0.25, 0.5, 0.75, 0.9)
    grids: Dict[float, DensityGrid] = {qv: fft_density(qv) for qv in all_q}
    for qv, grid in grids.items():
        dx = grid.x[1] - grid.x[0]
        mass = float(np.sum(grid.density) * dx)
        support_mask = np.abs(grid.x) <= grid.support_radius + 2 * dx
        minimum = float(np.min(grid.density[support_mask]))
        maximum = float(np.max(grid.density[support_mask]))
        checks.append(("FFT density mass", f"q={qv}", f"{abs(mass-1):.4e}", "|integral-1|"))
        checks.append(("FFT support minimum", f"q={qv}", f"{minimum:.4e}", "minimum on numerical support"))
        checks.append(("FFT density maximum", f"q={qv}", f"{maximum:.10f}", "numerical sup norm"))
        if abs(qv) < 0.5:
            r = abs(qv)
            if qv > 0:
                left, right, predicted_height = r, 1 - r, 1 / (1 - r)
            else:
                left = r * r / (1 - r)
                right = 1 - left
                predicted_height = 1 / (1 + r)
            x_eval = np.linspace(left + 0.02 * (right - left), right - 0.02 * (right - left), 1200)
            measured = interpolate_density(grid, x_eval - 0.5)
            plateau_error = float(np.max(np.abs(measured - predicted_height)))
            checks.append(("plateau height", f"q={qv}", f"{plateau_error:.4e}", "max interior error"))

    for r in (0.25, 0.5, 0.75):
        gp, gm = grids[r], grids[-r]
        z = np.linspace(-3.2, 3.2, 5000)
        sig_p = math.sqrt((1 - r) / (12 * (1 + r)))
        sig_m = math.sqrt((1 + r) / (12 * (1 - r)))
        dp = sig_p * interpolate_density(gp, sig_p * z)
        dm = sig_m * interpolate_density(gm, sig_m * z)
        residual = float(np.max(np.abs(dp - dm)))
        checks.append(("standardized density sign collapse", f"r={r}", f"{residual:.4e}", "max density residual"))

    write_figures(grids)

    cumulant_rows: List[Tuple[float, float, float]] = []
    for qv in (-0.9, -0.5, -0.25, 0.25, 0.5, 0.9):
        kurtosis_excess = -(6.0 / 5.0) * (1 - qv*qv) / (1 + qv*qv)
        sixth = (48.0 / 7.0) * (1 - qv*qv) ** 2 / (1 + qv*qv + qv**4)
        cumulant_rows.append((qv, kurtosis_excess, sixth))
    with (HERE / "standardized_cumulants.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["q", "excess_kurtosis", "standardized_sixth_cumulant"])
        writer.writerows(cumulant_rows)

    with (HERE / "numerical_checks.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["identity", "parameters", "residual_or_count", "metric"])
        writer.writerows(checks)

    with (HERE / "NUMERICAL_README.txt").open("w", encoding="utf-8") as handle:
        handle.write("Numerical supplement for the q-Fabius/Rvachev report\n")
        handle.write("=====================================================\n\n")
        handle.write("Run: python q_fabius_experiments.py\n\n")
        handle.write("The program is deterministic. Exact rational arithmetic is used for\n")
        handle.write("q-binomial, q-Lagrange, and digital-product checks; mpmath uses 80\n")
        handle.write("decimal digits for analytic product checks. Density figures use direct\n")
        handle.write("FFT inversion on a 2^16-point padded grid.\n\n")
        handle.write(f"Python: {platform.python_version()}\n")
        handle.write(f"NumPy: {np.__version__}\n")
        handle.write(f"Matplotlib: {matplotlib.__version__}\n")
        handle.write(f"mpmath: {mp.__version__}\n")

    print(f"Wrote {len(checks)} checks")
    print("Generated figures, CSV tables, and reproducibility notes in", HERE)


if __name__ == "__main__":
    main()
