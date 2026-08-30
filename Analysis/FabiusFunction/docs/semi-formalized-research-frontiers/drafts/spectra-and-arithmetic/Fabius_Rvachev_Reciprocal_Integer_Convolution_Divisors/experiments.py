#!/usr/bin/env python3
"""Numerical experiments for the reciprocal-integer divisor report.

This script reproduces every numerical table and figure used in the report.
It deliberately separates exact integer/combinatorial checks from floating-point
Fourier and cascade visualizations.

Mathematical objects
--------------------
The Rvachev characteristic function is

    Phi(z) = product_{n>=0} sinc(pi*z/2**n),

where sinc(u)=sin(u)/u.  For an integer M>=2, its reciprocal-integer
convolution divisor has characteristic function

    Q_M(z) = Phi(z) / Phi(z/M)
           = product_{n>=0} (1/M) sum_{j=0}^{M-1}
               exp(2*pi*i*z*(M-1-2*j)/(M*2**(n+1))).

Equivalently, after an affine change of variable, the divisor is the law of

    Z_M = sum_{n>=1} J_n / 2**n,

with i.i.d. digits J_n uniform on {0,...,M-1}.  The finite-level digit
polynomial is

    A_{M,N}(x) = product_{j=0}^{N-1} (1+x^{2^j}+...+x^{(M-1)2^j}).

Its coefficients are computed exactly with Python integers.

Usage
-----
    python experiments.py --output-dir .

Dependencies: Python 3.10+, NumPy, Matplotlib, mpmath.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import Iterable, Sequence

import mpmath as mp
import numpy as np
import matplotlib.pyplot as plt


def digit_coefficients(M: int, N: int) -> np.ndarray:
    """Return exact coefficients of A_{M,N}(x) as an object array.

    The update

        A_{M,N+1}(x) = A_{M,N}(x) * sum_{j=0}^{M-1} x^{j 2^N}

    is implemented by shifted additions.  This is much faster than a generic
    polynomial convolution and keeps every coefficient as an exact Python int.
    """
    if M < 2 or N < 0:
        raise ValueError("Require M >= 2 and N >= 0")
    coeff = np.array([1], dtype=object)
    for level in range(N):
        step = 1 << level
        new = np.zeros(len(coeff) + (M - 1) * step, dtype=object)
        for digit in range(M):
            start = digit * step
            new[start : start + len(coeff)] += coeff
        coeff = new
    return coeff


def thue_morse_block(N: int) -> np.ndarray:
    """Return coefficients epsilon_n=(-1)^{binary digit sum of n}, n<2^N."""
    n = np.arange(1 << N, dtype=np.uint64)
    # Python's bit_count is exact and portable.  N is small in all experiments.
    return np.array([1 if int(k).bit_count() % 2 == 0 else -1 for k in n], dtype=object)


def verify_thue_morse_quotient(M: int, N: int) -> bool:
    """Verify A_{M,N}(x) T_N(x) = T_N(x^M) coefficientwise exactly."""
    a = digit_coefficients(M, N)
    t = thue_morse_block(N)
    lhs = np.convolve(a, t)
    rhs = np.zeros(M * ((1 << N) - 1) + 1, dtype=object)
    rhs[::M] = t
    if len(lhs) != len(rhs):
        return False
    return bool(np.array_equal(lhs, rhs))


def stern_sequence(nmax: int) -> list[int]:
    """Return Stern's diatomic sequence s(0),...,s(nmax)."""
    if nmax < 0:
        return []
    s = [0] * (nmax + 1)
    if nmax >= 1:
        s[1] = 1
    for n in range(2, nmax + 1):
        if n % 2 == 0:
            s[n] = s[n // 2]
        else:
            k = n // 2
            s[n] = s[k] + s[k + 1]
    return s


def verify_stern_hyperbinary(nmax: int = 1024) -> bool:
    """Verify c_3(n)=s(n+1) for all n<=nmax using a stabilized product."""
    N = math.ceil(math.log2(max(1, nmax + 1))) + 1
    coeff = digit_coefficients(3, N)
    stern = stern_sequence(nmax + 1)
    return all(int(coeff[n]) == stern[n + 1] for n in range(nmax + 1))


def box_density(M: int, N: int) -> tuple[np.ndarray, np.ndarray]:
    """Piecewise-constant density of a dyadic box smoothing of Z_{M,N}.

    Each atom at n/2^N has mass coefficient[n]/M^N.  Spreading that mass
    uniformly over a box of width 2^{-N} gives height

        coefficient[n] * 2^N / M^N = coefficient[n] * (2/M)^N.

    These are visualization approximants; for odd M they do not converge in L1
    to a density because the limiting measure is singular continuous.
    """
    coeff = digit_coefficients(M, N)
    x = (np.arange(len(coeff), dtype=float) + 0.5) / float(1 << N)
    height = np.asarray([float(int(c)) for c in coeff]) * (2.0 / M) ** N
    return x, height


def finite_cdf_values(M: int, N: int, x_values: Sequence[float]) -> np.ndarray:
    """Evaluate the finite-level CDF P(Z_{M,N}<=x) at specified x values."""
    coeff = digit_coefficients(M, N)
    cumulative = np.cumsum(np.asarray([float(int(c)) for c in coeff])) / float(M**N)
    indices = np.floor(np.asarray(x_values) * (1 << N) + 1e-12).astype(int)
    out = np.empty(len(indices), dtype=float)
    out[indices < 0] = 0.0
    out[indices >= len(cumulative)] = 1.0
    mask = (indices >= 0) & (indices < len(cumulative))
    out[mask] = cumulative[indices[mask]]
    return out


def endpoint_profile(M: int, N: int, theta: np.ndarray) -> np.ndarray:
    """Approximate Omega_M(theta)=2^{alpha theta} H_M(2^{-theta})."""
    alpha = math.log(M, 2.0)
    x = 2.0 ** (-theta)
    h = finite_cdf_values(M, N, x)
    return (2.0 ** (alpha * theta)) * h


def zero_multiplicity(M: int, n: int) -> int:
    """Exact zero multiplicity of Q_M at a positive integer n."""
    if M < 2 or n < 1:
        raise ValueError("Require M>=2 and n>=1")

    def v2(k: int) -> int:
        return (k & -k).bit_length() - 1

    if n % M:
        return 1 + v2(n)
    return v2(M)


def q_characteristic(M: int, z: float | mp.mpf, levels: int = 100) -> mp.mpc:
    """Evaluate Q_M(z) stably from the discrete digit factors.

    This representation remains stable at the integer points where the formal
    quotient Phi(z)/Phi(z/M) has removable 0/0 singularities.
    """
    z_mp = mp.mpf(z)
    product = mp.mpc(1)
    for n in range(levels):
        factor = mp.mpc(0)
        scale = 2 ** (n + 1)
        for j in range(M):
            digit = mp.mpf(M - 1 - 2 * j) / M
            factor += mp.e ** (2j * mp.pi * z_mp * digit / scale)
        product *= factor / M
    return product


def write_csv(path: Path, header: Iterable[str], rows: Iterable[Iterable[object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(list(header))
        writer.writerows(rows)


def make_cascade_plot(M: int, levels: Sequence[int], output: Path) -> None:
    """Plot finite-level box-density approximants for one digit alphabet size."""
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    for N in levels:
        x, h = box_density(M, N)
        # Downsample only for rendering; all exact summaries use full arrays.
        stride = max(1, len(x) // 9000)
        ax.plot(x[::stride], h[::stride], linewidth=0.85, label=f"N={N}")
    ax.set_xlabel(r"$x$ in the support of $Z_M$")
    ax.set_ylabel("dyadic box height")
    ax.set_title(f"Finite cascade approximants for M={M}")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(output, dpi=180)
    plt.close(fig)


def make_endpoint_profile_plot(output: Path) -> None:
    """Plot endpoint phase profiles for power-of-two and non-power-of-two M."""
    theta = np.linspace(0.0, 1.0, 401, endpoint=False)
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    for M, N in [(3, 16), (4, 14), (5, 15), (6, 14)]:
        omega = endpoint_profile(M, N, theta)
        ax.plot(theta, omega, linewidth=1.1, label=f"M={M}")
    ax.set_xlabel(r"dyadic phase $\theta$")
    ax.set_ylabel(r"$2^{(\log_2 M)\theta} H_M(2^{-\theta})$")
    ax.set_title("Endpoint log-periodic phase profiles")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(output, dpi=180)
    plt.close(fig)


def make_zero_plot(output: Path) -> None:
    """Plot the first zero multiplicities for three representative divisors."""
    n = np.arange(1, 65)
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    for M in (3, 4, 6):
        mult = np.array([zero_multiplicity(M, int(k)) for k in n])
        ax.step(n, mult, where="mid", linewidth=1.0, label=f"M={M}")
    ax.set_xlabel(r"positive integer zero $n$")
    ax.set_ylabel(r"$\operatorname{ord}_{n} Q_M$")
    ax.set_title("Arithmetic zero divisors")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(output, dpi=180)
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="Directory in which figures/ and data/ are created.",
    )
    args = parser.parse_args()
    root = args.output_dir.resolve()
    figures = root / "figures"
    data = root / "data"
    figures.mkdir(parents=True, exist_ok=True)
    data.mkdir(parents=True, exist_ok=True)

    # Exact algebraic checks.
    quotient_checks = [(M, N, verify_thue_morse_quotient(M, N)) for M in range(2, 9) for N in (4, 7)]
    stern_ok = verify_stern_hyperbinary(2048)

    # Cascade summary: maxima and L2 energies of the box approximants.
    cascade_rows: list[tuple[object, ...]] = []
    for M in (3, 5, 6):
        for N in (8, 10, 12, 14, 16):
            coeff = digit_coefficients(M, N)
            max_height = float(max(int(c) for c in coeff)) * (2.0 / M) ** N
            l2_energy = (
                sum(int(c) ** 2 for c in coeff) * (2.0**N) / float(M ** (2 * N))
            )
            cascade_rows.append((M, N, len(coeff), f"{max_height:.15g}", f"{l2_energy:.15g}"))
    write_csv(
        data / "cascade_summary.csv",
        ("M", "N", "number_of_bins", "max_box_height", "L2_energy"),
        cascade_rows,
    )

    # Exact zero multiplicities.
    write_csv(
        data / "zero_multiplicities.csv",
        ("n", "ord_Q3", "ord_Q4", "ord_Q6"),
        ((n, zero_multiplicity(3, n), zero_multiplicity(4, n), zero_multiplicity(6, n)) for n in range(1, 129)),
    )

    # Non-Rajchman subsequences for odd M: values are constant under doubling.
    mp.mp.dps = 60
    fourier_rows: list[tuple[object, ...]] = []
    for M in (3, 5, 7):
        for k in range(0, 11):
            z = M * (1 << k)
            value = q_characteristic(M, z, levels=120)
            fourier_rows.append((M, k, z, mp.nstr(mp.re(value), 30), mp.nstr(abs(value), 30)))
    write_csv(
        data / "odd_fourier_subsequence.csv",
        ("M", "k", "frequency_M_times_2_to_k", "Re_QM", "abs_QM"),
        fourier_rows,
    )

    # Stern/hyperbinary coefficients, compared exactly with the finite product.
    stern = stern_sequence(129)
    coeff3 = digit_coefficients(3, 9)
    write_csv(
        data / "stern_hyperbinary_check.csv",
        ("n", "coefficient_c3_n", "stern_s_n_plus_1", "equal"),
        ((n, int(coeff3[n]), stern[n + 1], int(coeff3[n]) == stern[n + 1]) for n in range(0, 128)),
    )

    # Endpoint profiles as numerical data for independent replotting.
    theta = np.linspace(0.0, 1.0, 401, endpoint=False)
    profile_columns: list[np.ndarray] = [theta]
    profile_header = ["theta"]
    for M, N in [(3, 16), (4, 14), (5, 15), (6, 14)]:
        profile_columns.append(endpoint_profile(M, N, theta))
        profile_header.append(f"Omega_M{M}_N{N}")
    matrix = np.column_stack(profile_columns)
    write_csv(data / "endpoint_profiles.csv", profile_header, matrix.tolist())

    # Figures included in the report.
    make_cascade_plot(3, (8, 12, 16), figures / "cascade_M3.png")
    make_cascade_plot(6, (8, 12, 16), figures / "cascade_M6.png")
    make_endpoint_profile_plot(figures / "endpoint_profiles.png")
    make_zero_plot(figures / "zero_multiplicities.png")

    # Human-readable reproducibility summary.
    with (data / "experiment_summary.txt").open("w", encoding="utf-8") as handle:
        handle.write("Exact Thue-Morse quotient checks\n")
        handle.write("================================\n")
        for M, N, ok in quotient_checks:
            handle.write(f"M={M:2d}, N={N:2d}: {ok}\n")
        handle.write(f"\nStern/hyperbinary equality through n=2048: {stern_ok}\n")
        handle.write("\nSelected odd-M Fourier subsequences\n")
        handle.write("===================================\n")
        for M in (3, 5, 7):
            vals = [row for row in fourier_rows if row[0] == M]
            handle.write(f"M={M}: abs(Q_M(M*2^k)) = {vals[0][4]} for k=0,...,10\n")
        handle.write("\nAll figures and CSV files were regenerated by this script.\n")

    if not all(ok for _, _, ok in quotient_checks):
        raise RuntimeError("At least one exact Thue-Morse quotient check failed")
    if not stern_ok:
        raise RuntimeError("Stern/hyperbinary check failed")

    print(f"Wrote figures to {figures}")
    print(f"Wrote data to {data}")


if __name__ == "__main__":
    main()
