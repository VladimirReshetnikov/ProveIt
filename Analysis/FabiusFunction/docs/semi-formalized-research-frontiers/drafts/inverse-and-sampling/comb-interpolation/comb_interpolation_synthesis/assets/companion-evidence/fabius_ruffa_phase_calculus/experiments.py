#!/usr/bin/env python3
"""Numerical and symbolic checks for the Bernoulli--Ruffa phase calculus.

This program accompanies the report
``fabius_ruffa_phase_calculus.tex``.  It has three deliberately separate
layers:

1. Exact rational algebra (SymPy): cumulants and moments of Rvachev's
   ``up`` density, moments of the derivative of the Fabius function, and
   the integrals I_p = integral_0^1 x^p F(x) dx.
2. Independent numerical reconstruction (NumPy/SciPy): inverse Fourier
   transformation of

       Phi(t) = product_{k>=1} sinc(t/2^k),  sinc z = sin(z)/z,

   followed by numerical integration to recover the Fabius CDF.
3. Direct tests of the shifted Euler--Maclaurin collapse, the first-alias
   formula, exact phase cubature, and Thue--Morse phase filters.

The FFT calculation is not used to derive any formula in the report.  It is
an independent numerical check.  The exact CSV table is generated even when
``--skip-fft`` is selected.

Typical use
-----------

    python experiments.py --output-dir .

A higher-resolution run (larger memory footprint) is

    python experiments.py --output-dir . --grid-power 20

Dependencies: Python 3.10+, NumPy, SciPy, SymPy, mpmath, matplotlib.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, Sequence

import mpmath as mp
import numpy as np
import sympy as sp
from scipy.integrate import cumulative_trapezoid
from scipy.interpolate import PchipInterpolator


# ---------------------------------------------------------------------------
# Exact moments
# ---------------------------------------------------------------------------


def up_cumulant(n: int) -> sp.Rational:
    """Return the n-th cumulant of the probability density up(x).

    The moment generating function is

        M(t) = product_{k>=1} sinh(t/2^k)/(t/2^k).

    Hence odd cumulants vanish and

        kappa_{2r} = 2^(2r-1) B_{2r} / (r (2^(2r)-1)).
    """

    if n <= 0 or n % 2:
        return sp.Rational(0)
    r = n // 2
    return sp.simplify(
        sp.Rational(2 ** (2 * r - 1), 1)
        * sp.bernoulli(2 * r)
        / (sp.Rational(r, 1) * (2 ** (2 * r) - 1))
    )


def up_moments(max_order: int) -> list[sp.Rational]:
    """Compute u_n = integral x^n up(x) dx exactly, 0 <= n <= max_order.

    The recurrence is the standard moment--cumulant recurrence

        u_n = sum_{k=1}^n binom(n-1,k-1) kappa_k u_{n-k}.
    """

    u: list[sp.Rational] = [sp.Rational(0)] * (max_order + 1)
    u[0] = sp.Rational(1)
    for n in range(1, max_order + 1):
        u[n] = sp.simplify(
            sum(
                sp.binomial(n - 1, k - 1) * up_cumulant(k) * u[n - k]
                for k in range(1, n + 1)
            )
        )
    return u


def exact_moment_rows(max_p: int) -> list[dict[str, object]]:
    """Return exact moment data through I_max_p.

    If Y has density up on [-1,1], then X=(Y+1)/2 has density F'(x) on
    [0,1].  We use

        a_n = E[X^n] = 2^(-n) sum_j binom(n,j) u_j,
        I_p = (1-a_{p+1})/(p+1).
    """

    u = up_moments(max_p + 1)
    rows: list[dict[str, object]] = []
    for p in range(max_p + 1):
        n = p + 1
        a_n = sp.simplify(
            sum(sp.binomial(n, j) * u[j] for j in range(n + 1))
            / sp.Integer(2) ** n
        )
        i_p = sp.simplify((1 - a_n) / n)
        rows.append(
            {
                "p": p,
                "u_p": u[p],
                "a_p_plus_1": a_n,
                "I_p": i_p,
                "I_p_decimal": sp.N(i_p, 24),
            }
        )
    return rows


def write_exact_moment_table(path: Path, max_p: int = 14) -> None:
    rows = exact_moment_rows(max_p)
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(
            stream,
            fieldnames=["p", "u_p", "a_p_plus_1", "I_p", "I_p_decimal"],
        )
        writer.writeheader()
        for row in rows:
            writer.writerow({key: str(value) for key, value in row.items()})


# ---------------------------------------------------------------------------
# Fourier product and a numerical Fabius sampler
# ---------------------------------------------------------------------------


def phi_scalar(t: mp.mpf | mp.mpc, terms: int = 100) -> mp.mpf | mp.mpc:
    """High-precision scalar evaluation of Phi(t).

    ``terms=100`` is excessive for the moderate arguments used in the
    first-alias sums; the omitted tail differs from 1 by O(4^-terms).
    """

    result: mp.mpf | mp.mpc = mp.mpf(1)
    for k in range(1, terms + 1):
        z = t / (2**k)
        result *= mp.sin(z) / z if z else 1
    return result


@dataclass(frozen=True)
class FabiusSampler:
    """Numerical samples of up and an interpolating Fabius CDF."""

    x: np.ndarray
    density: np.ndarray
    cdf: np.ndarray
    fabius: Callable[[np.ndarray | float], np.ndarray | float]


def build_fabius_sampler(
    grid_power: int = 19,
    domain_length: float = 4.0,
    product_terms: int = 50,
) -> FabiusSampler:
    """Reconstruct up(x) by inverse FFT and return F(x).

    The spatial interval has length 4, while up is supported on [-1,1].
    This leaves a full unit of zero padding on both sides, preventing periodic
    copies from touching.  With NumPy's transform convention,

        density = fftshift(ifft(Phi(omega))).real / dx.

    The monotone PCHIP interpolant is applied to the CDF rather than to the
    density.  Values outside the support are set exactly to 0 or 1.
    """

    n = 1 << grid_power
    dx = domain_length / n
    omega = 2 * np.pi * np.fft.fftfreq(n, d=dx)

    phi = np.ones(n, dtype=np.float64)
    for k in range(1, product_terms + 1):
        # np.sinc(z) = sin(pi*z)/(pi*z), hence the division by pi.
        phi *= np.sinc(omega / (np.pi * (2**k)))

    density = np.fft.fftshift(np.fft.ifft(phi).real) / dx
    x = (np.arange(n) - n // 2) * dx

    # Remove only roundoff-level negative/positive noise.  No clipping of
    # meaningful values is performed.
    density[np.abs(density) < 1.0e-14] = 0.0

    cdf = np.concatenate(([0.0], cumulative_trapezoid(density, x)))
    cdf /= cdf[-1]
    interpolant = PchipInterpolator(x, cdf, extrapolate=False)

    def fabius(z: np.ndarray | float) -> np.ndarray | float:
        values = np.asarray(z, dtype=np.float64)
        y = 2.0 * values - 1.0
        result = np.empty_like(values)
        result[y <= -1.0] = 0.0
        result[y >= 1.0] = 1.0
        mask = (y > -1.0) & (y < 1.0)
        result[mask] = interpolant(y[mask])
        return result.item() if result.ndim == 0 else result

    return FabiusSampler(x=x, density=density, cdf=cdf, fabius=fabius)


# ---------------------------------------------------------------------------
# Shifted quadrature and exact Bernoulli correction
# ---------------------------------------------------------------------------


def falling_factorial(p: int, j: int) -> int:
    if j < 0 or j > p:
        return 0
    return math.factorial(p) // math.factorial(p - j)


def bernoulli_correction(p: int, panels: int, theta: float) -> float:
    """Return the finite endpoint polynomial in the shifted theorem."""

    th = sp.Float(theta, 50)
    total = sp.Rational(0)
    for r in range(1, p + 2):
        total += (
            falling_factorial(p, r - 1)
            * sp.bernoulli(r, th)
            / (sp.factorial(r) * sp.Integer(panels) ** r)
        )
    return float(sp.N(total, 30))


def shifted_sum(
    fabius: Callable[[np.ndarray | float], np.ndarray | float],
    p: int,
    panels: int,
    theta: float,
) -> float:
    k = np.arange(panels, dtype=np.float64)
    x = (k + theta) / panels
    return float(np.mean((x**p) * np.asarray(fabius(x))))


def exact_i_p(p: int) -> sp.Rational:
    return exact_moment_rows(p)[p]["I_p"]  # type: ignore[return-value]


def first_alias_remainder(
    p: int,
    theta: float,
    odd_part: int = 1,
    max_odd: int = 301,
    product_terms: int = 100,
) -> float:
    """Evaluate the first-defect series when M=2^p*odd_part, p>=1.

    The exact formula from the report is

      (-1)^(p+1) p!/M^(p+1)
      * sum_{ell odd, ell!=0}
        Phi(pi*odd_part*ell) exp(2*pi*i*ell*theta)
        /(2*pi*i*ell)^(p+1).
    """

    if p < 1 or odd_part < 1 or odd_part % 2 == 0:
        raise ValueError("Require p >= 1 and a positive odd odd_part.")

    mp.mp.dps = 70
    panels = (2**p) * odd_part
    total = mp.mpc(0)
    for ell in range(-max_odd, max_odd + 1):
        if ell == 0 or ell % 2 == 0:
            continue
        total += (
            phi_scalar(mp.pi * odd_part * ell, product_terms)
            * mp.e ** (2j * mp.pi * ell * theta)
            / (2 * mp.pi * 1j * ell) ** (p + 1)
        )
    value = ((-1) ** (p + 1)) * mp.factorial(p) * total / panels ** (p + 1)
    return float(mp.re(value))


# ---------------------------------------------------------------------------
# Phase filters
# ---------------------------------------------------------------------------


def thue_morse_sign(j: int) -> int:
    return -1 if j.bit_count() % 2 else 1


def thue_morse_phase_filter(
    fabius: Callable[[np.ndarray | float], np.ndarray | float],
    p: int,
    panels: int,
    s: int,
) -> float:
    """Compute sum_j (-1)^s_2(j) Q_{M,j/2^s,p}."""

    return sum(
        thue_morse_sign(j)
        * shifted_sum(fabius, p, panels, j / (2**s))
        for j in range(2**s)
    )


def thue_morse_leading_value(p: int, panels: int) -> sp.Rational:
    """Exact filter for s=p+1 in the stable range."""

    s = p + 1
    return sp.Rational(
        ((-1) ** s) * math.factorial(p),
        (2 ** (s * (s + 1) // 2)) * (panels**s),
    )


def phase_rule_value(
    fabius: Callable[[np.ndarray | float], np.ndarray | float],
    p: int,
    panels: int,
    nodes_and_weights: Sequence[tuple[float, float]],
) -> float:
    return sum(
        weight * shifted_sum(fabius, p, panels, theta)
        for theta, weight in nodes_and_weights
    )


# ---------------------------------------------------------------------------
# Output tables and plot
# ---------------------------------------------------------------------------


def write_numerical_checks(
    path: Path,
    sampler: FabiusSampler,
    max_p: int = 6,
) -> None:
    rows: list[dict[str, object]] = []

    # Stable shifted theorem: M=2^(p+1) works for every phase.
    for p in range(max_p + 1):
        panels = 2 ** (p + 1)
        exact = float(exact_i_p(p))
        for theta in (0.0, 0.13, 0.25, 0.37, 0.5, 0.75, 1.0):
            q = shifted_sum(sampler.fabius, p, panels, theta)
            correction = bernoulli_correction(p, panels, theta)
            rows.append(
                {
                    "experiment": "stable_shifted_collapse",
                    "p": p,
                    "panels": panels,
                    "theta": theta,
                    "observed": q - exact - correction,
                    "predicted": 0.0,
                    "difference": q - exact - correction,
                }
            )

    # First defect M=2^p.  Forced phases have exactly zero alias remainder;
    # theta=0.13 tests the full Fourier series.
    for p in range(1, max_p + 1):
        panels = 2**p
        exact = float(exact_i_p(p))
        forced = (0.0, 0.5) if p % 2 == 0 else (0.25, 0.75)
        for theta in (*forced, 0.13):
            q = shifted_sum(sampler.fabius, p, panels, theta)
            observed = q - exact - bernoulli_correction(p, panels, theta)
            predicted = first_alias_remainder(p, theta, max_odd=151)
            rows.append(
                {
                    "experiment": "first_alias",
                    "p": p,
                    "panels": panels,
                    "theta": theta,
                    "observed": observed,
                    "predicted": predicted,
                    "difference": observed - predicted,
                }
            )

    # Simpson and Boole applied in the phase variable.  These are exact for
    # p<=2 and p<=4, respectively, once the phase polynomial is stable.
    simpson = ((0.0, 1 / 6), (0.5, 4 / 6), (1.0, 1 / 6))
    boole = (
        (0.0, 7 / 90),
        (0.25, 32 / 90),
        (0.5, 12 / 90),
        (0.75, 32 / 90),
        (1.0, 7 / 90),
    )
    for name, rule, p_max in (
        ("simpson_phase_rule", simpson, 2),
        ("boole_phase_rule", boole, 4),
    ):
        for p in range(p_max + 1):
            panels = 2 ** (p + 1)
            observed = phase_rule_value(sampler.fabius, p, panels, rule)
            predicted = float(exact_i_p(p))
            rows.append(
                {
                    "experiment": name,
                    "p": p,
                    "panels": panels,
                    "theta": "multiple",
                    "observed": observed,
                    "predicted": predicted,
                    "difference": observed - predicted,
                }
            )

    # The s=p+1 Thue--Morse phase filter has a single surviving Bernoulli
    # mode.  A slightly over-resolved M is used to stay well inside the stable
    # range and away from FFT interpolation noise at very coarse grids.
    for p in range(0, min(max_p, 5) + 1):
        panels = 2 ** (p + 2)
        s = p + 1
        observed = thue_morse_phase_filter(sampler.fabius, p, panels, s)
        predicted = float(thue_morse_leading_value(p, panels))
        rows.append(
            {
                "experiment": "thue_morse_phase_filter",
                "p": p,
                "panels": panels,
                "theta": f"all j/2^{s}",
                "observed": observed,
                "predicted": predicted,
                "difference": observed - predicted,
            }
        )

    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(
            stream,
            fieldnames=[
                "experiment",
                "p",
                "panels",
                "theta",
                "observed",
                "predicted",
                "difference",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)


def write_phase_defect_plot(path: Path) -> None:
    """Plot normalized first-defect shapes for p=1,...,4."""

    import matplotlib.pyplot as plt

    mp.mp.dps = 50
    odd = np.arange(1, 302, 2)
    coeff = np.array([float(phi_scalar(mp.pi * int(ell), 80)) for ell in odd])
    theta = np.linspace(0.0, 1.0, 1601)

    fig, ax = plt.subplots(figsize=(8.0, 4.8))
    for p in range(1, 5):
        if p % 2:
            shape = np.sum(
                coeff[:, None]
                * np.cos(2 * np.pi * odd[:, None] * theta[None, :])
                / odd[:, None] ** (p + 1),
                axis=0,
            )
        else:
            shape = np.sum(
                coeff[:, None]
                * np.sin(2 * np.pi * odd[:, None] * theta[None, :])
                / odd[:, None] ** (p + 1),
                axis=0,
            )
        shape /= np.max(np.abs(shape))
        ax.plot(theta, shape, label=f"p={p}")

    ax.axhline(0.0, linewidth=0.8)
    ax.set_xlabel(r"phase $\theta$")
    ax.set_ylabel("normalized first-alias remainder")
    ax.set_title("Pure-dyadic first-defect phase functions")
    ax.legend(ncol=4)
    ax.grid(True, linewidth=0.4, alpha=0.5)
    fig.tight_layout()
    fig.savefig(path, dpi=220)
    plt.close(fig)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("."),
        help="Directory for CSV and PNG outputs (default: current directory).",
    )
    parser.add_argument(
        "--grid-power",
        type=int,
        default=19,
        help="FFT length is 2^GRID_POWER (default: 19).",
    )
    parser.add_argument(
        "--product-terms",
        type=int,
        default=50,
        help="Number of sinc factors in the FFT product (default: 50).",
    )
    parser.add_argument(
        "--skip-fft",
        action="store_true",
        help="Generate only exact moments and the Fourier-series plot.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)

    write_exact_moment_table(args.output_dir / "moment_table.csv", max_p=14)
    write_phase_defect_plot(args.output_dir / "phase_defect.png")

    if not args.skip_fft:
        sampler = build_fabius_sampler(
            grid_power=args.grid_power,
            product_terms=args.product_terms,
        )
        write_numerical_checks(
            args.output_dir / "numerical_checks.csv", sampler, max_p=6
        )

        normalization = float(np.trapezoid(sampler.density, sampler.x))
        min_density = float(np.min(sampler.density))
        print(f"FFT normalization: {normalization:.17g}")
        print(f"Minimum sampled density (roundoff diagnostic): {min_density:.3e}")

    print(f"Wrote outputs to {args.output_dir.resolve()}")


if __name__ == "__main__":
    main()
