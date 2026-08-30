#!/usr/bin/env python3
"""Numerical and exact experiments for the Fabius--Rvachev zero-bias tower.

This script accompanies the report

    Zero-Bias Towers and Spectral Peeling in the Fabius--Rvachev System.

It is intentionally self-contained.  The calculations use only the standard
scientific Python stack (NumPy, SciPy, mpmath, SymPy, and Matplotlib); no data
are downloaded.

The main objects are

    Y = sum_{j>=1} 2^{-j} U_j,      U_j ~ Uniform[-1,1],

whose density is Rvachev's up-function, and the iterated zero-bias laws
Y^[m].  The script checks or illustrates five exact results from the report:

1. a stable positive recurrence for the even moments of Y;
2. exact moment formulas for every level of the zero-bias tower;
3. the q-Pochhammer formula for collision-free occupancy patterns;
4. the Thue--Morse sign in the first nonzero value released from each
   integer Fourier zero;
5. the logarithmically slow Gaussianization rate forced by the flat Fabius
   endpoint.

It also samples Y^[m] from the occupancy representation.  This avoids the
catastrophically inefficient rejection sampler that would otherwise be needed
for the 2m-power-biased endpoint radius at large m.

Usage
-----

    python zero_bias_tower_experiments.py

All tables are written under ``data/`` and all figures under ``figures/``
relative to this file.  The random seed is fixed for reproducibility.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
import sympy as sp
from scipy.special import gammaln

# Keep regenerated vector figures repository-safe: embedded TrueType outlines,
# rather than Matplotlib's default Type 3 PDF fonts.
plt.rcParams["pdf.fonttype"] = 42
plt.rcParams["ps.fonttype"] = 42


# ---------------------------------------------------------------------------
# Basic arithmetic helpers
# ---------------------------------------------------------------------------


def odd_double_factorial(m: int) -> int:
    """Return (2m-1)!!, with (-1)!! = 1 when m=0."""

    value = 1
    for k in range(1, m + 1):
        value *= 2 * k - 1
    return value


def v2(n: int) -> int:
    """2-adic valuation of a positive integer."""

    if n <= 0:
        raise ValueError("v2 expects a positive integer")
    value = 0
    while n % 2 == 0:
        value += 1
        n //= 2
    return value


def binary_digit_sum(n: int) -> int:
    """Number of ones in the binary expansion of n."""

    if n < 0:
        raise ValueError("binary_digit_sum expects a nonnegative integer")
    return n.bit_count()


def q_pochhammer(q: Fraction, n: int) -> Fraction:
    """Finite q-Pochhammer symbol (q;q)_n for exact rational q."""

    value = Fraction(1)
    for j in range(1, n + 1):
        value *= 1 - q**j
    return value


# ---------------------------------------------------------------------------
# Exact and floating-point moments of the centered Rvachev law
# ---------------------------------------------------------------------------


def _sympy_rational_to_fraction(value: sp.Rational) -> Fraction:
    value = sp.Rational(value)
    return Fraction(int(value.p), int(value.q))


def rvachev_cumulant(k: int) -> Fraction:
    r"""Return the exact cumulant kappa_k of Y.

    Odd cumulants vanish.  For k=2r,

        kappa_{2r} = 2^{2r} B_{2r} / (2r (2^{2r}-1)).

    The sign of the Bernoulli number is included.
    """

    if k <= 0:
        raise ValueError("k must be positive")
    if k % 2 == 1:
        return Fraction(0)
    r = k // 2
    bernoulli = _sympy_rational_to_fraction(sp.bernoulli(2 * r))
    return Fraction(2 ** (2 * r), 2 * r * (2 ** (2 * r) - 1)) * bernoulli


def exact_moments(max_degree: int) -> list[Fraction]:
    r"""Compute moments mu_n=E[Y^n] exactly through ``max_degree``.

    The complete Bell recurrence

        mu_n = sum_{k=1}^n binom(n-1,k-1) kappa_k mu_{n-k}

    is convenient for low degrees and gives exact rational values.  For high
    degrees we use the positive fixed-point recurrence below, because the Bell
    recurrence contains severe cancellation.
    """

    moments = [Fraction(0) for _ in range(max_degree + 1)]
    moments[0] = Fraction(1)
    for n in range(1, max_degree + 1):
        total = Fraction(0)
        for k in range(1, n + 1):
            total += (
                Fraction(math.comb(n - 1, k - 1))
                * rvachev_cumulant(k)
                * moments[n - k]
            )
        moments[n] = total
    return moments


def even_moments_positive(max_half_degree: int) -> np.ndarray:
    r"""Compute mu_{2r}, 0<=r<=max_half_degree, stably in double precision.

    Splitting the random series at its first digit gives

        Y  =_d  (Y' + U)/2,

    where U is uniform on [-1,1].  Taking the 2r-th moment and moving the
    self-term to the left yields the *positive* recurrence

      mu_{2r} = 1/(2^{2r}-1)
                 sum_{j=0}^{r-1} binom(2r,2j)
                 mu_{2j}/(2r-2j+1).

    Every summand is nonnegative.  We evaluate binomial coefficients on the
    logarithmic scale, preventing overflow even when r is in the thousands.
    """

    if max_half_degree < 0:
        raise ValueError("max_half_degree must be nonnegative")

    moments = np.zeros(max_half_degree + 1, dtype=float)
    moments[0] = 1.0
    log_two = math.log(2.0)

    for r in range(1, max_half_degree + 1):
        n = 2 * r
        # log(2^n-1) written this way is accurate both for small and large n.
        log_denominator = n * log_two + math.log1p(-math.exp(-n * log_two))
        j = np.arange(r, dtype=float)
        k = 2.0 * j
        log_binomial = (
            gammaln(n + 1.0) - gammaln(k + 1.0) - gammaln(n - k + 1.0)
        )
        weights = np.exp(log_binomial - log_denominator) / (n - k + 1.0)
        moments[r] = float(np.dot(weights, moments[:r]))

    return moments


def tower_even_moment(
    level: int, half_degree: int, base_even_moments: Sequence[float]
) -> float:
    r"""Return E[(Y^[level])^(2*half_degree)] from the closed formula.

    For m=level and r=half_degree,

      E[(Y^[m])^{2r}]
        = (2m-1)!! (2r-1)!!/(2m+2r-1)!!
          * mu_{2m+2r}/mu_{2m}.
    """

    m = level
    r = half_degree
    if m < 0 or r < 0:
        raise ValueError("level and half_degree must be nonnegative")
    if m + r >= len(base_even_moments):
        raise ValueError("base moment table is too short")

    denominator = odd_double_factorial(m + r)
    prefactor = odd_double_factorial(m) * odd_double_factorial(r) / denominator
    return float(prefactor * base_even_moments[m + r] / base_even_moments[m])


# ---------------------------------------------------------------------------
# The Gamma--zeta periodic correction from the negative-Laplace expansion
# ---------------------------------------------------------------------------


def periodic_fourier_coefficient(k: int) -> mp.mpc:
    r"""Fourier coefficient of the repository's periodic function Psi.

    With L=log 2 and chi_k=2*pi*i*k/L,

        Psi_hat(k) = -Gamma(-chi_k) zeta(1-chi_k)/L,   k != 0,
        Psi_hat(0) = 0.

    The Gamma factor makes the series exponentially convergent.
    """

    if k == 0:
        return mp.mpc(0)
    log_two = mp.log(2)
    chi = 2 * mp.pi * 1j * k / log_two
    return -mp.gamma(-chi) * mp.zeta(1 - chi) / log_two


def periodic_psi(theta: float, modes: int = 12) -> float:
    """Evaluate Psi(theta) by a symmetric Fourier truncation."""

    value = mp.mpc(0)
    for k in range(-modes, modes + 1):
        if k:
            value += periodic_fourier_coefficient(k) * mp.e ** (
                2 * mp.pi * 1j * k * theta
            )
    return float(mp.re(value))


def periodic_psi_prime(theta: float, modes: int = 12) -> float:
    """Evaluate Psi'(theta) by termwise Fourier differentiation."""

    value = mp.mpc(0)
    for k in range(-modes, modes + 1):
        if k:
            value += (
                2
                * mp.pi
                * 1j
                * k
                * periodic_fourier_coefficient(k)
                * mp.e ** (2 * mp.pi * 1j * k * theta)
            )
    return float(mp.re(value))


# ---------------------------------------------------------------------------
# Thue--Morse release values at peeled Fourier zeros
# ---------------------------------------------------------------------------


def mp_sinc(x: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """sin(x)/x with the removable value at zero."""

    return mp.sin(x) / x if x != 0 else mp.mpf(1)


def odd_tail_product(u: int, terms: int = 180) -> mp.mpf:
    r"""A_u = product_{ell>=1} sinc(pi*u/2^ell), for odd positive u."""

    if u <= 0 or u % 2 == 0:
        raise ValueError("u must be a positive odd integer")
    value = mp.mpf(1)
    for ell in range(1, terms + 1):
        value *= mp_sinc(mp.pi * u / (2**ell))
    return mp.re(value)


@dataclass(frozen=True)
class ReleaseValue:
    frequency_index: int
    zero_order: int
    odd_part: int
    tail_product: mp.mpf
    released_value: mp.mpf
    predicted_sign: int


def released_fourier_value(n: int, exact: Sequence[Fraction]) -> ReleaseValue:
    r"""First nonzero tower value at t=2*pi*n.

    If r=v_2(n)+1 and u=n/2^{r-1}, then

      phi_r(2*pi*n)
        = (-1)^{r+1} r!(2r-1)!! A_u
          /(mu_{2r}(2*pi*n)^{2r}).

    The sign of A_u is the Thue--Morse sign
    (-1)^{s_2((u-1)/2)}.
    """

    if n <= 0:
        raise ValueError("n must be positive")
    r = v2(n) + 1
    u = n // (2 ** (r - 1))
    if 2 * r >= len(exact):
        raise ValueError("exact moment table is too short")

    tail = odd_tail_product(u)
    mu = mp.mpf(exact[2 * r].numerator) / exact[2 * r].denominator
    value = (
        (-1) ** (r + 1)
        * math.factorial(r)
        * odd_double_factorial(r)
        * tail
        / (mu * (2 * mp.pi * n) ** (2 * r))
    )
    sign = (-1) ** (r + 1 + binary_digit_sum((u - 1) // 2))
    return ReleaseValue(n, r, u, tail, value, sign)


# ---------------------------------------------------------------------------
# Occupancy law for the iterated zero-bias transform of a geometric sum
# ---------------------------------------------------------------------------


def local_occupancy_weights(coefficient: float, level: int) -> np.ndarray:
    r"""Weights c^(2k)/(k!(2k+1)!!), 0<=k<=level.

    The recurrence

        w_k/w_{k-1} = c^2/[k(2k+1)]

    avoids separate factorial evaluations.
    """

    weights = np.zeros(level + 1, dtype=float)
    weights[0] = 1.0
    c2 = coefficient * coefficient
    for k in range(1, level + 1):
        weights[k] = weights[k - 1] * c2 / (k * (2 * k + 1))
    return weights


@dataclass
class OccupancySampler:
    """Dynamic-programming sampler for the q-geometric occupancy law.

    The infinite digit set is truncated after ``digit_count`` places.  For
    q=1/2 and digit_count=48 the omitted total spatial scale is below 4e-15;
    the probability that a bias hit lands there is even smaller.
    """

    q: float
    level: int
    digit_count: int = 48

    def __post_init__(self) -> None:
        if not (0.0 < self.q < 1.0):
            raise ValueError("q must lie in (0,1)")
        if self.level < 0:
            raise ValueError("level must be nonnegative")
        if self.digit_count <= 0:
            raise ValueError("digit_count must be positive")

        self.coefficients = (1.0 - self.q) * self.q ** np.arange(self.digit_count)
        self.weights = np.array(
            [local_occupancy_weights(c, self.level) for c in self.coefficients]
        )

        # suffix[j,r] is the coefficient of x^r in the product of local
        # generating functions for digits j,j+1,... .
        self.suffix = np.zeros((self.digit_count + 1, self.level + 1))
        self.suffix[self.digit_count, 0] = 1.0
        for j in range(self.digit_count - 1, -1, -1):
            for remaining in range(self.level + 1):
                self.suffix[j, remaining] = sum(
                    self.weights[j, k] * self.suffix[j + 1, remaining - k]
                    for k in range(remaining + 1)
                )

        if self.suffix[0, self.level] <= 0.0:
            raise ArithmeticError("occupancy partition function underflowed")

    def sample(self, sample_count: int, seed: int) -> np.ndarray:
        r"""Sample the level-m tower law.

        Conditional on occupancy k_j, the j-th uniform digit is replaced by

            2*Beta(k_j+1,k_j+1)-1,

        which is exactly its k_j-fold zero-bias transform.  Digits with
        k_j=0 remain uniform.
        """

        if sample_count <= 0:
            raise ValueError("sample_count must be positive")
        rng = np.random.default_rng(seed)
        samples = np.empty(sample_count, dtype=float)

        for sample_index in range(sample_count):
            remaining = self.level
            value = 0.0

            for j, coefficient in enumerate(self.coefficients):
                if remaining:
                    probabilities = np.array(
                        [
                            self.weights[j, k]
                            * self.suffix[j + 1, remaining - k]
                            for k in range(remaining + 1)
                        ],
                        dtype=float,
                    )
                    probabilities /= probabilities.sum()
                    occupancy = int(
                        rng.choice(remaining + 1, p=probabilities)
                    )
                else:
                    occupancy = 0

                digit = 2.0 * rng.beta(occupancy + 1, occupancy + 1) - 1.0
                value += coefficient * digit
                remaining -= occupancy

            if remaining != 0:
                raise ArithmeticError("occupancy truncation lost a bias hit")

            # The un-biased geometric tail equals q^J times an independent
            # copy of Y_q.  Thirty additional digits make its approximation
            # far smaller than double-precision plotting accuracy.
            tail_copy = 0.0
            for ell in range(30):
                tail_copy += (
                    (1.0 - self.q)
                    * self.q**ell
                    * rng.uniform(-1.0, 1.0)
                )
            value += self.q**self.digit_count * tail_copy
            samples[sample_index] = value

        return samples


def collision_free_probability_half(level: int, exact: Sequence[Fraction]) -> Fraction:
    r"""Exact collision-free probability for q=1/2.

    The general formula is

      P_distinct = (2m-1)!! m! / (mu_{2m} 3^m)
                   * (1-q)^{2m} q^{m(m-1)}/(q^2;q^2)_m.
    """

    m = level
    if m <= 0:
        return Fraction(1)
    if 2 * m >= len(exact):
        raise ValueError("exact moment table is too short")

    q = Fraction(1, 2)
    numerator = Fraction(odd_double_factorial(m) * math.factorial(m), 1)
    numerator *= (1 - q) ** (2 * m) * q ** (m * (m - 1))
    denominator = exact[2 * m] * 3**m * q_pochhammer(q * q, m)
    return numerator / denominator


# ---------------------------------------------------------------------------
# Table and figure generation
# ---------------------------------------------------------------------------


def write_csv(path: Path, fieldnames: Sequence[str], rows: Iterable[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def generate_tables(output_root: Path, moments: np.ndarray) -> None:
    data_dir = output_root / "data"
    exact = exact_moments(40)

    # Low exact moments, useful for independently checking normalizations.
    exact_rows = []
    for r in range(0, 11):
        value = exact[2 * r]
        exact_rows.append(
            {
                "r": r,
                "moment": f"{value.numerator}/{value.denominator}",
                "decimal": f"{float(value):.17g}",
            }
        )
    write_csv(data_dir / "exact_even_moments.csv", ["r", "moment", "decimal"], exact_rows)

    # High-moment ratio and its leading logarithmic normalization.
    ratio_rows = []
    log_two = math.log(2.0)
    for m in range(2, len(moments) - 1):
        ratio = moments[m + 1] / moments[m]
        gap = 1.0 - ratio
        leading = math.log(2.0 * m) / (m * log_two)
        ratio_rows.append(
            {
                "tower_level_m": m,
                "mu_2m": f"{moments[m]:.17g}",
                "mu_2m_plus_2_over_mu_2m": f"{ratio:.17g}",
                "gap": f"{gap:.17g}",
                "leading_gap": f"{leading:.17g}",
                "gap_over_leading": f"{gap / leading:.17g}",
            }
        )
    write_csv(
        data_dir / "high_moment_ratios.csv",
        [
            "tower_level_m",
            "mu_2m",
            "mu_2m_plus_2_over_mu_2m",
            "gap",
            "leading_gap",
            "gap_over_leading",
        ],
        ratio_rows,
    )

    # Exact collision-free occupancy probabilities for the dyadic law.
    collision_rows = []
    for m in range(1, 9):
        probability = collision_free_probability_half(m, exact)
        collision_rows.append(
            {
                "m": m,
                "exact_probability": f"{probability.numerator}/{probability.denominator}",
                "decimal_probability": f"{float(probability):.17g}",
            }
        )
    write_csv(
        data_dir / "collision_free_probabilities.csv",
        ["m", "exact_probability", "decimal_probability"],
        collision_rows,
    )

    # First released Fourier value at each integer lattice zero.
    mp.mp.dps = 80
    release_rows = []
    for n in range(1, 33):
        record = released_fourier_value(n, exact)
        release_rows.append(
            {
                "N": n,
                "r=v2(N)+1": record.zero_order,
                "odd_part_u": record.odd_part,
                "A_u": mp.nstr(record.tail_product, 25),
                "phi_r(2*pi*N)": mp.nstr(record.released_value, 25),
                "predicted_sign": record.predicted_sign,
                "observed_sign": 1 if record.released_value > 0 else -1,
            }
        )
    write_csv(
        data_dir / "released_fourier_values.csv",
        [
            "N",
            "r=v2(N)+1",
            "odd_part_u",
            "A_u",
            "phi_r(2*pi*N)",
            "predicted_sign",
            "observed_sign",
        ],
        release_rows,
    )

    # Convergence of the first four scaled even moments to Gaussian values.
    tower_rows = []
    selected_levels = [1, 2, 3, 5, 10, 20, 50, 100, 200, 500, 1000]
    for m in selected_levels:
        if m + 4 >= len(moments):
            continue
        row: dict[str, int | str] = {"m": m}
        for r in range(1, 5):
            scaled = (2.0 * m) ** r * tower_even_moment(m, r, moments)
            gaussian = float(odd_double_factorial(r))
            row[f"scaled_moment_{2*r}"] = f"{scaled:.17g}"
            row[f"ratio_to_gaussian_{2*r}"] = f"{scaled / gaussian:.17g}"
        tower_rows.append(row)
    fields = ["m"]
    for r in range(1, 5):
        fields.extend([f"scaled_moment_{2*r}", f"ratio_to_gaussian_{2*r}"])
    write_csv(data_dir / "tower_moment_convergence.csv", fields, tower_rows)


def plot_moment_ratio(output_root: Path, moments: np.ndarray) -> None:
    figure_dir = output_root / "figures"
    m = np.arange(4, len(moments) - 1)
    ratio = moments[m + 1] / moments[m]
    gap = 1.0 - ratio
    leading = np.log(2.0 * m) / (m * math.log(2.0))

    plt.figure(figsize=(7.3, 4.4))
    plt.plot(m, gap / leading, label=r"$(1-\mu_{2m+2}/\mu_{2m})/[\log(2m)/(m\log2)]$")
    plt.axhline(1.0, linewidth=1.0, label="predicted limit")
    plt.xscale("log")
    plt.xlabel(r"tower level $m$")
    plt.ylabel("normalized high-moment gap")
    plt.title("Logarithmic endpoint scale in Rvachev high moments")
    plt.grid(True, alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(figure_dir / "moment_ratio_convergence.pdf")
    plt.savefig(figure_dir / "moment_ratio_convergence.png", dpi=180)
    plt.close()


def plot_tower_moments(output_root: Path, moments: np.ndarray) -> None:
    figure_dir = output_root / "figures"
    levels = np.unique(np.geomspace(1, len(moments) - 6, 180).astype(int))

    plt.figure(figsize=(7.3, 4.5))
    for r in range(1, 5):
        values = np.array(
            [
                (2.0 * m) ** r
                * tower_even_moment(int(m), r, moments)
                / odd_double_factorial(r)
                for m in levels
            ]
        )
        plt.plot(levels, values, label=rf"moment order ${2*r}$")
    plt.axhline(1.0, linewidth=1.0, label="Gaussian value")
    plt.xscale("log")
    plt.xlabel(r"tower level $m$")
    plt.ylabel("scaled moment / Gaussian moment")
    plt.title(r"Gaussianization of $\sqrt{2m}\,Y^{[m]}$")
    plt.grid(True, alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(figure_dir / "tower_moment_convergence.pdf")
    plt.savefig(figure_dir / "tower_moment_convergence.png", dpi=180)
    plt.close()


def plot_periodic_profile(output_root: Path) -> None:
    figure_dir = output_root / "figures"
    mp.mp.dps = 55
    theta = np.linspace(0.0, 1.0, 801)

    # Computing Gamma and zeta at every plotting point is needlessly costly.
    # Evaluate the exponentially decaying Fourier coefficients once and then
    # use vectorized complex exponentials in ordinary double precision.
    modes = np.array([k for k in range(-12, 13) if k != 0], dtype=int)
    coefficients = np.array(
        [complex(periodic_fourier_coefficient(int(k))) for k in modes],
        dtype=complex,
    )
    exponentials = np.exp(2j * np.pi * np.outer(theta, modes))
    derivative = np.real(
        exponentials @ (2j * np.pi * modes * coefficients)
    )

    plt.figure(figsize=(7.3, 4.2))
    plt.plot(theta, derivative)
    plt.xlabel(r"phase $\theta$")
    plt.ylabel(r"$\Psi'(\theta)$")
    plt.title("Gamma--zeta phase derivative inherited by the tower")
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    plt.savefig(figure_dir / "periodic_phase_derivative.pdf")
    plt.savefig(figure_dir / "periodic_phase_derivative.png", dpi=180)
    plt.close()


def plot_spectral_peeling(output_root: Path, max_n: int = 64, max_level: int = 7) -> None:
    figure_dir = output_root / "figures"
    x_values: list[int] = []
    y_values: list[int] = []
    sizes: list[float] = []

    for level in range(max_level + 1):
        for n in range(1, max_n + 1):
            multiplicity = max(v2(n) + 1 - level, 0)
            if multiplicity:
                x_values.append(n)
                y_values.append(level)
                sizes.append(22.0 * multiplicity * multiplicity)

    plt.figure(figsize=(8.0, 4.5))
    plt.scatter(x_values, y_values, s=sizes)
    plt.xlabel(r"integer frequency index $N$ in $t=2\pi N$")
    plt.ylabel(r"tower level $m$")
    plt.yticks(range(max_level + 1))
    plt.title("Inherited lattice zeros under spectral peeling")
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    plt.savefig(figure_dir / "spectral_peeling.pdf")
    plt.savefig(figure_dir / "spectral_peeling.png", dpi=180)
    plt.close()


def plot_density_samples(
    output_root: Path,
    moments: np.ndarray,
    sample_count: int,
    seed: int,
) -> None:
    figure_dir = output_root / "figures"
    levels = [1, 3, 10, 30]
    bins = np.linspace(-4.0, 4.0, 181)

    sampled: dict[int, np.ndarray] = {}

    plt.figure(figsize=(7.5, 4.7))
    for offset, level in enumerate(levels):
        sampler = OccupancySampler(q=0.5, level=level, digit_count=48)
        samples = sampler.sample(sample_count, seed + 1009 * offset)
        sampled[level] = samples
        scaled = math.sqrt(2.0 * level) * samples
        plt.hist(
            scaled,
            bins=bins,
            density=True,
            histtype="step",
            linewidth=1.1,
            label=rf"$m={level}$",
        )

    x = np.linspace(-4.0, 4.0, 801)
    normal_density = np.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)
    plt.plot(x, normal_density, linewidth=1.4, label="standard normal")
    plt.xlabel("scaled coordinate")
    plt.ylabel("density")
    plt.title(r"Occupancy-sampled densities of $\sqrt{2m}\,Y^{[m]}$")
    plt.grid(True, alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(figure_dir / "tower_density_monte_carlo.pdf")
    plt.savefig(figure_dir / "tower_density_monte_carlo.png", dpi=180)
    plt.close()

    # Record empirical variance as a sampler check against the exact formula.
    check_rows = []
    for level in levels:
        samples = sampled[level]
        exact_variance = tower_even_moment(level, 1, moments)
        check_rows.append(
            {
                "m": level,
                "sample_count": sample_count,
                "empirical_mean": f"{samples.mean():.17g}",
                "empirical_variance": f"{samples.var():.17g}",
                "exact_variance": f"{exact_variance:.17g}",
                "relative_variance_error": f"{samples.var()/exact_variance-1.0:.17g}",
            }
        )
    write_csv(
        output_root / "data" / "occupancy_sampler_checks.csv",
        [
            "m",
            "sample_count",
            "empirical_mean",
            "empirical_variance",
            "exact_variance",
            "relative_variance_error",
        ],
        check_rows,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-level",
        type=int,
        default=2000,
        help="largest half-degree in the floating moment table (default: 2000)",
    )
    parser.add_argument(
        "--samples",
        type=int,
        default=30000,
        help="Monte Carlo samples per displayed tower level (default: 30000)",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=20260830,
        help="random seed (default: 20260830)",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.max_level < 40:
        raise ValueError("--max-level must be at least 40")

    root = Path(__file__).resolve().parent
    (root / "data").mkdir(exist_ok=True)
    (root / "figures").mkdir(exist_ok=True)

    print(f"Computing even moments through mu_{2*args.max_level} ...")
    moments = even_moments_positive(args.max_level)

    print("Writing exact and numerical tables ...")
    generate_tables(root, moments)

    print("Generating deterministic figures ...")
    plot_moment_ratio(root, moments)
    plot_tower_moments(root, moments)
    plot_periodic_profile(root)
    plot_spectral_peeling(root)

    print("Sampling tower densities from the occupancy law ...")
    plot_density_samples(root, moments, args.samples, args.seed)

    print("Done.  Outputs are in data/ and figures/.")


if __name__ == "__main__":
    main()
