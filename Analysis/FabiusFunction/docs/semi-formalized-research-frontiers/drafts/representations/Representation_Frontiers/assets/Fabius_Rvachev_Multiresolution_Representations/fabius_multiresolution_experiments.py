#!/usr/bin/env python3
"""Reproducible experiments for the Fabius--Rvachev representation report.

The program checks and illustrates the report's dyadic multiresolution,
Fourier-sampling, binomial-layer, Bessel, and Bernstein formulas.  Exact
arithmetic is used whenever a claim is arithmetic: every dyadic Fabius value,
Faber--Schauder coefficient, energy partial sum, and triangular coefficient is
computed with ``fractions.Fraction`` or Python integers.  Floating-point work
is deliberately based on independent representations (the sinc product,
period-two Fourier inversion, numerical quadrature, and Kummer functions).

No network access is used.  Dependencies are Python 3.10+, NumPy, SciPy,
mpmath, and Matplotlib.  Running the file creates all tables and figures next
to it.

Typical invocation
------------------

    python fabius_multiresolution_experiments.py --max-exact-level 16

The default parameters are the ones used for the bundled report.  A smaller
``--max-exact-level`` gives a faster exploratory run; level 16 is already
quite modest because the exact dyadic evaluator is a terminating bit
recursion rather than numerical quadrature.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
from scipy import integrate, special
from scipy.fft import dct
from scipy.stats import binom


ROOT = Path(__file__).resolve().parent
FIGURES = ROOT / "figures"
FIGURES.mkdir(exist_ok=True)


# ---------------------------------------------------------------------------
# Exact inverse-power values and arbitrary dyadic evaluation
# ---------------------------------------------------------------------------


def inverse_power_values(max_n: int) -> list[Fraction]:
    r"""Return ``V_n = F(2^{-n})`` exactly for ``0 <= n <= max_n``.

    The triangular recurrence is one of the established exact-arithmetic
    identities in the ProveIt development:

        V_n = 1 / (2^{n(n-1)/2}(2^n-1))
              * sum_{k=0}^{n-1}
                2^{k(k-1)/2} V_k / (n-k+1)!.

    ``V_0=F(1)=1``.  Every operation below is rational.
    """

    if max_n < 0:
        raise ValueError("max_n must be nonnegative")
    values = [Fraction(1, 1)]
    for n in range(1, max_n + 1):
        total = Fraction(0, 1)
        for k in range(n):
            total += (
                Fraction(2 ** (k * (k - 1) // 2), math.factorial(n - k + 1))
                * values[k]
            )
        denominator = 2 ** (n * (n - 1) // 2) * (2**n - 1)
        values.append(total / denominator)
    return values


def exact_dyadic_table(exponent: int, inverse_values: Sequence[Fraction]) -> list[Fraction]:
    r"""Return all values ``F(a/2^exponent)`` exactly.

    The terminating highest-bit recursion used here is the Taylor-block
    evaluator from the repository.  If ``a=2^b+q`` and ``r=exponent-b``, then

        F(a/2^exponent)
          = sum_{j=0}^r 2^{j(j+1)/2} V_{r-j}
              (q/2^exponent)^j / j! - F(q/2^exponent).

    Since ``q<a``, filling the table from left to right automatically memoizes
    every recursive subproblem.  The cost is O(exponent*2^exponent) rational
    operations and no approximation is involved.
    """

    if exponent < 0:
        raise ValueError("exponent must be nonnegative")
    if len(inverse_values) <= exponent:
        raise ValueError("inverse_values does not contain enough entries")

    denominator = 1 << exponent
    values: list[Fraction] = [Fraction(0, 1)] * (denominator + 1)
    values[denominator] = Fraction(1, 1)

    for a in range(1, denominator):
        highest_bit = a.bit_length() - 1
        order = exponent - highest_bit
        remainder = a - (1 << highest_bit)
        y = Fraction(remainder, denominator)

        block = Fraction(0, 1)
        y_power = Fraction(1, 1)
        factorial = 1
        for j in range(order + 1):
            if j > 0:
                y_power *= y
                factorial *= j
            block += (
                Fraction(2 ** (j * (j + 1) // 2), factorial)
                * inverse_values[order - j]
                * y_power
            )
        values[a] = block - values[remainder]

    return values


# ---------------------------------------------------------------------------
# Exact Faber--Schauder coefficients and energy sums
# ---------------------------------------------------------------------------


def faber_levels(
    dyadic_values: Sequence[Fraction], table_exponent: int, levels: int
) -> list[list[Fraction]]:
    r"""Return exact midpoint defects ``c_{m,k}`` for ``m < levels``.

    For the cell ``[k/2^m,(k+1)/2^m]``,

        c_{m,k} = F((2k+1)/2^{m+1})
                  - (F(k/2^m)+F((k+1)/2^m))/2.

    The supplied table may be finer than the requested levels; exact
    subsampling then recovers the coarser values.
    """

    if not (0 <= levels <= table_exponent):
        raise ValueError("levels must lie between 0 and table_exponent")
    expected = (1 << table_exponent) + 1
    if len(dyadic_values) != expected:
        raise ValueError("dyadic_values has the wrong length")

    result: list[list[Fraction]] = []
    for m in range(levels):
        stride = 1 << (table_exponent - (m + 1))
        row: list[Fraction] = []
        for k in range(1 << m):
            left = dyadic_values[(2 * k) * stride]
            midpoint = dyadic_values[(2 * k + 1) * stride]
            right = dyadic_values[(2 * k + 2) * stride]
            row.append(midpoint - (left + right) / 2)
        result.append(row)
    return result


def energy_partial_sums(levels: Sequence[Sequence[Fraction]]) -> list[Fraction]:
    r"""Return rational partial sums for ``A_2 = integral_0^1 F(x)^2 dx``.

    Haar Parseval gives the exact positive series

        A_2 = 1/4 + sum_{m>=0} 2^m sum_k c_{m,k}^2.

    The ``J``-th returned value includes levels ``0,...,J-1``.  Level zero is
    identically zero by the symmetry ``F(1/2)=1/2``, but it is retained so the
    indexing agrees with the report.
    """

    total = Fraction(1, 4)
    partials: list[Fraction] = []
    for m, row in enumerate(levels):
        total += (1 << m) * sum((c * c for c in row), Fraction(0, 1))
        partials.append(total)
    return partials


def beta_coefficient(q: int) -> Fraction:
    r"""The ``q``-th all-orders coefficient in the level-energy expansion.

        beta_q = (-1)^{q+1}
                 2^{q(q+1)+1}(2^{2q}-1)/(2q+2)!.
    """

    if q < 1:
        raise ValueError("q must be positive")
    sign = 1 if q % 2 == 1 else -1
    return Fraction(
        sign * 2 ** (q * (q + 1) + 1) * (2 ** (2 * q) - 1),
        math.factorial(2 * q + 2),
    )


def gamma_coefficient(q: int) -> Fraction:
    r"""Tail coefficient ``gamma_q=beta_q/(1-4^{-q})``."""

    beta = beta_coefficient(q)
    return beta / (Fraction(1, 1) - Fraction(1, 4**q))


def accelerated_energy(partial: Fraction, level_count: int, order: int) -> mp.mpf:
    r"""Accelerate a rational energy partial sum by ``order`` tail terms.

    If ``R_J`` contains levels below ``J``, then

        A_2 - R_J ~ A_2 sum_{q>=1} gamma_q 4^{-qJ}.

    Solving this truncated relation for ``A_2`` gives the estimator below.
    """

    denominator = Fraction(1, 1)
    for q in range(1, order + 1):
        denominator -= gamma_coefficient(q) * Fraction(1, 4 ** (q * level_count))
    rational_estimate = partial / denominator
    return mp.mpf(rational_estimate.numerator) / rational_estimate.denominator


# ---------------------------------------------------------------------------
# Independent sinc-product and period-two Fourier evaluators
# ---------------------------------------------------------------------------


def sinc(value: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Return ``sin(value)/value`` with its removable value at zero."""

    if value == 0:
        return mp.mpf(1)
    return mp.sin(value) / value


def phi_product(
    t: mp.mpf | mp.mpc, factors: int = 180
) -> mp.mpf | mp.mpc:
    r"""Evaluate the angular Fourier transform of ``up``.

        Phi(t) = product_{j>=1} sinc(t/2^j).

    For bounded ``t``, the omitted logarithmic tail is O(|t|^2 4^{-factors}).
    """

    value: mp.mpf | mp.mpc = mp.mpf(1)
    scale = mp.mpf(2)
    for _ in range(factors):
        value *= sinc(t / scale)
        scale *= 2
    return value


def odd_sample_coefficients(modes: int, factors: int = 180) -> tuple[mp.mpf, ...]:
    r"""Return ``Phi((2m+1)pi)`` for the period-two cosine expansion."""

    return tuple(mp.re(phi_product((2 * m + 1) * mp.pi, factors)) for m in range(modes))


@dataclass(frozen=True)
class FourierReference:
    """Fast vectorized evaluator built from the independent sinc samples."""

    coefficients: np.ndarray

    @property
    def modes(self) -> int:
        return int(self.coefficients.size)

    def up(self, values: np.ndarray | Sequence[float] | float) -> np.ndarray:
        r"""Evaluate ``up`` using its established period-two cosine series.

            up(x) = 1/2 + sum_{m>=0} Phi((2m+1)pi)
                                  cos((2m+1)pi x),  |x|<=1.
        """

        array = np.asarray(values, dtype=float)
        flat = array.reshape(-1)
        result = np.zeros_like(flat)
        inside = np.abs(flat) <= 1.0
        if np.any(inside):
            frequencies = (2 * np.arange(self.modes) + 1) * np.pi
            phase = np.outer(flat[inside], frequencies)
            result[inside] = 0.5 + np.cos(phase) @ self.coefficients
        return result.reshape(array.shape)

    def fabius(self, values: np.ndarray | Sequence[float] | float) -> np.ndarray:
        """Evaluate the bounded Fabius CDF from ``F(x)=up(x-1)`` on [0,1]."""

        array = np.asarray(values, dtype=float)
        result = np.zeros_like(array)
        result[array >= 1.0] = 1.0
        interior = (array > 0.0) & (array < 1.0)
        if np.any(interior):
            result[interior] = self.up(array[interior] - 1.0)
        return result


def make_fourier_reference(modes: int = 160) -> FourierReference:
    coefficients_mp = odd_sample_coefficients(modes)
    return FourierReference(np.asarray([float(x) for x in coefficients_mp], dtype=float))


# ---------------------------------------------------------------------------
# Faber and Haar transform checks
# ---------------------------------------------------------------------------


def piecewise_linear_from_exact(
    dyadic_values: Sequence[Fraction], exponent: int, points: np.ndarray
) -> np.ndarray:
    """Evaluate the exact-node dyadic linear interpolant on a NumPy grid."""

    nodes = np.linspace(0.0, 1.0, (1 << exponent) + 1)
    values = np.asarray([float(v) for v in dyadic_values], dtype=float)
    return np.interp(points, nodes, values)


def phi_from_haar(
    t: mp.mpf | mp.mpc,
    levels: Sequence[Sequence[Fraction]],
) -> mp.mpf | mp.mpc:
    r"""Evaluate the finite Haar--sinc-squared expansion of ``Phi``.

        Phi(t) = sinc(t)
          + sum_{m,k} 2^m c_{m,k}/(i t)
              exp(i t(1-2k/2^m)) (1-exp(-i t/2^m))^2.

    The value at zero is assigned by continuity.  The exact coefficients are
    converted to mpmath only at the last possible moment.
    """

    if t == 0:
        return mp.mpf(1)
    total: mp.mpf | mp.mpc = sinc(t)
    imaginary_unit = mp.j
    for m, row in enumerate(levels):
        scale = 1 << m
        step_phase = mp.e ** (-2 * imaginary_unit * t / scale)
        phase = mp.e ** (imaginary_unit * t)
        factor = (1 - mp.e ** (-imaginary_unit * t / scale)) ** 2
        prefactor = scale * factor / (imaginary_unit * t)
        for coefficient in row:
            c = mp.mpf(coefficient.numerator) / coefficient.denominator
            total += prefactor * c * phase
            phase *= step_phase
    return total


# ---------------------------------------------------------------------------
# Triangular Bernoulli/binomial layer
# ---------------------------------------------------------------------------


def phi_triangular(t: mp.mpf | mp.mpc, max_layer: int) -> mp.mpf | mp.mpc:
    r"""Finite triangular product ``prod_{n=2}^N cos(t/2^n)^{n-1}``."""

    value: mp.mpf | mp.mpc = mp.mpf(1)
    for n in range(2, max_layer + 1):
        value *= mp.cos(t / (2**n)) ** (n - 1)
    return value


def triangular_polynomial(max_layer: int) -> list[int]:
    r"""Return coefficients of

        P_N(q)=prod_{n=2}^N (1+q^{2^{N-n}})^{n-1}.

    Repeated shift-and-add multiplication is faster and simpler than a generic
    symbolic polynomial package.  Coefficients are exact arbitrary-precision
    integers.
    """

    if max_layer < 2:
        return [1]
    coefficients = [1]
    for n in range(2, max_layer + 1):
        shift = 1 << (max_layer - n)
        for _ in range(n - 1):
            old_length = len(coefficients)
            updated = coefficients + [0] * shift
            for index in range(old_length):
                updated[index + shift] += coefficients[index]
            coefficients = updated
    return coefficients


def log_concavity_certificate(coefficients: Sequence[int]) -> tuple[bool, int | None]:
    """Check ``a_k^2 >= a_{k-1}a_{k+1}`` exactly at every interior index."""

    for k in range(1, len(coefficients) - 1):
        if coefficients[k] * coefficients[k] < coefficients[k - 1] * coefficients[k + 1]:
            return False, k
    return True, None


# ---------------------------------------------------------------------------
# Shannon reconstruction from odd samples
# ---------------------------------------------------------------------------


def phi_shannon_odd(
    z: mp.mpf | mp.mpc,
    positive_pairs: int,
    factors: int = 180,
) -> mp.mpf | mp.mpc:
    r"""Truncate the odd-lattice cardinal expansion.

        Phi(z) = sin(z)/z
          - 2 z sin(z) sum_{m>=0}
              Phi((2m+1)pi)/(z^2-(2m+1)^2 pi^2).

    The sample sequence is rapidly decreasing because ``up`` is smooth and
    compactly supported.  At a sample point the formula is interpreted by its
    removable limit; the experiment points deliberately avoid those poles.
    """

    total: mp.mpf | mp.mpc = sinc(z)
    correction: mp.mpf | mp.mpc = mp.mpf(0)
    for m in range(positive_pairs):
        sample_location = (2 * m + 1) * mp.pi
        sample = phi_product(sample_location, factors)
        correction += sample / (z * z - sample_location * sample_location)
    return total - 2 * z * mp.sin(z) * correction


# ---------------------------------------------------------------------------
# Chebyshev/Bessel coefficients
# ---------------------------------------------------------------------------


def phi_product_float(t: float, factors: int = 80) -> float:
    """Double-precision scalar sinc product for SciPy quadrature."""

    value = 1.0
    scale = 2.0
    for _ in range(factors):
        argument = t / scale
        if argument != 0.0:
            value *= math.sin(argument) / argument
        scale *= 2.0
    return value


def chebyshev_coefficients_dct(reference: FourierReference, degree: int = 12) -> np.ndarray:
    r"""Compute continuous Chebyshev coefficients by a fine cosine quadrature.

    On ``x=cos(theta)``, the coefficients are ordinary cosine coefficients of
    ``up(cos(theta))``.  A DCT-I on a sufficiently fine Lobatto grid is the
    trapezoidal rule for this smooth periodic function.
    """

    intervals = 1 << 14
    theta = np.linspace(0.0, np.pi, intervals + 1)
    values = reference.up(np.cos(theta))
    coefficients = dct(values, type=1) / intervals
    return coefficients[: degree + 1]


def chebyshev_coefficient_bessel(order: int, cutoff: float = 96.0) -> float:
    r"""Evaluate the Bessel--sinc-product formula for one Chebyshev coefficient."""

    if order % 2 == 1:
        return 0.0

    def integrand(t: float) -> float:
        return special.jv(order, t) * phi_product_float(t)

    integral, _error = integrate.quad(
        integrand,
        0.0,
        cutoff,
        epsabs=2e-12,
        epsrel=2e-12,
        limit=500,
        points=[k * math.pi for k in range(1, int(cutoff / math.pi) + 1)],
    )
    return 2.0 * ((-1.0) ** (order // 2)) * integral / math.pi


# ---------------------------------------------------------------------------
# Bernstein limits and the hypergeometric transform
# ---------------------------------------------------------------------------


def bernstein_values(samples: np.ndarray, points: np.ndarray) -> np.ndarray:
    """Evaluate a Bernstein polynomial as a binomial expectation."""

    degree = samples.size - 1
    k = np.arange(degree + 1)
    probabilities = binom.pmf(k[None, :], degree, points[:, None])
    return probabilities @ samples


def bernstein_fourier_hypergeometric(
    up_samples: Sequence[Fraction], t: mp.mpf | mp.mpc
) -> mp.mpf | mp.mpc:
    r"""Fourier transform of the Bernstein approximant to the centered bump.

    If ``g(y)=up(2y-1)`` and ``g_k=g(k/n)``, then

        Phi_n(t) = 2 e^{it}/(n+1) sum_k g_k
                   1F1(k+1; n+2; -2it).
    """

    degree = len(up_samples) - 1
    total: mp.mpf | mp.mpc = mp.mpf(0)
    for k, sample in enumerate(up_samples):
        value = mp.mpf(sample.numerator) / sample.denominator
        total += value * mp.hyp1f1(k + 1, degree + 2, -2 * mp.j * t)
    return 2 * mp.e ** (mp.j * t) * total / (degree + 1)


# ---------------------------------------------------------------------------
# Formatting helpers
# ---------------------------------------------------------------------------


def fraction_tex(value: Fraction) -> str:
    """Format a Fraction as compact LaTeX."""

    if value.denominator == 1:
        return str(value.numerator)
    return rf"\frac{{{value.numerator}}}{{{value.denominator}}}"


def mp_text(value: mp.mpf | mp.mpc, digits: int = 30) -> str:
    """Stable text rendering for mpmath values."""

    return mp.nstr(value, n=digits, strip_zeros=False)


# ---------------------------------------------------------------------------
# Experiment driver
# ---------------------------------------------------------------------------


def run(max_exact_level: int, precision: int) -> dict[str, object]:
    mp.mp.dps = precision

    inverse = inverse_power_values(max_exact_level + 3)
    dyadic = exact_dyadic_table(max_exact_level, inverse)
    levels = faber_levels(dyadic, max_exact_level, max_exact_level)
    partials = energy_partial_sums(levels)

    # The highest available exact partial sum, accelerated by several orders,
    # serves as a numerical reference only.  Every raw partial is itself exact.
    acceleration_order = min(7, max(1, max_exact_level // 2))
    energy_estimate = accelerated_energy(
        partials[-1], max_exact_level, acceleration_order
    )

    reference = make_fourier_reference(modes=180)

    # Exact-node Faber interpolation errors against independent Fourier
    # inversion.  The theoretical bound is 4^{-J}.
    grid = np.linspace(0.0, 1.0, 32769)
    reference_f = reference.fabius(grid)
    faber_rows: list[dict[str, object]] = []
    for exponent in range(2, min(max_exact_level, 10) + 1):
        stride = 1 << (max_exact_level - exponent)
        coarse_values = dyadic[::stride]
        interpolant = piecewise_linear_from_exact(coarse_values, exponent, grid)
        error = float(np.max(np.abs(interpolant - reference_f)))
        faber_rows.append(
            {
                "level": exponent,
                "max_error": error,
                "scaled_error": error * (4**exponent),
                "bound": 4.0 ** (-exponent),
            }
        )

    # Haar transform checks against the direct sinc product.
    transform_points = [
        mp.mpf("0.3"),
        mp.mpf("1.7"),
        mp.mpf("5.2"),
        mp.mpf("10.0"),
        mp.mpf("30.0"),
        mp.mpc("3.0", "0.7"),
    ]
    haar_rows: list[dict[str, str]] = []
    haar_levels = levels[: min(max_exact_level, 14)]
    for point in transform_points:
        direct = phi_product(point)
        reconstructed = phi_from_haar(point, haar_levels)
        haar_rows.append(
            {
                "point": mp_text(point, 12),
                "direct": mp_text(direct, 24),
                "reconstructed": mp_text(reconstructed, 24),
                "absolute_error": mp_text(abs(direct - reconstructed), 8),
            }
        )

    # Triangular-product checks and exact log-concavity tests.
    triangular_transform_rows: list[dict[str, str]] = []
    for point in (mp.mpf("0.7"), mp.mpf("4.0"), mp.mpf("11.0")):
        direct = phi_product(point)
        finite = phi_triangular(point, max_layer=36)
        triangular_transform_rows.append(
            {
                "point": mp_text(point, 8),
                "sinc_product": mp_text(direct, 24),
                "triangular_product_N36": mp_text(finite, 24),
                "absolute_error": mp_text(abs(direct - finite), 8),
            }
        )

    log_concavity_rows: list[dict[str, object]] = []
    final_triangular_coefficients: list[int] = [1]
    for layer in range(2, 17):
        coefficients = triangular_polynomial(layer)
        passed, failure = log_concavity_certificate(coefficients)
        symmetric = coefficients == list(reversed(coefficients))
        peak = max(coefficients)
        first_peak = coefficients.index(peak)
        log_concavity_rows.append(
            {
                "N": layer,
                "degree": len(coefficients) - 1,
                "symmetric": symmetric,
                "log_concave": passed,
                "failure_index": failure,
                "first_peak": first_peak,
            }
        )
        if layer == 16:
            final_triangular_coefficients = coefficients

    # Shannon reconstruction at real and complex points.
    shannon_points = [
        mp.mpf("0.7"),
        mp.mpf("2.3"),
        mp.mpf("5.2"),
        mp.mpf("10.1"),
        mp.mpc("3.0", "0.7"),
        mp.mpc("8.0", "1.2"),
    ]
    shannon_rows: list[dict[str, str]] = []
    for point in shannon_points:
        direct = phi_product(point)
        reconstructed = phi_shannon_odd(point, positive_pairs=40)
        shannon_rows.append(
            {
                "point": mp_text(point, 12),
                "direct": mp_text(direct, 24),
                "reconstructed": mp_text(reconstructed, 24),
                "absolute_error": mp_text(abs(direct - reconstructed), 8),
            }
        )

    # Chebyshev coefficients: a cosine-grid computation versus the new
    # Bessel--sinc-product integral.
    chebyshev_dct = chebyshev_coefficients_dct(reference, degree=12)
    chebyshev_rows: list[dict[str, object]] = []
    for order in range(0, 13, 2):
        bessel_value = chebyshev_coefficient_bessel(order)
        chebyshev_rows.append(
            {
                "order": order,
                "dct": float(chebyshev_dct[order]),
                "bessel": bessel_value,
                "absolute_error": abs(float(chebyshev_dct[order]) - bessel_value),
            }
        )

    # Bernstein approximation errors at dyadic degrees.
    bernstein_grid = np.linspace(0.0, 1.0, 4097)
    bernstein_reference = reference.fabius(bernstein_grid)
    bernstein_rows: list[dict[str, float | int]] = []
    for exponent in range(3, min(max_exact_level, 8) + 1):
        degree = 1 << exponent
        stride = 1 << (max_exact_level - exponent)
        samples = np.asarray([float(v) for v in dyadic[::stride]], dtype=float)
        approximation = bernstein_values(samples, bernstein_grid)
        error = float(np.max(np.abs(approximation - bernstein_reference)))
        bernstein_rows.append(
            {
                "degree": degree,
                "max_error": error,
                "bound": 1.0 / degree,
            }
        )

    # One direct Kummer-transform check.  The up-samples are exactly rational.
    hyper_degree_exponent = min(5, max_exact_level)
    hyper_degree = 1 << hyper_degree_exponent
    hyper_stride = 1 << (max_exact_level - hyper_degree_exponent)
    f_samples = dyadic[::hyper_stride]
    up_samples: list[Fraction] = []
    for k in range(hyper_degree + 1):
        argument_numerator = abs(2 * k - hyper_degree)
        # up(2k/n-1)=F(1-|2k/n-1|).
        f_index = hyper_degree - argument_numerator
        up_samples.append(f_samples[f_index])
    hyper_t = mp.mpf("2.7")
    hyper_value = bernstein_fourier_hypergeometric(up_samples, hyper_t)

    # Numerically integrate the same Bernstein polynomial for an independent
    # check of the Kummer identity.
    up_samples_float = np.asarray([float(v) for v in up_samples], dtype=float)

    def bernstein_up_scalar(y: float) -> float:
        probabilities = binom.pmf(np.arange(hyper_degree + 1), hyper_degree, y)
        return float(probabilities @ up_samples_float)

    direct_real = integrate.quad(
        lambda y: 2.0
        * bernstein_up_scalar(y)
        * math.cos(float(hyper_t) * (2.0 * y - 1.0)),
        0.0,
        1.0,
        epsabs=2e-12,
        epsrel=2e-12,
        limit=300,
    )[0]
    direct_imag = -integrate.quad(
        lambda y: 2.0
        * bernstein_up_scalar(y)
        * math.sin(float(hyper_t) * (2.0 * y - 1.0)),
        0.0,
        1.0,
        epsabs=2e-12,
        epsrel=2e-12,
        limit=300,
    )[0]
    hyper_direct = mp.mpc(direct_real, direct_imag)

    # ------------------------------------------------------------------
    # Figures.  Each chart is a separate Matplotlib figure; no style or
    # explicit colors are imposed, so Matplotlib's defaults remain visible.
    # ------------------------------------------------------------------

    # Figure 1: exact-node dyadic interpolants.
    plt.figure(figsize=(8.2, 4.8))
    plt.plot(grid, reference_f, label="F (sinc-product inversion)", linewidth=2.0)
    for exponent in (2, 4, 6):
        if exponent <= max_exact_level:
            stride = 1 << (max_exact_level - exponent)
            coarse_values = dyadic[::stride]
            interpolant = piecewise_linear_from_exact(coarse_values, exponent, grid)
            plt.plot(grid, interpolant, label=rf"dyadic interpolant $J={exponent}$")
    plt.xlabel("x")
    plt.ylabel("value")
    plt.title("Exact-rational Faber--Schauder approximants")
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIGURES / "faber_approximants.png", dpi=180)
    plt.close()

    # Figure 2: raw and accelerated energy errors.
    js = np.arange(2, max_exact_level + 1)
    raw_errors = []
    accelerated_errors = []
    energy_reference_float = float(energy_estimate)
    for j in js:
        raw = float(partials[j - 1])
        accelerated = float(accelerated_energy(partials[j - 1], int(j), min(4, j // 2)))
        raw_errors.append(abs(raw - energy_reference_float))
        accelerated_errors.append(abs(accelerated - energy_reference_float))
    plt.figure(figsize=(8.2, 4.8))
    plt.semilogy(js, raw_errors, marker="o", label="raw rational partial sum")
    plt.semilogy(js, accelerated_errors, marker="s", label="four-term tail acceleration")
    plt.xlabel("number J of dyadic levels")
    plt.ylabel("absolute error")
    plt.title("Positive energy series and asymptotic acceleration")
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIGURES / "energy_convergence.png", dpi=180)
    plt.close()

    # Figure 3: odd-sample cardinal convergence.
    sample_counts = np.arange(1, 31)
    cardinal_errors = []
    cardinal_test_points = [mp.mpf("0.7"), mp.mpf("2.3"), mp.mpc("3.0", "0.7")]
    for count in sample_counts:
        error = max(
            abs(phi_product(point) - phi_shannon_odd(point, int(count)))
            for point in cardinal_test_points
        )
        cardinal_errors.append(float(error))
    plt.figure(figsize=(8.2, 4.8))
    plt.semilogy(sample_counts, cardinal_errors, marker="o")
    plt.xlabel("positive odd sample pairs retained")
    plt.ylabel("maximum absolute error")
    plt.title("Odd-lattice Shannon reconstruction of the sinc product")
    plt.tight_layout()
    plt.savefig(FIGURES / "odd_sampling_convergence.png", dpi=180)
    plt.close()

    # Figure 4: the exact triangular mass polynomial at N=12.
    triangular_plot_coefficients = triangular_polynomial(12)
    triangular_probabilities = np.asarray(triangular_plot_coefficients, dtype=float)
    triangular_probabilities /= triangular_probabilities.sum()
    triangular_lattice = np.arange(triangular_probabilities.size) / (2**12)
    plt.figure(figsize=(8.2, 4.8))
    plt.plot(triangular_lattice, triangular_probabilities)
    plt.xlabel(r"lattice point $\ell/2^{12}$")
    plt.ylabel("probability mass")
    plt.title("Triangular independent-binomial approximation")
    plt.tight_layout()
    plt.savefig(FIGURES / "triangular_distribution.png", dpi=180)
    plt.close()

    # ------------------------------------------------------------------
    # Human-readable and machine-readable result files.
    # ------------------------------------------------------------------

    results: dict[str, object] = {
        "settings": {
            "max_exact_level": max_exact_level,
            "decimal_precision": precision,
            "fourier_reference_modes": reference.modes,
            "energy_acceleration_order": acceleration_order,
        },
        "exact_inverse_power_values": [str(v) for v in inverse[: min(12, len(inverse))]],
        "low_faber_coefficients": {
            str(m): [str(c) for c in levels[m]] for m in range(min(5, len(levels)))
        },
        "energy_partials": [
            {
                "J": j,
                "fraction": str(partials[j - 1]),
                "decimal": format(float(partials[j - 1]), ".17g"),
            }
            for j in range(1, len(partials) + 1)
        ],
        "energy_estimate": mp_text(energy_estimate, 70),
        "beta_gamma": [
            {
                "q": q,
                "beta": str(beta_coefficient(q)),
                "gamma": str(gamma_coefficient(q)),
            }
            for q in range(1, 8)
        ],
        "faber_errors": faber_rows,
        "haar_transform_checks": haar_rows,
        "triangular_transform_checks": triangular_transform_rows,
        "triangular_log_concavity": log_concavity_rows,
        "shannon_checks": shannon_rows,
        "chebyshev_checks": chebyshev_rows,
        "bernstein_errors": bernstein_rows,
        "hypergeometric_transform_check": {
            "degree": hyper_degree,
            "t": mp_text(hyper_t, 8),
            "kummer": mp_text(hyper_value, 24),
            "direct_quadrature": mp_text(hyper_direct, 24),
            "absolute_error": mp_text(abs(hyper_value - hyper_direct), 8),
        },
        "triangular_N16": {
            "degree": len(final_triangular_coefficients) - 1,
            "total_mass_numerator": str(sum(final_triangular_coefficients)),
        },
    }

    with (ROOT / "numerical_results.json").open("w", encoding="utf-8") as stream:
        json.dump(results, stream, indent=2)
        stream.write("\n")

    with (ROOT / "numerical_results.txt").open("w", encoding="utf-8") as stream:
        stream.write("Fabius--Rvachev multiresolution experiments\n")
        stream.write("=" * 49 + "\n\n")
        stream.write(f"Exact dyadic level: {max_exact_level}\n")
        stream.write(f"mpmath precision: {precision} decimal digits\n\n")
        stream.write("Accelerated energy estimate A_2:\n")
        stream.write(f"  {mp_text(energy_estimate, 70)}\n\n")
        stream.write("First beta/gamma coefficients:\n")
        for q in range(1, 8):
            stream.write(
                f"  q={q}: beta={beta_coefficient(q)}, gamma={gamma_coefficient(q)}\n"
            )
        stream.write("\nHaar transform residuals:\n")
        for row in haar_rows:
            stream.write(f"  t={row['point']}: {row['absolute_error']}\n")
        stream.write("\nOdd-sample Shannon residuals (40 positive pairs):\n")
        for row in shannon_rows:
            stream.write(f"  z={row['point']}: {row['absolute_error']}\n")
        stream.write("\nTriangular log-concavity exact checks:\n")
        for row in log_concavity_rows:
            stream.write(
                f"  N={row['N']:2d}, degree={row['degree']:5d}, "
                f"symmetric={row['symmetric']}, log_concave={row['log_concave']}\n"
            )
        stream.write("\nChebyshev DCT/Bessel checks:\n")
        for row in chebyshev_rows:
            stream.write(
                f"  n={row['order']:2d}: DCT={row['dct']:.15g}, "
                f"Bessel={row['bessel']:.15g}, error={row['absolute_error']:.3e}\n"
            )
        stream.write("\nBernstein errors:\n")
        for row in bernstein_rows:
            stream.write(
                f"  n={row['degree']:3d}: error={row['max_error']:.12g}, "
                f"bound={row['bound']:.12g}\n"
            )
        stream.write("\nKummer transform check:\n")
        stream.write(
            f"  degree={hyper_degree}, residual="
            f"{mp_text(abs(hyper_value - hyper_direct), 10)}\n"
        )

    # A compact TeX fragment is included by the report.  Keep it free of
    # packages and document-level commands.
    with (ROOT / "generated_tables.tex").open("w", encoding="utf-8") as stream:
        stream.write("% Generated by fabius_multiresolution_experiments.py\n")
        stream.write("\\begin{table}[htbp]\n\\centering\n")
        stream.write("\\caption{Exact rational energy partial sums and accelerated values.}\n")
        stream.write("\\label{tab:energy-numerics}\n")
        stream.write("\\begin{tabular}{@{}rrrr@{}}\n\\toprule\n")
        stream.write("$J$ & $R_J$ (decimal) & accelerated & raw error \\\\\n\\midrule\n")
        selected_js = sorted(set([2, 3, 4, 5, 6, 8, 10, 12, 14, max_exact_level]))
        for j in selected_js:
            if j > max_exact_level:
                continue
            raw = mp.mpf(partials[j - 1].numerator) / partials[j - 1].denominator
            accelerated = accelerated_energy(partials[j - 1], j, min(5, max(1, j // 2)))
            raw_error = abs(energy_estimate - raw)
            stream.write(
                f"{j} & {mp.nstr(raw, 16)} & {mp.nstr(accelerated, 16)} & "
                f"{mp.nstr(raw_error, 5)} \\\\\n"
            )
        stream.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")

        stream.write("\\begin{table}[htbp]\n\\centering\n")
        stream.write("\\caption{Chebyshev coefficients from cosine quadrature and the Bessel--sinc integral.}\n")
        stream.write("\\label{tab:chebyshev-check}\n")
        stream.write("\\begin{tabular}{@{}rrrr@{}}\n\\toprule\n")
        stream.write("$n$ & cosine-grid value & Bessel-product value & absolute residual \\\\\n\\midrule\n")
        for row in chebyshev_rows:
            stream.write(
                f"{row['order']} & {row['dct']:.12g} & {row['bessel']:.12g} & "
                f"{row['absolute_error']:.2e} \\\\\n"
            )
        stream.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n\n")

        stream.write("\\begin{table}[htbp]\n\\centering\n")
        stream.write("\\caption{Exact tests of the triangular coefficient conjecture.}\n")
        stream.write("\\label{tab:triangular-check}\n")
        stream.write("\\begin{tabular}{@{}rrrr@{}}\n\\toprule\n")
        stream.write("$N$ & degree & palindromic & log-concave \\\\\n\\midrule\n")
        for row in log_concavity_rows:
            if row["N"] in {4, 6, 8, 10, 12, 14, 16}:
                stream.write(
                    f"{row['N']} & {row['degree']} & "
                    f"{'yes' if row['symmetric'] else 'no'} & "
                    f"{'yes' if row['log_concave'] else 'no'} \\\\\n"
                )
        stream.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n")

    return results


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-exact-level",
        type=int,
        default=16,
        help="finest exact dyadic denominator exponent (default: 16)",
    )
    parser.add_argument(
        "--precision",
        type=int,
        default=90,
        help="mpmath decimal precision (default: 90)",
    )
    return parser.parse_args()


def main() -> None:
    arguments = parse_arguments()
    if not (8 <= arguments.max_exact_level <= 19):
        raise SystemExit("--max-exact-level must lie between 8 and 19")
    if arguments.precision < 50:
        raise SystemExit("--precision must be at least 50")
    results = run(arguments.max_exact_level, arguments.precision)
    print("Generated numerical_results.{txt,json}, generated_tables.tex, and figures/.")
    print("Accelerated A_2 =", results["energy_estimate"])


if __name__ == "__main__":
    main()
