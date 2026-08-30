#!/usr/bin/env python3
"""Numerical experiments for the Fabius/Rvachev integral-frontier report.

The script is self-contained and uses two independent descriptions of the
Fabius law:

1. Exact rational moments from the distributional fixed point
       X = (U + X') / 2,
   where U is uniform on [0,1] and X' is an independent copy of X.

2. The finite Thue--Morse spline density for
       Y_n = sum_{j=1}^n V_j / 2^j,
   where V_j is uniform on [-1,1].  Its CDF P_n gives the finite-rank
   approximation F_n(x) = P_n(2x-1).

The experiments check:
  * the primitive identity integral_0^x F(t)dt = F(x/2);
  * closed polynomial-weight antiderivatives;
  * the universal beta substitution;
  * the quantile/Laplace product identity;
  * the Newton--Mellin interpolation from rational moments;
  * the product integral int F(1-F), equivalently a Gini mean difference.

Outputs:
  numerical_results.txt  human-readable details
  numerical_results.tex  compact LaTeX tables used by the report

Only NumPy and SciPy are required.  Long-double arithmetic and symmetry are
used for the alternating spline sums; ranks above about 10 should instead use
arbitrary precision because of severe cancellation.
"""

from __future__ import annotations

import cmath
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np
from scipy.special import beta as beta_function

OUTPUT_DIR = Path(__file__).resolve().parent


def thue_morse_sign(k: int) -> int:
    """Return (-1)^{s_2(k)}, where s_2 is the binary digit sum."""
    return 1 if k.bit_count() % 2 == 0 else -1


@dataclass
class FiniteFabiusSpline:
    """Finite Thue--Morse spline approximation of the Fabius distribution."""

    rank: int

    def __post_init__(self) -> None:
        if not (2 <= self.rank <= 12):
            raise ValueError("rank should lie between 2 and 12")
        n = self.rank
        indices = np.arange(2**n, dtype=np.int64)
        self.signs = np.array(
            [thue_morse_sign(int(k)) for k in indices], dtype=np.longdouble
        )
        self.knots = indices.astype(np.longdouble) / (
            np.longdouble(2) ** (n - 1)
        )
        self.support_radius = np.longdouble(1) - np.longdouble(2) ** (-n)
        self.cdf_coefficient = (
            np.longdouble(2) ** (n * (n - 1) // 2)
        ) / np.longdouble(math.factorial(n))
        self.density_coefficient = (
            np.longdouble(2) ** (n * (n - 1) // 2)
        ) / np.longdouble(math.factorial(n - 1))
        self.primitive_coefficient = (
            np.longdouble(2) ** (n * (n - 1) // 2)
        ) / np.longdouble(math.factorial(n + 1))

    def _centered_cdf_raw(self, y: float | np.longdouble) -> np.longdouble:
        z = np.maximum(
            np.longdouble(y) + self.support_radius - self.knots,
            np.longdouble(0),
        )
        return self.cdf_coefficient * np.sum(
            self.signs * z**self.rank, dtype=np.longdouble
        )

    def _centered_density_raw(self, y: float | np.longdouble) -> np.longdouble:
        z = np.maximum(
            np.longdouble(y) + self.support_radius - self.knots,
            np.longdouble(0),
        )
        return self.density_coefficient * np.sum(
            self.signs * z ** (self.rank - 1), dtype=np.longdouble
        )

    def _centered_cdf_primitive_raw(
        self, y: float | np.longdouble
    ) -> np.longdouble:
        """Integral of the centered CDF from -infinity to y."""
        z = np.maximum(
            np.longdouble(y) + self.support_radius - self.knots,
            np.longdouble(0),
        )
        return self.primitive_coefficient * np.sum(
            self.signs * z ** (self.rank + 1), dtype=np.longdouble
        )

    def cdf(self, x: float) -> float:
        """Finite Fabius CDF F_n(x), stabilized by reflection symmetry."""
        if x <= 0.0:
            return 0.0
        if x >= 1.0:
            return 1.0
        if x > 0.5:
            return 1.0 - self.cdf(1.0 - x)
        value = self._centered_cdf_raw(2.0 * x - 1.0)
        return float(max(np.longdouble(0), min(np.longdouble(0.5), value)))

    def density(self, x: float) -> float:
        """Density F_n'(x)=2 p_n(2x-1), stabilized by symmetry."""
        if x <= 0.0 or x >= 1.0:
            return 0.0
        if x > 0.5:
            return self.density(1.0 - x)
        return float(2.0 * self._centered_density_raw(2.0 * x - 1.0))

    def integral_cdf(self, x: float) -> float:
        """Compute integral_0^x F_n(t)dt from the explicit spline primitive."""
        if x <= 0.0:
            return 0.0
        if x > 1.0:
            return self.integral_cdf(1.0) + x - 1.0
        # t -> y=2t-1 gives dt=dy/2.  The centered CDF is zero below -1.
        return float(0.5 * self._centered_cdf_primitive_raw(2.0 * x - 1.0))

    def quantile(self, y: float, iterations: int = 52) -> float:
        """Invert F_n by symmetry and bisection."""
        if y <= 0.0:
            return 0.0
        if y >= 1.0:
            return 1.0
        if y > 0.5:
            return 1.0 - self.quantile(1.0 - y, iterations)
        lo, hi = 0.0, 0.5
        for _ in range(iterations):
            mid = 0.5 * (lo + hi)
            if self.cdf(mid) < y:
                lo = mid
            else:
                hi = mid
        return 0.5 * (lo + hi)

    def laplace_product(self, s: float) -> float:
        """Exact transform of the finite centered-tail approximation X_n."""
        result = math.exp(-s / 2.0)
        for k in range(1, self.rank + 1):
            z = s / (2.0 ** (k + 1))
            result *= math.sinh(z) / z if z != 0.0 else 1.0
        return result


def exact_moments(max_order: int) -> list[Fraction]:
    """Return d_n=E[X^n] exactly for 0<=n<=max_order.

    From X=(U+X')/2,
      (2^n-1)d_n = sum_{k<n} binom(n,k)d_k/(n-k+1).
    """
    if max_order < 0:
        raise ValueError("max_order must be nonnegative")
    moments = [Fraction(1, 1)]
    for n in range(1, max_order + 1):
        numerator = sum(
            Fraction(math.comb(n, k), n - k + 1) * moments[k]
            for k in range(n)
        )
        moments.append(numerator / Fraction(2**n - 1, 1))
    return moments


def gauss_integral(function, a: float, b: float, nodes: int = 320) -> complex:
    """Gauss--Legendre quadrature on [a,b]."""
    x, w = np.polynomial.legendre.leggauss(nodes)
    points = 0.5 * (b - a) * (x + 1.0) + a
    values = np.array([function(float(t)) for t in points], dtype=np.complex128)
    return 0.5 * (b - a) * np.dot(w, values)


def weighted_closed_form(spline: FiniteFabiusSpline, x: float, p: int) -> float:
    """Finite dyadic formula proposed for integral_0^x t^p F(t)dt."""
    value = 0.0
    for j in range(p + 1):
        coefficient = (
            (-1) ** j
            * math.factorial(p)
            / math.factorial(p - j)
            * 2.0 ** (j * (j + 1) // 2)
        )
        value += coefficient * x ** (p - j) * spline.cdf(x / 2.0 ** (j + 1))
    return value


def newton_mellin(z: complex, moments: Sequence[Fraction], terms: int) -> complex:
    """Evaluate D(z) from the Newton--Mellin series using `terms` terms."""
    if terms < 1 or terms >= len(moments):
        raise ValueError("need 1 <= terms < len(moments)")
    series = 0.0j
    falling = 1.0 + 0.0j
    for j in range(terms):
        if j > 0:
            falling *= z - j
        series += (
            (-1) ** j
            * falling
            * float(moments[j + 1])
            / math.factorial(j + 1)
        )
    return 1.0 - z * series


def beta_direct(
    spline: FiniteFabiusSpline, a: float, b: float, order: int = 8
) -> float:
    """Integrate F^a(1-F)^b F' interval by interval across spline knots."""
    local_x, local_w = np.polynomial.legendre.leggauss(order)
    n = spline.rank
    endpoints = np.linspace(2.0 ** (-n - 1), 1.0 - 2.0 ** (-n - 1), 2**n + 1)
    total = 0.0
    for lo, hi in zip(endpoints[:-1], endpoints[1:]):
        points = 0.5 * (lo + hi) + 0.5 * (hi - lo) * local_x
        values = []
        for x in points:
            f_value = spline.cdf(float(x))
            density = spline.density(float(x))
            values.append(f_value**a * (1.0 - f_value) ** b * density)
        total += 0.5 * (hi - lo) * float(np.dot(local_w, values))
    return total


def gini_product(spline: FiniteFabiusSpline, nodes: int = 500) -> float:
    """Compute int_0^1 F(x)(1-F(x))dx."""
    return float(
        gauss_integral(
            lambda x: spline.cdf(x) * (1.0 - spline.cdf(x)), 0.0, 1.0, nodes
        ).real
    )


def run() -> tuple[str, str]:
    text_lines: list[str] = []

    # 1. Primitive identity and product constant across ranks.
    primitive_rows: list[tuple[int, float, float]] = []
    test_x = [0.2, 0.37, 0.8, 1.0]
    for rank in (6, 8, 10):
        spline = FiniteFabiusSpline(rank)
        max_error = max(
            abs(spline.integral_cdf(x) - spline.cdf(x / 2.0)) for x in test_x
        )
        product = gini_product(spline)
        primitive_rows.append((rank, max_error, product))

    text_lines.append("Primitive identity and product integral")
    for rank, error, product in primitive_rows:
        text_lines.append(
            f"  rank={rank:2d}: max primitive residual={error:.12e}; "
            f"int F(1-F)={product:.12f}"
        )

    # 2. Polynomial weighted antiderivatives.
    spline10 = FiniteFabiusSpline(10)
    weighted_rows: list[tuple[int, complex, float, float]] = []
    x0 = 0.83
    for p in (0, 1, 2, 3, 5):
        direct = gauss_integral(
            lambda t, p=p: t**p * spline10.cdf(t), 0.0, x0, 360
        ).real
        closed = weighted_closed_form(spline10, x0, p)
        weighted_rows.append((p, direct, closed, direct - closed))

    text_lines.append("\nPolynomial-weight antiderivatives at x=0.83, rank 10")
    for p, direct, closed, difference in weighted_rows:
        text_lines.append(
            f"  p={p}: direct={direct:.15f}; closed={closed:.15f}; "
            f"difference={difference:.12e}"
        )

    # 3. Universal beta substitution.
    beta_rows: list[tuple[float, float, float, float, float]] = []
    for a, b in ((0.3, 0.7), (2.0, 1.0), (0.1, 0.1)):
        direct = beta_direct(spline10, a, b)
        exact = float(beta_function(a + 1.0, b + 1.0))
        beta_rows.append((a, b, direct, exact, direct - exact))

    text_lines.append("\nUniversal beta substitution, rank 10")
    for a, b, direct, exact, difference in beta_rows:
        text_lines.append(
            f"  (a,b)=({a},{b}): direct={direct:.15f}; beta={exact:.15f}; "
            f"difference={difference:.12e}"
        )

    # 4. Quantile/Laplace identity.
    q_nodes, q_weights = np.polynomial.legendre.leggauss(400)
    ys = 0.5 * (q_nodes + 1.0)
    weights = 0.5 * q_weights
    quantiles = np.array([spline10.quantile(float(y)) for y in ys])
    laplace_rows: list[tuple[float, float, float, float]] = []
    for s in (0.7, 2.5, 5.0):
        direct = float(np.dot(weights, np.exp(-s * quantiles)))
        product = spline10.laplace_product(s)
        laplace_rows.append((s, direct, product, direct - product))

    text_lines.append("\nQuantile/Laplace identity, rank 10, 400 nodes")
    for s, direct, product, difference in laplace_rows:
        text_lines.append(
            f"  s={s}: quantile={direct:.15f}; product={product:.15f}; "
            f"difference={difference:.12e}"
        )

    # 5. Newton--Mellin interpolation.
    moments = exact_moments(220)
    z = 0.5 + 0.7j
    # Independent finite-rank quantile reference.
    reference = complex(np.dot(weights, np.exp(z * np.log(quantiles))))
    newton_rows: list[tuple[int, complex, float]] = []
    for terms in (5, 10, 20, 40, 60, 100):
        value = newton_mellin(z, moments, terms)
        newton_rows.append((terms, value, abs(value - reference)))

    text_lines.append("\nNewton--Mellin interpolation at z=0.5+0.7i")
    text_lines.append(f"  finite-rank quantile reference={reference.real:.15f}{reference.imag:+.15f}i")
    for terms, value, error in newton_rows:
        text_lines.append(
            f"  terms={terms:3d}: value={value.real:.15f}{value.imag:+.15f}i; "
            f"error={error:.12e}"
        )

    text_lines.append("\nFirst exact moments")
    for n in range(9):
        text_lines.append(f"  d_{n} = {moments[n]}")

    log_constant = sum(float(moments[n]) / n for n in range(1, 201))
    text_lines.append(
        f"\nPartial sum sum_(n<=200) d_n/n = {log_constant:.12f}"
    )

    # Compact LaTeX tables.
    tex_lines: list[str] = []
    tex_lines.extend(
        [
            r"\begin{tabular}{rcc}",
            r"\toprule",
            r"Spline rank & max. primitive residual & $\int_0^1F_n(1-F_n)$\\",
            r"\midrule",
        ]
    )
    for rank, error, product in primitive_rows:
        tex_lines.append(f"{rank} & ${error:.3e}$ & ${product:.12f}$\\\\")
    tex_lines.extend([r"\bottomrule", r"\end{tabular}", r"\par\medskip"])

    tex_lines.extend(
        [
            r"\begin{tabular}{rccc}",
            r"\toprule",
            r"$p$ & quadrature & dyadic formula & difference\\",
            r"\midrule",
        ]
    )
    for p, direct, closed, difference in weighted_rows:
        tex_lines.append(
            f"{p} & ${direct:.12f}$ & ${closed:.12f}$ & ${difference:.3e}$\\\\"
        )
    tex_lines.extend([r"\bottomrule", r"\end{tabular}", r"\par\medskip"])

    tex_lines.extend(
        [
            r"\begin{tabular}{rcc}",
            r"\toprule",
            r"Newton terms & approximation error & approximation\\",
            r"\midrule",
        ]
    )
    for terms, value, error in newton_rows:
        tex_lines.append(
            f"{terms} & ${error:.3e}$ & "
            f"${value.real:.9f}{value.imag:+.9f}\\,i$\\\\"
        )
    tex_lines.extend([r"\bottomrule", r"\end{tabular}"])

    return "\n".join(text_lines) + "\n", "\n".join(tex_lines) + "\n"


def main() -> None:
    text, tex = run()
    (OUTPUT_DIR / "numerical_results.txt").write_text(text, encoding="utf-8")
    (OUTPUT_DIR / "numerical_results.tex").write_text(tex, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
