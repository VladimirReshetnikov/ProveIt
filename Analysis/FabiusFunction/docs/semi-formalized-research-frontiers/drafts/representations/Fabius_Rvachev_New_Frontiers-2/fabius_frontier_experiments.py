#!/usr/bin/env python3
"""Numerical and exact-arithmetic experiments for the report
"Fabius--Rvachev Orthogonal and Log-Concavity Frontiers".

The script uses only the exact even-moment recurrence for Rvachev's up-law
and the monic three-term recurrence of its native orthogonal polynomials.
No sampled values of the Fabius or up functions are used.

Notation
--------
Let mu(dx) = up(x) dx on [-1,1], and let m_k = integral x^k dmu(x).
The odd moments vanish, while c_n = m_{2n} obeys

  (2n+1)(2^(2n)-1)c_n
      = sum_{j=0}^{n-1} binom(2n+1,2j)c_j,  c_0 = 1.

The monic orthogonal polynomials pi_n satisfy

  pi_0 = 1, pi_1 = x,
  pi_{n+1}(x) = x*pi_n(x) - beta_n*pi_{n-1}(x),

where H_n = integral pi_n(x)^2 dmu(x), beta_n = H_n/H_{n-1}.
For a monic orthogonal polynomial one may evaluate the norm without a
quadratic convolution:

  H_n = integral x^n*pi_n(x) dmu(x).

This identity makes the high-precision computation O(N^2) coefficient
operations, although severe cancellation requires thousands of decimal
places when N is a few hundred.

Outputs
-------
* data/jacobi_coefficients.csv        high-precision beta_n and diagnostics
* data/pi_product_approximants.csv    rational-product and Christoffel pi limits
* data/exact_low_degree.csv           exact fractions for the initial data
* figures/jacobi_coefficients.pdf     beta_n -> 1/4
* figures/scaled_jacobi_deficit.pdf   diagnostic for log^2(n)/n^2 correction
* figures/pi_product_error.pdf        diagnostic for the new rational pi product
* figures/pi_approximants.pdf         product versus Christoffel approximants
* figures/zero_quantiles.pdf           zeros compared with the arcsine law

Reproducibility
---------------
The archive ships precomputed tables made with --degree 200 --dps 4800.
A smaller run, for example --degree 120 --dps 2500, is useful for a quick
independent check.  The low-degree exact calculation is always performed.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence, TypeVar

import mpmath as mp
import matplotlib.pyplot as plt
import numpy as np

Scalar = TypeVar("Scalar", Fraction, mp.mpf)


@dataclass
class OrthogonalData:
    """Moment, norm, recurrence-coefficient, and polynomial data."""

    even_moments: list
    moments: list
    polynomials: list[list]
    norms: list
    beta: list


def add_polynomials(a: Sequence[Scalar], b: Sequence[Scalar]) -> list[Scalar]:
    """Add coefficient arrays stored in ascending powers of x."""

    n = max(len(a), len(b))
    zero = a[0] * 0 if a else b[0] * 0
    out = [zero for _ in range(n)]
    for i, value in enumerate(a):
        out[i] += value
    for i, value in enumerate(b):
        out[i] += value
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def scale_polynomial(a: Sequence[Scalar], factor: Scalar) -> list[Scalar]:
    return [factor * value for value in a]


def x_times(a: Sequence[Scalar]) -> list[Scalar]:
    """Multiply a coefficient array by x."""

    return [a[0] * 0, *a]


def make_even_moments_exact(max_index: int) -> list[Fraction]:
    """Return c_0,...,c_max_index using exact rational arithmetic."""

    c = [Fraction(1)]
    for n in range(1, max_index + 1):
        numerator = sum(
            Fraction(math.comb(2 * n + 1, 2 * j)) * c[j]
            for j in range(n)
        )
        denominator = (2 * n + 1) * (2 ** (2 * n) - 1)
        c.append(numerator / denominator)
    return c


def make_even_moments_mp(max_index: int) -> list[mp.mpf]:
    """Return c_0,...,c_max_index at the current mpmath precision."""

    c = [mp.mpf(1)]
    for n in range(1, max_index + 1):
        numerator = mp.fsum(
            mp.mpf(math.comb(2 * n + 1, 2 * j)) * c[j]
            for j in range(n)
        )
        denominator = mp.mpf(2 * n + 1) * (mp.mpf(2) ** (2 * n) - 1)
        c.append(numerator / denominator)
    return c


def interleave_moments(even_moments: Sequence[Scalar]) -> list[Scalar]:
    """Create m_0,...,m_{2r} from c_j=m_{2j} and m_{2j+1}=0."""

    zero = even_moments[0] * 0
    moments: list[Scalar] = []
    for value in even_moments:
        moments.extend((value, zero))
    moments.pop()  # no odd moment after the final even moment is needed
    return moments


def orthogonal_data_from_moments(
    even_moments: Sequence[Scalar], degree: int
) -> OrthogonalData:
    """Build monic orthogonal polynomials and beta_1,...,beta_degree.

    The input must contain c_0,...,c_degree so moments through order 2*degree
    are available.  beta[0] is a harmless zero sentinel; beta[n] is beta_n.
    """

    if degree < 1:
        raise ValueError("degree must be at least 1")
    if len(even_moments) <= degree:
        raise ValueError("insufficient moments")

    moments = interleave_moments(even_moments)
    zero = even_moments[0] * 0
    one = even_moments[0] * 0 + 1

    polynomials: list[list[Scalar]] = [[one], [zero, one]]
    norms: list[Scalar] = [one, moments[2]]
    beta: list[Scalar] = [zero, norms[1] / norms[0]]

    # At loop index n we already know pi_{n-1}, pi_n, H_{n-1}, H_n,
    # and beta_n.  We form pi_{n+1}, then use <pi_{n+1},x^{n+1}>=H_{n+1}.
    for n in range(1, degree):
        next_poly = add_polynomials(
            x_times(polynomials[n]),
            scale_polynomial(polynomials[n - 1], -beta[n]),
        )
        polynomials.append(next_poly)

        next_norm = sum(
            coeff * moments[j + n + 1]
            for j, coeff in enumerate(next_poly)
        )
        norms.append(next_norm)
        beta.append(next_norm / norms[n])

    return OrthogonalData(
        even_moments=list(even_moments),
        moments=moments,
        polynomials=polynomials,
        norms=norms,
        beta=beta,
    )


def fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def mp_text(value: mp.mpf, digits: int = 50) -> str:
    return mp.nstr(value, n=digits, strip_zeros=False)


def product_pi_approximants(beta: Sequence[Scalar]) -> list[Scalar]:
    """Return Pi_M = 2 prod_{j=1}^M beta_{2j}/beta_{2j-1}."""

    one = beta[1] * 0 + 1
    current = 2 * one
    out = [current]  # Pi_0=2
    for m in range(1, (len(beta) - 1) // 2 + 1):
        current *= beta[2 * m] / beta[2 * m - 1]
        out.append(current)
    return out


def christoffel_even_pi_approximants(pi_product: Sequence[Scalar]) -> list[Scalar]:
    """Return C_M = 2M*lambda_{2M}(0), M>=1.

    The exact identity

        C_M = M / sum_{m=0}^{M-1} 1/Pi_m

    follows from p_{2m}(0)^2 = 2/Pi_m.
    """

    out: list[Scalar] = []
    reciprocal_sum = pi_product[0] * 0
    for m in range(1, len(pi_product)):
        reciprocal_sum += 1 / pi_product[m - 1]
        out.append(m / reciprocal_sum)
    return out


def assert_low_degree_values(exact: OrthogonalData) -> None:
    """Guard against indexing or normalization mistakes."""

    expected = {
        1: Fraction(1, 9),
        2: Fraction(32, 225),
        3: Fraction(619, 3675),
    }
    for n, value in expected.items():
        if exact.beta[n] != value:
            raise AssertionError(
                f"beta_{n}: got {exact.beta[n]}, expected {value}"
            )

    expected_p = {
        2: [Fraction(-1, 9), Fraction(0), Fraction(1)],
        3: [Fraction(0), Fraction(-19, 75), Fraction(0), Fraction(1)],
        4: [
            Fraction(619, 33075),
            Fraction(0),
            Fraction(-62, 147),
            Fraction(0),
            Fraction(1),
        ],
    }
    for n, coeffs in expected_p.items():
        if exact.polynomials[n] != coeffs:
            raise AssertionError(
                f"pi_{n}: got {exact.polynomials[n]}, expected {coeffs}"
            )


def write_exact_table(path: Path, exact: OrthogonalData) -> None:
    products = product_pi_approximants(exact.beta)
    christoffel = christoffel_even_pi_approximants(products)
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(
            [
                "n",
                "c_n=m_2n",
                "H_n",
                "beta_n",
                "Pi_floor(n/2)_when_even",
                "2M_lambda_2M_when_n=2M",
            ]
        )
        for n in range(min(len(exact.norms), 21)):
            row = [
                n,
                fraction_text(exact.even_moments[n])
                if n < len(exact.even_moments)
                else "",
                fraction_text(exact.norms[n]),
                fraction_text(exact.beta[n]) if n >= 1 else "",
                "",
                "",
            ]
            if n >= 2 and n % 2 == 0:
                m = n // 2
                row[4] = fraction_text(products[m])
                row[5] = fraction_text(christoffel[m - 1])
            writer.writerow(row)


def write_high_precision_tables(
    data_dir: Path, numerical: OrthogonalData
) -> tuple[list[mp.mpf], list[mp.mpf]]:
    beta = numerical.beta
    products = product_pi_approximants(beta)
    christoffel = christoffel_even_pi_approximants(products)

    with (data_dir / "jacobi_coefficients.csv").open(
        "w", newline="", encoding="utf-8"
    ) as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(
            [
                "n",
                "beta_n",
                "one_quarter_minus_beta_n",
                "n2_deficit_over_log2n2",
                "four_beta_n",
            ]
        )
        for n in range(1, len(beta)):
            deficit = mp.mpf(1) / 4 - beta[n]
            scaled = (
                n * n * deficit / mp.log(n, 2) ** 2 if n >= 2 else mp.nan
            )
            writer.writerow(
                [
                    n,
                    mp_text(beta[n], 70),
                    mp_text(deficit, 70),
                    mp_text(scaled, 50) if n >= 2 else "",
                    mp_text(4 * beta[n], 70),
                ]
            )

    with (data_dir / "pi_product_approximants.csv").open(
        "w", newline="", encoding="utf-8"
    ) as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(
            [
                "M",
                "Pi_M_product",
                "pi_minus_Pi_M",
                "M2_error_over_log2M2",
                "2M_lambda_2M_center",
                "pi_minus_christoffel",
                "M_times_christoffel_error",
            ]
        )
        for m in range(1, len(products)):
            product = products[m]
            center = christoffel[m - 1]
            product_scaled = (
                m * m * (mp.pi - product) / mp.log(m, 2) ** 2
                if m >= 2
                else mp.nan
            )
            writer.writerow(
                [
                    m,
                    mp_text(product, 70),
                    mp_text(mp.pi - product, 70),
                    mp_text(product_scaled, 50) if m >= 2 else "",
                    mp_text(center, 70),
                    mp_text(mp.pi - center, 70),
                    mp_text(m * (mp.pi - center), 50),
                ]
            )

    return products, christoffel


def make_figures(
    figures_dir: Path,
    numerical: OrthogonalData,
    products: Sequence[mp.mpf],
    christoffel: Sequence[mp.mpf],
) -> None:
    figures_dir.mkdir(parents=True, exist_ok=True)
    beta = numerical.beta

    # 1. Native Jacobi recurrence coefficients.
    n_values = list(range(1, len(beta)))
    plt.figure(figsize=(7.0, 4.2))
    plt.plot(n_values, [float(beta[n]) for n in n_values], label=r"$\beta_n$")
    plt.axhline(0.25, linestyle="--", label=r"$1/4$")
    plt.xlabel(r"$n$")
    plt.ylabel(r"recurrence coefficient")
    plt.title("Native up-law Jacobi coefficients")
    plt.legend()
    plt.tight_layout()
    plt.savefig(figures_dir / "jacobi_coefficients.pdf")
    plt.close()

    # 2. Candidate logarithmic-square correction.
    n_values = list(range(2, len(beta)))
    scaled = [
        float(n * n * (mp.mpf(1) / 4 - beta[n]) / mp.log(n, 2) ** 2)
        for n in n_values
    ]
    plt.figure(figsize=(7.0, 4.2))
    plt.plot(n_values, scaled)
    plt.axhline(float(2 / mp.pi), linestyle="--", label=r"$2/\pi$")
    plt.xlabel(r"$n$")
    plt.ylabel(r"$n^2(1/4-\beta_n)/(\log_2 n)^2$")
    plt.title("Scaled recurrence-coefficient deficit")
    plt.legend()
    plt.tight_layout()
    plt.savefig(figures_dir / "scaled_jacobi_deficit.pdf")
    plt.close()

    # 3. Product error on the conjectured scale.
    m_values = list(range(2, len(products)))
    scaled_error = [
        float(m * m * (mp.pi - products[m]) / mp.log(m, 2) ** 2)
        for m in m_values
    ]
    plt.figure(figsize=(7.0, 4.2))
    plt.plot(m_values, scaled_error)
    plt.axhline(1.0, linestyle="--", label=r"candidate limit $1$")
    plt.xlabel(r"$M$")
    plt.ylabel(r"$M^2(\pi-\Pi_M)/(\log_2 M)^2$")
    plt.title("Scaled error of the rational Jacobi product for pi")
    plt.legend()
    plt.tight_layout()
    plt.savefig(figures_dir / "pi_product_error.pdf")
    plt.close()

    # 4. Compare the direct product with its Christoffel harmonic mean.
    m_values = list(range(1, len(products)))
    plt.figure(figsize=(7.0, 4.2))
    plt.plot(m_values, [float(products[m]) for m in m_values], label=r"$\Pi_M$")
    plt.plot(
        m_values,
        [float(christoffel[m - 1]) for m in m_values],
        label=r"$2M\lambda_{2M}(0)$",
    )
    plt.axhline(float(mp.pi), linestyle="--", label=r"$\pi$")
    plt.xlabel(r"$M$")
    plt.ylabel("approximant")
    plt.title("Two moment-theoretic approximations to pi")
    plt.legend()
    plt.tight_layout()
    plt.savefig(figures_dir / "pi_approximants.pdf")
    plt.close()

    # 5. Zeros of pi_N are eigenvalues of the N-by-N Jacobi truncation.
    # Comparing ordered zeros with arcsine quantiles avoids histogram binning.
    zero_degree = min(100, len(beta) - 1)
    jacobi = np.zeros((zero_degree, zero_degree), dtype=float)
    for n in range(1, zero_degree):
        a_n = math.sqrt(float(beta[n]))
        jacobi[n - 1, n] = a_n
        jacobi[n, n - 1] = a_n
    zeros = np.linalg.eigvalsh(jacobi)
    probabilities = (np.arange(zero_degree) + 0.5) / zero_degree
    arcsine_quantiles = -np.cos(np.pi * probabilities)
    plt.figure(figsize=(7.0, 4.2))
    plt.plot(probabilities, zeros, label=rf"zeros of $\pi_{{{zero_degree}}}$")
    plt.plot(probabilities, arcsine_quantiles, linestyle="--", label="arcsine quantiles")
    plt.xlabel("normalized zero index")
    plt.ylabel("location in $[-1,1]$")
    plt.title("Native up-law zeros and the equilibrium distribution")
    plt.legend()
    plt.tight_layout()
    plt.savefig(figures_dir / "zero_quantiles.pdf")
    plt.close()


def print_diagnostics(
    numerical: OrthogonalData,
    products: Sequence[mp.mpf],
    christoffel: Sequence[mp.mpf],
) -> None:
    beta = numerical.beta
    increasing = all(beta[n + 1] > beta[n] for n in range(1, len(beta) - 1))
    below_quarter = all(beta[n] < mp.mpf(1) / 4 for n in range(1, len(beta)))
    print(f"computed beta_1,...,beta_{len(beta)-1}")
    print(f"strictly increasing on computed range: {increasing}")
    print(f"strictly below 1/4 on computed range: {below_quarter}")

    sample_n = [10, 20, 40, 60, 80, 100, 150, 200, 250, len(beta) - 1]
    print("\nselected beta_n values")
    for n in sorted(set(n for n in sample_n if 1 <= n < len(beta))):
        deficit = mp.mpf(1) / 4 - beta[n]
        scaled = n * n * deficit / mp.log(n, 2) ** 2
        print(
            f"n={n:4d} beta={mp.nstr(beta[n], 18)} "
            f"scaled_deficit={mp.nstr(scaled, 12)}"
        )

    sample_m = [1, 2, 3, 4, 5, 10, 20, 50, 75, 100, 125, len(products) - 1]
    print("\nselected pi approximants")
    for m in sorted(set(m for m in sample_m if 1 <= m < len(products))):
        scaled = (
            m * m * (mp.pi - products[m]) / mp.log(m, 2) ** 2
            if m >= 2
            else mp.nan
        )
        print(
            f"M={m:4d} Pi_M={mp.nstr(products[m], 18)} "
            f"scaled_error={mp.nstr(scaled, 12) if m >= 2 else '-'} "
            f"Christoffel={mp.nstr(christoffel[m-1], 18)}"
        )

    # The Szego norm product C_up = lim prod_{n<=N} 4 beta_n.
    szego_partial = mp.mpf(1)
    for n in range(1, len(beta)):
        szego_partial *= 4 * beta[n]
    print(
        "\nlast partial Fabius-Szego norm constant "
        f"prod_(n<=N) 4 beta_n = {mp.nstr(szego_partial, 25)}"
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--degree",
        type=int,
        default=160,
        help="largest beta index for the high-precision run (default: 160)",
    )
    parser.add_argument(
        "--dps",
        type=int,
        default=3600,
        help="mpmath decimal precision (default: 3600)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="output root containing data/ and figures/",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.degree < 12:
        raise SystemExit("--degree must be at least 12")
    if args.dps < max(100, 15 * args.degree):
        print(
            "warning: the requested precision is low for the requested degree; "
            "cancellation may corrupt the final coefficients"
        )

    output = args.output.resolve()
    data_dir = output / "data"
    figures_dir = output / "figures"
    data_dir.mkdir(parents=True, exist_ok=True)
    figures_dir.mkdir(parents=True, exist_ok=True)

    # Exact initial segment: this both supplies publication-ready fractions and
    # acts as a normalization test for the high-precision implementation.
    exact_degree = min(24, args.degree)
    exact_moments = make_even_moments_exact(exact_degree)
    exact = orthogonal_data_from_moments(exact_moments, exact_degree)
    assert_low_degree_values(exact)
    write_exact_table(data_dir / "exact_low_degree.csv", exact)

    # High-precision run.
    mp.mp.dps = args.dps
    numerical_moments = make_even_moments_mp(args.degree)
    numerical = orthogonal_data_from_moments(numerical_moments, args.degree)

    # A second guard compares the exact and numerical initial segment.
    for n in range(1, exact_degree + 1):
        exact_as_mp = mp.mpf(exact.beta[n].numerator) / exact.beta[n].denominator
        error = abs(numerical.beta[n] - exact_as_mp)
        if error > mp.mpf(10) ** (-(args.dps // 2)):
            raise AssertionError(f"high-precision beta_{n} failed exact check")

    if any(value <= 0 for value in numerical.norms):
        raise ArithmeticError("a computed squared norm is nonpositive")

    products, christoffel = write_high_precision_tables(data_dir, numerical)
    make_figures(figures_dir, numerical, products, christoffel)
    print_diagnostics(numerical, products, christoffel)


if __name__ == "__main__":
    main()
