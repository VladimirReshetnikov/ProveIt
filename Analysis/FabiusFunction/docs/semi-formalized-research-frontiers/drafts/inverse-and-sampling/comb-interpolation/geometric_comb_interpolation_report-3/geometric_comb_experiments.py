#!/usr/bin/env python3
"""Numerical and exact-arithmetic experiments for geometric-comb interpolation.

This script accompanies the report

    Interpolation on a Geometric Comb:
    Lagrange Filters, Jackson--Newton Series, q-Analogues,
    and the Fabius--Rvachev Bridge.

The program deliberately separates two kinds of computation:

* exact rational arithmetic, used for the half-base q=1/2 identities and for
  the Fabius moment/value recurrences; and
* high-precision floating-point arithmetic, used only for infinite sinc
  products and plots.

Running the script creates CSV tables and PDF/PNG figures in the requested
output directory.  No numerical experiment is used as a substitute for a
proof in the report; the assertions below are independent checks of the
closed formulas proved there.

Usage
-----
    python geometric_comb_experiments.py --output-dir output

Dependencies
------------
    Python 3.9+
    mpmath
    matplotlib

Only the Python standard library is needed for all exact-arithmetic checks.
"""

from __future__ import annotations

import argparse
import csv
import math
from fractions import Fraction
from pathlib import Path
from typing import Iterable, List, Sequence

import matplotlib.pyplot as plt
import mpmath as mp


# ---------------------------------------------------------------------------
# Elementary q-functions (exact for Fraction arguments)
# ---------------------------------------------------------------------------


def q_pochhammer(q: Fraction, n: int) -> Fraction:
    """Return (q;q)_n = product_{j=1}^n (1-q^j) exactly."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    value = Fraction(1)
    for j in range(1, n + 1):
        value *= 1 - q**j
    return value


def gaussian_binomial(n: int, k: int, q: Fraction) -> Fraction:
    """Return the Gaussian coefficient [n choose k]_q exactly."""
    if k < 0 or k > n:
        return Fraction(0)
    return q_pochhammer(q, n) / (q_pochhammer(q, k) * q_pochhammer(q, n - k))


def geometric_lagrange_zero_weights(n: int, q: Fraction) -> List[Fraction]:
    r"""Lagrange weights for evaluation at zero on 1,q,...,q^n.

    lambda_{n,k} = (-1)^(n-k) q^((n-k)(n-k+1)/2)
                   / ((q;q)_k (q;q)_{n-k}).
    """
    return [
        (-1) ** (n - k)
        * q ** ((n - k) * (n - k + 1) // 2)
        / (q_pochhammer(q, k) * q_pochhammer(q, n - k))
        for k in range(n + 1)
    ]


def barycentric_weights(n: int, a: Fraction, q: Fraction) -> List[Fraction]:
    r"""Barycentric weights for nodes a q^j, 0 <= j <= n.

    beta_j = 1 / product_{r != j}(a q^j-a q^r).
    The common scale of barycentric weights is immaterial, but this routine
    returns the literal reciprocal derivative of the nodal polynomial.
    """
    result: List[Fraction] = []
    for j in range(n + 1):
        exponent = -j * n + j * (j + 1) // 2
        result.append(
            (-1) ** j
            * q**exponent
            / (a**n * q_pochhammer(q, j) * q_pochhammer(q, n - j))
        )
    return result


def mellin_symbol_direct(n: int, q: mp.mpf, s: mp.mpf) -> mp.mpf:
    """Compute sum_k lambda_{n,k} q^(k s) in high precision."""
    q_fraction = Fraction(str(q)) if q in (mp.mpf("0.5"), mp.mpf("0.25")) else None
    if q_fraction is not None:
        weights = [mp.mpf(w.numerator) / w.denominator for w in geometric_lagrange_zero_weights(n, q_fraction)]
    else:
        weights = geometric_lagrange_zero_weights_mp(n, q)
    return mp.fsum(weights[k] * q ** (k * s) for k in range(n + 1))


def mellin_symbol_product(n: int, q: mp.mpf, s: mp.mpf) -> mp.mpf:
    r"""Closed Mellin multiplier q^(ns) (q^(1-s);q)_n/(q;q)_n."""
    numerator = mp.mpf(1)
    denominator = mp.mpf(1)
    for j in range(n):
        numerator *= 1 - q ** (1 - s + j)
    for j in range(1, n + 1):
        denominator *= 1 - q**j
    return q ** (n * s) * numerator / denominator


# ---------------------------------------------------------------------------
# Jackson derivatives and geometric divided differences
# ---------------------------------------------------------------------------


def q_integer(m: int, q: Fraction) -> Fraction:
    """Return [m]_q=(1-q^m)/(1-q), with [0]_q=0."""
    if m < 0:
        raise ValueError("m must be nonnegative")
    return (1 - q**m) / (1 - q) if m else Fraction(0)


def q_derivative_polynomial(coefficients: Sequence[Fraction], q: Fraction) -> List[Fraction]:
    """Apply the Jackson derivative to a polynomial in ascending powers."""
    if len(coefficients) <= 1:
        return [Fraction(0)]
    return [coefficients[m] * q_integer(m, q) for m in range(1, len(coefficients))]


def evaluate_polynomial(coefficients: Sequence[Fraction], x: Fraction) -> Fraction:
    """Evaluate an ascending-power polynomial by Horner's rule."""
    value = Fraction(0)
    for coefficient in reversed(coefficients):
        value = value * x + coefficient
    return value


def jackson_newton_coefficient(
    coefficients: Sequence[Fraction], k: int, a: Fraction, q: Fraction
) -> Fraction:
    r"""Return D_q^k f(a)/[k]_q! exactly for a polynomial f."""
    derived = list(coefficients)
    for _ in range(k):
        derived = q_derivative_polynomial(derived, q)
    q_factorial = Fraction(1)
    for j in range(1, k + 1):
        q_factorial *= q_integer(j, q)
    return evaluate_polynomial(derived, a) / q_factorial


def explicit_geometric_divided_difference(
    values: Sequence[Fraction], k: int, a: Fraction, q: Fraction
) -> Fraction:
    """Closed divided-difference formula at a,aq,...,aq^k."""
    total = Fraction(0)
    for j in range(k + 1):
        exponent = -j * k + j * (j + 1) // 2
        total += (
            (-1) ** j
            * q**exponent
            * values[j]
            / (a**k * q_pochhammer(q, j) * q_pochhammer(q, k - j))
        )
    return total


# ---------------------------------------------------------------------------
# Exact Fabius data at the dyadic comb
# ---------------------------------------------------------------------------


def fabius_moments(max_order: int) -> List[Fraction]:
    r"""Moments mu_n = E[X^n] for X=sum_{j>=1} 2^{-j} U_j.

    The recurrence follows from X = (U+X')/2:

        (2^n-1) mu_n = sum_{k=0}^{n-1} binom(n,k) mu_k/(n-k+1).
    """
    moments: List[Fraction] = [Fraction(1)]
    for n in range(1, max_order + 1):
        rhs = Fraction(0)
        for k in range(n):
            rhs += Fraction(math.comb(n, k), n - k + 1) * moments[k]
        moments.append(rhs / (2**n - 1))
    return moments


def fabius_dyadic_values(moments: Sequence[Fraction]) -> List[Fraction]:
    r"""Return F(2^{-n}) = 2^{-n(n-1)/2} mu_n/n! exactly."""
    return [
        Fraction(1, 2 ** (n * (n - 1) // 2)) * moments[n] / math.factorial(n)
        for n in range(len(moments))
    ]


def mersenne_products(max_order: int) -> List[int]:
    r"""M_n = product_{j=1}^n (2^j-1), with M_0=1."""
    result = [1]
    value = 1
    for n in range(1, max_order + 1):
        value *= 2**n - 1
        result.append(value)
    return result


def fabius_newton_coefficients(
    moments: Sequence[Fraction], mersenne: Sequence[int]
) -> List[Fraction]:
    r"""Newton coefficients for interpolation at 1,1/2,1/4,... .

    If A_n is the coefficient of product_{r=0}^{n-1}(x-2^{-r}), then

        A_n = 2^{n(n+1)/2} sum_{j=0}^n
              (-1)^j mu_j/(j! M_j M_{n-j}).

    This Mersenne-convolution formula is algebraically equivalent to the
    Gaussian transform

        A_n = 1/(1/2;1/2)_n sum_j (-1)^j [n choose j]_2 mu_j/j!.
    """
    max_order = len(moments) - 1
    result: List[Fraction] = []
    for n in range(max_order + 1):
        convolution = Fraction(0)
        for j in range(n + 1):
            convolution += (
                (-1) ** j
                * moments[j]
                / (math.factorial(j) * mersenne[j] * mersenne[n - j])
            )
        result.append(2 ** (n * (n + 1) // 2) * convolution)
    return result


def fabius_endpoint_extrapolants(
    moments: Sequence[Fraction], mersenne: Sequence[int]
) -> List[Fraction]:
    r"""Return P_n(0), where P_n interpolates F at 1,1/2,...,2^{-n}.

    The exact Mersenne-moment convolution is

        P_n(0) = sum_{k=0}^n (-1)^(n-k) 2^k mu_k
                 /(k! M_k M_{n-k}).
    """
    max_order = len(moments) - 1
    result: List[Fraction] = []
    for n in range(max_order + 1):
        value = Fraction(0)
        for k in range(n + 1):
            value += (
                (-1) ** (n - k)
                * 2**k
                * moments[k]
                / (math.factorial(k) * mersenne[k] * mersenne[n - k])
            )
        result.append(value)
    return result


def evaluate_newton_partial(
    coefficients: Sequence[Fraction], x: Fraction, q: Fraction = Fraction(1, 2)
) -> Fraction:
    """Evaluate a geometric Newton partial sum with a=1 exactly."""
    value = Fraction(0)
    basis = Fraction(1)
    for n, coefficient in enumerate(coefficients):
        if n > 0:
            basis *= x - q ** (n - 1)
        value += coefficient * basis
    return value


# ---------------------------------------------------------------------------
# High-precision Rvachev Fourier product and reciprocal filter
# ---------------------------------------------------------------------------


def sinc_pi(x: mp.mpf) -> mp.mpf:
    """Normalized sinc sin(pi x)/(pi x), evaluated safely at zero."""
    return mp.mpf(1) if x == 0 else mp.sin(mp.pi * x) / (mp.pi * x)


def geometric_lagrange_zero_weights_mp(n: int, q: mp.mpf) -> List[mp.mpf]:
    """High-precision floating-point Lagrange weights."""
    poch = [mp.mpf(1)]
    for k in range(1, n + 1):
        poch.append(poch[-1] * (1 - q**k))
    return [
        (-1) ** (n - k)
        * q ** ((n - k) * (n - k + 1) // 2)
        / (poch[k] * poch[n - k])
        for k in range(n + 1)
    ]


def up_hat(q: mp.mpf, xi: mp.mpf, factors: int = 300) -> mp.mpf:
    r"""Fourier transform of the centered geometric-uniform density.

    u_q has Fourier transform

        product_{j>=0} sinc_pi(2(1-q) q^j xi).

    For q=1/2 this is Rvachev's classical infinite sinc product.
    """
    product = mp.mpf(1)
    for j in range(factors):
        product *= sinc_pi(2 * (1 - q) * q**j * xi)
    return product


def reciprocal_up_filter(q: mp.mpf, xi: mp.mpf, n: int) -> mp.mpf:
    r"""Finite reciprocal-product approximant from the Lagrange filter.

    Let S_k(xi)=product_{j=0}^{k-1}sinc_pi(2(1-q)q^j xi).  Then

        R_n(xi)=sum_{k=0}^n lambda_{n,k}/S_k(xi)

    converges to 1/hat(u_q)(xi) away from the zero set.
    """
    weights = geometric_lagrange_zero_weights_mp(n, q)
    prefix = mp.mpf(1)
    terms = []
    for k in range(n + 1):
        if k > 0:
            j = k - 1
            prefix *= sinc_pi(2 * (1 - q) * q**j * xi)
        terms.append(weights[k] / prefix)
    return mp.fsum(terms)


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------


def mp_log10_fraction(value: Fraction) -> float:
    """Accurate base-10 logarithm of an arbitrarily large rational."""
    if value == 0:
        return float("-inf")
    return float(mp.log10(mp.mpf(abs(value.numerator))) - mp.log10(value.denominator))


def write_csv(path: Path, header: Sequence[str], rows: Iterable[Sequence[object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(header)
        writer.writerows(rows)


def save_figure(fig: plt.Figure, stem: Path) -> None:
    """Save each plot in both vector PDF and preview PNG formats."""
    fig.tight_layout()
    fig.savefig(stem.with_suffix(".pdf"), bbox_inches="tight")
    fig.savefig(stem.with_suffix(".png"), dpi=180, bbox_inches="tight")
    plt.close(fig)


# ---------------------------------------------------------------------------
# Validation and experiment driver
# ---------------------------------------------------------------------------


def run_exact_identity_checks() -> None:
    """Raise AssertionError if any proved finite identity is violated."""
    q = Fraction(2, 3)
    a = Fraction(3, 2)

    # Barycentric formula against direct products.
    n = 6
    closed = barycentric_weights(n, a, q)
    for j in range(n + 1):
        direct_denominator = Fraction(1)
        xj = a * q**j
        for r in range(n + 1):
            if r != j:
                direct_denominator *= xj - a * q**r
        assert closed[j] == 1 / direct_denominator

    # The zero-evaluation row reproduces constants and annihilates x^d,
    # 1 <= d <= n.  Its first residual moment is also checked.
    weights = geometric_lagrange_zero_weights(n, q)
    assert sum(weights) == 1
    for degree in range(1, n + 1):
        assert sum(weights[k] * q ** (k * degree) for k in range(n + 1)) == 0
    degree = n + 3
    expected = (
        (-1) ** n
        * q ** (n * (n + 1) // 2)
        * gaussian_binomial(degree - 1, n, q)
    )
    assert sum(weights[k] * q ** (k * degree) for k in range(n + 1)) == expected

    # Jackson derivative = divided difference on a geometric comb.
    polynomial = [Fraction(7, 5), Fraction(-3, 2), Fraction(11, 7), Fraction(5, 9), Fraction(-2, 3), Fraction(4, 11)]
    values = [evaluate_polynomial(polynomial, a * q**j) for j in range(len(polynomial))]
    for k in range(len(polynomial)):
        assert jackson_newton_coefficient(polynomial, k, a, q) == explicit_geometric_divided_difference(values, k, a, q)

    # The Mellin multiplier formula is checked independently in high precision
    # at a nonintegral exponent.
    mp.mp.dps = 80
    q_mp = mp.mpf(2) / 3
    s_mp = mp.mpf(7) / 4
    direct = mellin_symbol_direct(7, q_mp, s_mp)
    product = mellin_symbol_product(7, q_mp, s_mp)
    assert abs(direct - product) < mp.mpf("1e-65")


def run_experiments(output_dir: Path, max_order: int = 80) -> None:
    if max_order < 0:
        raise ValueError("max_order must be nonnegative")

    output_dir.mkdir(parents=True, exist_ok=True)
    figure_dir = output_dir / "figures"
    data_dir = output_dir / "data"
    figure_dir.mkdir(exist_ok=True)
    data_dir.mkdir(exist_ok=True)

    run_exact_identity_checks()

    mp.mp.dps = 100
    moments = fabius_moments(max_order)
    values = fabius_dyadic_values(moments)
    mersenne = mersenne_products(max_order)
    newton = fabius_newton_coefficients(moments, mersenne)
    endpoint = fabius_endpoint_extrapolants(moments, mersenne)

    # Cross-check the two independent formulas for all exact Newton
    # coefficients through a moderate order.
    direct_coefficients: List[Fraction] = []
    q_half = Fraction(1, 2)
    check_order = min(20, max_order)
    for k in range(check_order + 1):
        direct_coefficients.append(
            explicit_geometric_divided_difference(values, k, Fraction(1), q_half)
        )
        assert direct_coefficients[-1] == newton[k]

    # Cross-check endpoint values against the literal Lagrange row.
    for n in range(check_order + 1):
        weights = geometric_lagrange_zero_weights(n, q_half)
        literal = sum(weights[k] * values[k] for k in range(n + 1))
        assert literal == endpoint[n]
        if n > 0:
            # Successive Newton partial sums differ by A_n phi_n(0).
            increment = newton[n] * (-1) ** n * q_half ** (n * (n - 1) // 2)
            assert endpoint[n] - endpoint[n - 1] == increment

    write_csv(
        data_dir / "fabius_moments_and_comb_values.csv",
        ["n", "moment_exact", "F(2^-n)_exact", "F(2^-n)_decimal"],
        [
            (n, str(moments[n]), str(values[n]), mp.nstr(mp.mpf(values[n].numerator) / values[n].denominator, 25))
            for n in range(max_order + 1)
        ],
    )

    x_off_comb = Fraction(1, 3)
    partial_at_off_comb: List[Fraction] = []
    for n in range(max_order + 1):
        partial_at_off_comb.append(evaluate_newton_partial(newton[: n + 1], x_off_comb))

    write_csv(
        data_dir / "fabius_geometric_interpolation.csv",
        [
            "n",
            "newton_coefficient_exact",
            "log2_abs_coefficient",
            "log2_abs_coefficient_over_n_squared",
            "endpoint_extrapolant_exact",
            "log10_abs_endpoint_extrapolant",
            "P_n(1/3)_exact",
            "log10_1_plus_abs_P_n(1/3)",
        ],
        [
            (
                n,
                str(newton[n]),
                "" if newton[n] == 0 else mp.nstr(mp.log(abs(mp.mpf(newton[n].numerator) / newton[n].denominator), 2), 18),
                "" if n == 0 or newton[n] == 0 else mp.nstr(mp.log(abs(mp.mpf(newton[n].numerator) / newton[n].denominator), 2) / (n * n), 18),
                str(endpoint[n]),
                "" if endpoint[n] == 0 else mp.nstr(mp.log10(abs(mp.mpf(endpoint[n].numerator) / endpoint[n].denominator)), 18),
                str(partial_at_off_comb[n]),
                mp.nstr(mp.log10(1 + abs(mp.mpf(partial_at_off_comb[n].numerator) / partial_at_off_comb[n].denominator)), 18),
            )
            for n in range(max_order + 1)
        ],
    )

    # Figure 1: superexponential convergence at the accumulation point.
    ns_endpoint = [n for n in range(2, max_order + 1) if endpoint[n] != 0]
    logs_endpoint = [mp_log10_fraction(endpoint[n]) for n in ns_endpoint]
    fig = plt.figure(figsize=(7.2, 4.5))
    ax = fig.add_subplot(111)
    ax.plot(ns_endpoint, logs_endpoint, marker="o", markersize=2.8, linewidth=1.1)
    ax.set_xlabel("interpolation degree n")
    ax.set_ylabel(r"$\log_{10}|P_n(0)|$")
    ax.set_title("Fabius geometric-comb extrapolation at the accumulation point")
    ax.grid(True, alpha=0.3)
    save_figure(fig, figure_dir / "fabius_endpoint_extrapolation")

    # Figure 2: exact divergence at a representative off-comb point.
    ns_div = list(range(max_order + 1))
    logs_div = [
        float(mp.log10(1 + abs(mp.mpf(v.numerator) / v.denominator)))
        for v in partial_at_off_comb
    ]
    fig = plt.figure(figsize=(7.2, 4.5))
    ax = fig.add_subplot(111)
    ax.plot(ns_div, logs_div, marker="o", markersize=2.8, linewidth=1.1)
    ax.set_xlabel("interpolation degree n")
    ax.set_ylabel(r"$\log_{10}(1+|P_n(1/3)|)$")
    ax.set_title("Fabius Newton interpolants diverge away from the geometric comb")
    ax.grid(True, alpha=0.3)
    save_figure(fig, figure_dir / "fabius_newton_divergence")

    # Figure 3: evidence for the conjectural 1/4 quadratic growth exponent.
    ns_growth = [n for n in range(4, max_order + 1) if newton[n] != 0]
    scaled_growth = [
        float(mp.log(abs(mp.mpf(newton[n].numerator) / newton[n].denominator), 2) / (n * n))
        for n in ns_growth
    ]
    fig = plt.figure(figsize=(7.2, 4.5))
    ax = fig.add_subplot(111)
    ax.plot(ns_growth, scaled_growth, marker="o", markersize=2.8, linewidth=1.1, label=r"$n^{-2}\log_2|A_n|$")
    ax.axhline(0.25, linestyle="--", linewidth=1.1, label="conjectural limit 1/4")
    ax.set_xlabel("n")
    ax.set_ylabel("scaled logarithmic growth")
    ax.set_title("Quadratic growth of the Fabius geometric-Newton coefficients")
    ax.legend()
    ax.grid(True, alpha=0.3)
    save_figure(fig, figure_dir / "fabius_newton_coefficient_growth")

    # Figure 4: exact l1 row norm and its saturation for fixed q.
    q_values = [mp.mpf("0.25"), mp.mpf("0.5"), mp.mpf("0.75")]
    ns_norm = list(range(0, 51))
    norm_rows = []
    fig = plt.figure(figsize=(7.2, 4.5))
    ax = fig.add_subplot(111)
    for q_value in q_values:
        running = mp.mpf(1)
        norms = [running]
        for n in range(1, len(ns_norm)):
            running *= (1 + q_value**n) / (1 - q_value**n)
            norms.append(running)
        norm_rows.append((q_value, norms))
        ax.plot(ns_norm, [float(v) for v in norms], linewidth=1.3, label=f"q={q_value}")
    ax.set_xlabel("n")
    ax.set_ylabel(r"$\sum_k |\lambda_{n,k}^{(q)}|$")
    ax.set_yscale("log")
    ax.set_title("The zero-extrapolation Lagrange row has bounded variation")
    ax.legend()
    ax.grid(True, alpha=0.3)
    save_figure(fig, figure_dir / "lagrange_row_norm")

    write_csv(
        data_dir / "lagrange_row_norms.csv",
        ["n"] + [f"q={q_value}" for q_value, _ in norm_rows],
        [
            [n] + [mp.nstr(norms[n], 25) for _, norms in norm_rows]
            for n in ns_norm
        ],
    )

    # Figure 5: reciprocal sinc-product reconstruction.
    q_mp = mp.mpf("0.5")
    xi = mp.mpf("0.37")  # deliberately away from every integer zero
    true_hat = up_hat(q_mp, xi)
    true_reciprocal = 1 / true_hat
    max_filter_degree = 28
    filter_ns = list(range(max_filter_degree + 1))
    filter_errors: List[mp.mpf] = []
    approximants: List[mp.mpf] = []
    for n in filter_ns:
        approximation = reciprocal_up_filter(q_mp, xi, n)
        approximants.append(approximation)
        filter_errors.append(abs(approximation - true_reciprocal))

    write_csv(
        data_dir / "rvachev_reciprocal_filter.csv",
        ["n", "approximant", "absolute_error"],
        [
            (n, mp.nstr(approximants[n], 40), mp.nstr(filter_errors[n], 20))
            for n in filter_ns
        ],
    )

    positive_indices = [n for n in filter_ns if filter_errors[n] > 0]
    fig = plt.figure(figsize=(7.2, 4.5))
    ax = fig.add_subplot(111)
    ax.plot(
        positive_indices,
        [float(mp.log10(filter_errors[n])) for n in positive_indices],
        marker="o",
        markersize=3.0,
        linewidth=1.2,
    )
    ax.set_xlabel("filter degree n")
    ax.set_ylabel("log10 absolute error")
    ax.set_title(r"Reciprocal Rvachev sinc product from the $q=1/2$ Lagrange filter")
    ax.grid(True, alpha=0.3)
    save_figure(fig, figure_dir / "rvachev_reciprocal_filter")

    # A compact text summary is convenient when the archive is inspected
    # without compiling the report.
    with (output_dir / "NUMERICAL_SUMMARY.txt").open("w", encoding="utf-8") as handle:
        handle.write("Exact and high-precision checks completed successfully.\n\n")
        handle.write("Selected endpoint extrapolants P_n(0):\n")
        for n in range(0, min(12, max_order) + 1):
            handle.write(f"  n={n:2d}: {endpoint[n]}  ~= {float(endpoint[n]): .12e}\n")
        handle.write("\nSelected off-comb interpolants P_n(1/3):\n")
        selected_orders = (5, 10, 15, 20, 30, 40, 60, 80)
        for n in selected_orders:
            if n <= max_order:
                handle.write(f"  n={n:2d}: log10(1+|P_n|) = {mp.log10(1 + abs(mp.mpf(partial_at_off_comb[n].numerator) / partial_at_off_comb[n].denominator))}\n")
        handle.write("\nRvachev reciprocal-product check at xi=0.37:\n")
        handle.write(f"  hat(u)(xi)        = {mp.nstr(true_hat, 50)}\n")
        handle.write(f"  1/hat(u)(xi)      = {mp.nstr(true_reciprocal, 50)}\n")
        handle.write(f"  degree-28 error   = {mp.nstr(filter_errors[-1], 25)}\n")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("experiment_output"),
        help="directory receiving figures, CSV tables, and the text summary",
    )
    parser.add_argument(
        "--max-order",
        type=int,
        default=80,
        help="maximum exact Fabius moment/interpolation order (default: 80)",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    run_experiments(args.output_dir, max_order=args.max_order)
    print(f"Wrote experiment output to {args.output_dir.resolve()}")


if __name__ == "__main__":
    main()
