#!/usr/bin/env python3
"""Numerical experiments for interpolation on a geometric comb.

This script accompanies the report

    Interpolation on a Geometric Comb: q-Newton Calculus,
    Modal Extrapolation, Geometric B-Splines, and
    Fabius-Rvachev Connections.

The code is deliberately self-contained and heavily commented.  It performs
four families of checks/experiments:

1. It verifies the exact Gaussian moment-cancellation identities for the
   Lagrange weights at the accumulation point 0.
2. It studies the total-variation (noise amplification) factor
       K_n(q)=(-q;q)_n/(q;q)_n
   and its q -> 1 asymptotic.
3. It verifies the regular-variation boundary-layer limit on pure powers,
   where everything has a closed form.
4. It computes exact rational values F(2^{-m}) of the Fabius function from a
   triangular recurrence and applies the dyadic geometric-comb filter.  This
   checks the sign theorem and the sharp smooth-remainder bound developed in
   the report.

Outputs are written next to this script:
    moment_checks.csv
    stability_growth.csv
    regular_variation.csv
    fabius_boundary.csv
    stability_growth.png
    regular_variation_convergence.png
    fabius_boundary_ratio.png

Dependencies: Python 3, mpmath, matplotlib.
"""

from __future__ import annotations

import csv
from fractions import Fraction
from math import factorial
from pathlib import Path
from typing import Iterable

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams.update({"pdf.fonttype": 42, "ps.fonttype": 42})

import matplotlib.pyplot as plt
import mpmath as mp


HERE = Path(__file__).resolve().parent
mp.mp.dps = 140  # Extra precision is needed for alternating high-order filters.


def q_pochhammer_finite(a: mp.mpf, q: mp.mpf, n: int) -> mp.mpf:
    """Return (a;q)_n = product_{j=0}^{n-1} (1-a q^j)."""
    value = mp.mpf(1)
    for j in range(n):
        value *= 1 - a * q**j
    return value


def q_factorial(q: mp.mpf, n: int) -> mp.mpf:
    """Return (q;q)_n."""
    return q_pochhammer_finite(q, q, n)


def q_pochhammer_infinite(
    a: mp.mpf, q: mp.mpf, tolerance: mp.mpf | None = None
) -> mp.mpf:
    """Numerically evaluate (a;q)_infinity for 0<q<1.

    The product is stopped when |a q^j| is below ``tolerance``.  At the chosen
    precision this makes the truncation error far smaller than anything shown
    in the tables or figures.
    """
    if tolerance is None:
        tolerance = mp.power(10, -(mp.mp.dps - 20))
    value = mp.mpf(1)
    j = 0
    while True:
        term = a * q**j
        value *= 1 - term
        j += 1
        if abs(term) < tolerance:
            return value
        if j > 1_000_000:
            raise RuntimeError("infinite q-product did not converge")


def gaussian_binomial(n: int, k: int, q: mp.mpf) -> mp.mpf:
    """Return the Gaussian binomial coefficient [n choose k]_q."""
    if k < 0 or k > n:
        return mp.mpf(0)
    return q_factorial(q, n) / (q_factorial(q, k) * q_factorial(q, n - k))


def origin_lagrange_weights(n: int, q: mp.mpf) -> list[mp.mpf]:
    r"""Weights for extrapolation from 1,q,...,q^n to 0.

    lambda_{n,k}=(-1)^{n-k} q^{(n-k)(n-k+1)/2}
                 / ((q;q)_k (q;q)_{n-k}).
    """
    weights: list[mp.mpf] = []
    for k in range(n + 1):
        r = n - k
        weight = (
            (-1) ** r
            * q ** (r * (r + 1) // 2)
            / (q_factorial(q, k) * q_factorial(q, r))
        )
        weights.append(weight)
    return weights


def recursive_filter(samples: Iterable[mp.mpf], q: mp.mpf) -> mp.mpf:
    r"""Apply the Gaussian row by the factorized triangular recursion.

    If g_0(x)=f(x), define
        g_j(x)=(g_{j-1}(q x)-q^j g_{j-1}(x))/(1-q^j).
    Given samples f(1),f(q),...,f(q^n), this in-place divided-difference-like
    recursion returns g_n(1), equal to the direct weighted sum.  The algorithm
    avoids forming a Vandermonde system.
    """
    work = [mp.mpf(v) for v in samples]
    n = len(work) - 1
    for j in range(1, n + 1):
        denominator = 1 - q**j
        work = [
            (work[k + 1] - q**j * work[k]) / denominator
            for k in range(len(work) - 1)
        ]
    return work[0]


def write_moment_checks() -> None:
    """Verify exact moments up to n+3 at q=1/2."""
    q = mp.mpf("0.5")
    path = HERE / "moment_checks.csv"
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(
            [
                "n",
                "max_abs_annihilated_moment",
                "first_residual_numeric",
                "first_residual_closed_form",
                "direct_vs_recursive_error",
            ]
        )
        for n in range(1, 21):
            weights = origin_lagrange_weights(n, q)
            annihilated = [
                mp.fsum(weights[k] * q ** (k * d) for k in range(n + 1))
                for d in range(1, n + 1)
            ]
            first_residual = mp.fsum(
                weights[k] * q ** (k * (n + 1)) for k in range(n + 1)
            )
            closed = (-1) ** n * q ** (n * (n + 1) // 2)

            # A non-polynomial sample vector also checks the operator recursion.
            samples = [mp.e ** (q**k) for k in range(n + 1)]
            direct = mp.fsum(weights[k] * samples[k] for k in range(n + 1))
            recursive = recursive_filter(samples, q)
            writer.writerow(
                [
                    n,
                    mp.nstr(max(abs(x) for x in annihilated), 30),
                    mp.nstr(first_residual, 30),
                    mp.nstr(closed, 30),
                    mp.nstr(abs(direct - recursive), 30),
                ]
            )


def stability_factor_infinite(q: mp.mpf) -> mp.mpf:
    """Return K_infinity(q)=(-q;q)_infinity/(q;q)_infinity."""
    return q_pochhammer_infinite(-q, q) / q_pochhammer_infinite(q, q)


def write_stability_data_and_plot() -> None:
    """Study total variation and the modular q->1 asymptotic."""
    q_values = [mp.mpf("0.05") + mp.mpf(j) * mp.mpf("0.009") for j in range(105)]
    rows: list[tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]] = []
    for q in q_values:
        if q >= mp.mpf("0.991"):
            break
        exact = stability_factor_infinite(q)
        t = -mp.log(q)
        asymptotic = mp.sqrt(t) / (2 * mp.sqrt(mp.pi)) * mp.e ** (
            mp.pi**2 / (4 * t)
        )
        rows.append((q, exact, asymptotic, exact / asymptotic))

    with (HERE / "stability_growth.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(["q", "K_infinity", "asymptotic", "ratio"])
        for row in rows:
            writer.writerow([mp.nstr(x, 35) for x in row])

    x = [float(row[0]) for row in rows]
    y = [float(mp.log10(row[1])) for row in rows]
    plt.figure(figsize=(7.2, 4.6))
    plt.plot(x, y, linewidth=1.8)
    plt.xlabel(r"comb ratio $q$")
    plt.ylabel(r"$\log_{10} K_\infty(q)$")
    plt.title("Noise amplification of accumulation-point extrapolation")
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    plt.savefig(HERE / "stability_growth.png", dpi=210)
    plt.close()


def pure_power_normalized_multiplier(n: int, alpha: mp.mpf, q: mp.mpf) -> mp.mpf:
    r"""Return q^{-alpha n} G_n[x^alpha](1).

    The exact expression is (q^{1-alpha};q)_n/(q;q)_n.  Its limit is the
    regular-variation constant C_q(alpha).
    """
    return q_pochhammer_finite(q ** (1 - alpha), q, n) / q_factorial(q, n)


def regular_variation_constant(alpha: mp.mpf, q: mp.mpf) -> mp.mpf:
    """Return C_q(alpha)=(q^{1-alpha};q)_infinity/(q;q)_infinity."""
    return q_pochhammer_infinite(q ** (1 - alpha), q) / q_pochhammer_infinite(q, q)


def write_regular_variation_data_and_plot() -> None:
    """Show convergence of pure-power multipliers to boundary-layer limits."""
    q = mp.mpf("0.5")
    alphas = [mp.mpf("0.7"), mp.mpf("1.3"), mp.mpf("2.4")]
    with (HERE / "regular_variation.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(
            ["alpha", "n", "normalized_multiplier", "limit", "absolute_error"]
        )
        for alpha in alphas:
            limit = regular_variation_constant(alpha, q)
            for n in range(1, 51):
                value = pure_power_normalized_multiplier(n, alpha, q)
                writer.writerow(
                    [
                        mp.nstr(alpha, 12),
                        n,
                        mp.nstr(value, 40),
                        mp.nstr(limit, 40),
                        mp.nstr(abs(value - limit), 40),
                    ]
                )

    plt.figure(figsize=(7.2, 4.6))
    for alpha in alphas:
        limit = regular_variation_constant(alpha, q)
        ns = list(range(1, 41))
        errors = [
            float(abs(pure_power_normalized_multiplier(n, alpha, q) - limit))
            for n in ns
        ]
        plt.semilogy(ns, errors, linewidth=1.7, label=rf"$\alpha={float(alpha):.1f}$")
    plt.xlabel(r"filter order $n$")
    plt.ylabel("absolute error to boundary-layer limit")
    plt.title(r"Regular-variation constants for $q=1/2$")
    plt.grid(True, alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(HERE / "regular_variation_convergence.png", dpi=210)
    plt.close()


def fabius_dyadic_values_exact(max_index: int) -> list[Fraction]:
    r"""Compute V_m=F(2^{-m}) exactly as rational numbers.

    The triangular recurrence used in the source monograph is

      V_0 = 1,
      V_m = 2^{-m(m-1)/2}/(2^m-1)
            * sum_{k=0}^{m-1} 2^{k(k-1)/2} V_k/(m-k+1)!.

    It gives, for example, V_1=1/2 and V_2=5/72.
    """
    values = [Fraction(1, 1)]
    for m in range(1, max_index + 1):
        subtotal = Fraction(0, 1)
        for k in range(m):
            subtotal += (
                Fraction(2 ** (k * (k - 1) // 2), factorial(m - k + 1))
                * values[k]
            )
        value = subtotal / (2**m - 1) / (2 ** (m * (m - 1) // 2))
        values.append(value)
    return values


def half_q_factorial_exact(n: int) -> Fraction:
    """Return (1/2;1/2)_n exactly."""
    value = Fraction(1, 1)
    for j in range(1, n + 1):
        value *= Fraction(2**j - 1, 2**j)
    return value


def half_origin_weight_exact(n: int, k: int) -> Fraction:
    """Exact dyadic origin Lagrange weight."""
    r = n - k
    return (
        Fraction((-1) ** r, 2 ** (r * (r + 1) // 2))
        / (half_q_factorial_exact(k) * half_q_factorial_exact(r))
    )


def fabius_boundary_filter_exact(
    n: int, start_index: int, values: list[Fraction]
) -> Fraction:
    r"""Return sum lambda_{n,k} F(2^{-(start_index+k)}) exactly."""
    return sum(
        (
            half_origin_weight_exact(n, k) * values[start_index + k]
            for k in range(n + 1)
        ),
        Fraction(0, 1),
    )


def fabius_dyadic_values_mp(max_index: int) -> list[mp.mpf]:
    """High-precision version of the dyadic recurrence for larger plots."""
    values = [mp.mpf(1)]
    for m in range(1, max_index + 1):
        subtotal = mp.mpf(0)
        for k in range(m):
            subtotal += (
                mp.power(2, k * (k - 1) // 2)
                * values[k]
                / mp.factorial(m - k + 1)
            )
        value = (
            mp.power(2, -m * (m - 1) // 2)
            * subtotal
            / (mp.power(2, m) - 1)
        )
        values.append(value)
    return values


def write_fabius_data_and_plot() -> None:
    r"""Check the exact Fabius boundary identity and its sign/bound.

    We choose A=2^{-(n+1)}.  The theorem in the report states

      G_{n,1/2}F(A)
        = (-1)^n (2A)^{n+1}/(n+1)! * E[F(S_n)],

    where S_n is a Dirichlet average in [0,1].  Consequently the sign is
    (-1)^n and the absolute value is bounded by (2A)^{n+1}/(n+1)!.
    The ratio in the final column is exactly E[F(S_n)].
    """
    exact_values = fabius_dyadic_values_exact(28)
    rows = []
    for n in range(1, 13):
        start = n + 1
        filtered = fabius_boundary_filter_exact(n, start, exact_values)
        bound = Fraction(1, factorial(n + 1) * 2 ** (n * (n + 1)))
        ratio = abs(filtered) / bound
        rows.append((n, start, filtered, bound, ratio))

    with (HERE / "fabius_boundary.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(
            [
                "n",
                "M_with_A=2^-M",
                "filtered_exact",
                "smooth_bound_exact",
                "ratio_exact",
                "sign_check",
            ]
        )
        for n, start, filtered, bound, ratio in rows:
            writer.writerow(
                [
                    n,
                    start,
                    f"{filtered.numerator}/{filtered.denominator}",
                    f"{bound.numerator}/{bound.denominator}",
                    f"{ratio.numerator}/{ratio.denominator}",
                    ((-1) ** n) * filtered > 0,
                ]
            )

    # The plot uses high precision rather than enormous exact rationals.
    max_n = 36
    values_mp = fabius_dyadic_values_mp(2 * max_n + 3)
    ns = list(range(1, max_n + 1))
    ratios: list[float] = []
    for n in ns:
        start = n + 1
        weights = origin_lagrange_weights(n, mp.mpf("0.5"))
        filtered = mp.fsum(
            weights[k] * values_mp[start + k] for k in range(n + 1)
        )
        bound = mp.power(2, -n * (n + 1)) / mp.factorial(n + 1)
        ratios.append(float(abs(filtered) / bound))

    plt.figure(figsize=(7.2, 4.6))
    plt.semilogy(ns, ratios, marker="o", markersize=3.2, linewidth=1.5)
    plt.xlabel(r"filter order $n$")
    plt.ylabel(r"$|\mathcal{G}_{n,1/2}F(2^{-(n+1)})|/B_n$")
    plt.title("Normalized Fabius boundary remainder")
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    plt.savefig(HERE / "fabius_boundary_ratio.png", dpi=210)
    plt.close()


def main() -> None:
    """Run all checks and create all companion data/figures."""
    write_moment_checks()
    write_stability_data_and_plot()
    write_regular_variation_data_and_plot()
    write_fabius_data_and_plot()
    print(f"Wrote experiment outputs to {HERE}")


if __name__ == "__main__":
    main()
