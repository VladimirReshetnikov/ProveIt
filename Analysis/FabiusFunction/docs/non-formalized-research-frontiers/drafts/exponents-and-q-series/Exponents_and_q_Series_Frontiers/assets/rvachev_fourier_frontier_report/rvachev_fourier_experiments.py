#!/usr/bin/env python3
"""Numerical and symbolic experiments for finite Rvachev-up approximants.

This script accompanies the report

    Fourier Images of Recursive Piecewise-Polynomial Approximations
    to Rvachev's up Function

It is intentionally self-contained and focuses on reproducible checks of the
new Fourier-side statements in the report:

* the correction quotient A(z) = sinc(z)/Phi(z), where
      Phi(z) = prod_{k>=1} sinc(z/2^k);
* exact Taylor coefficients of A and their dominant-pole asymptotics;
* the 2-adic divisor sequence ord_{pi m} A = 1-v_2(m);
* exact mean-square constants for the algebraic Fourier tail of f_n;
* positive atomic moment closures that accelerate convergence.

The code uses arbitrary precision for infinite products and exact rational
arithmetic for coefficient/moment calculations.  All generated figures use
only default Matplotlib colors so that the output remains readable under
common display themes.

Usage
-----
    python rvachev_fourier_experiments.py --out-dir numerical_output

Dependencies
------------
    mpmath, sympy, numpy, matplotlib

Fourier convention
------------------
    hhat(t) = integral_R h(x) exp(-i t x) dx,
    sinc(z) = sin(z)/z.
"""

from __future__ import annotations

import argparse
import csv
import math
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import mpmath as mp
import numpy as np
import sympy as sp

# Select a non-interactive backend before importing pyplot.  This is important
# when the script is run in a headless reproducibility environment.
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


# ---------------------------------------------------------------------------
# Basic analytic objects
# ---------------------------------------------------------------------------


def sinc(z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Return sin(z)/z with the removable value at z=0 filled in."""

    if z == 0:
        return mp.mpf(1)
    return mp.sin(z) / z


def phi(z: mp.mpf | mp.mpc, *, tol: mp.mpf | None = None,
        max_terms: int = 500) -> mp.mpf | mp.mpc:
    """Evaluate Phi(z) = product_{k>=1} sinc(z/2^k).

    The omitted logarithmic tail is O(|z|^2 4^{-K}), so stopping when
    |z|/2^K is small is reliable at the working precision.  We multiply
    directly rather than summing logarithms because the experiments include
    real zeros, whose multiplicities we want to preserve visibly.
    """

    if tol is None:
        tol = mp.power(10, -(mp.mp.dps - 12) / 2)
    product = mp.mpf(1)
    scale = mp.mpf(2)
    for _k in range(1, max_terms + 1):
        w = z / scale
        product *= sinc(w)
        # Once w is tiny, the remaining product differs from one by a
        # geometric tail of order w^2/3.  The factor 0.25 makes the stopping
        # test conservative.
        if abs(w) ** 2 < tol * mp.mpf("0.25"):
            return product
        scale *= 2
    raise RuntimeError("phi product did not converge within max_terms")


def correction_A(z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Evaluate A(z) by the stable identity A(z)=cos(z/2)/Phi(z/2).

    The expression is meromorphic.  At a pole the numerical result becomes
    very large rather than being regularized; this is useful for plotting the
    spectral conditioning thresholds.
    """

    return mp.cos(z / 2) / phi(z / 2)


def finite_transform(n: int, t: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Fourier transform F_n of the n-th recursive spline approximant.

    F_n(t) = prod_{k=1}^{n-1} sinc(t/2^k) * sinc(t/2^n)^2.
    """

    if n < 1:
        raise ValueError("n must be at least 1")
    result = mp.mpf(1)
    for k in range(1, n):
        result *= sinc(t / mp.power(2, k))
    result *= sinc(t / mp.power(2, n)) ** 2
    return result


# ---------------------------------------------------------------------------
# Exact arithmetic: Taylor coefficients, moments, and 2-adic data
# ---------------------------------------------------------------------------


def taylor_coefficients_A(order: int) -> list[sp.Rational]:
    r"""Return rho_0,...,rho_order in A(z)=sum rho_j z^(2j).

    We use the exact logarithmic series

      log A(z) = sum_{r>=1} ell_r z^(2r),
      ell_r = - 2^(2r-1)|B_{2r}|/[r(2r)!] * (4^r-2)/(4^r-1).

    If A(x)=exp(L(x)) with x=z^2, coefficient comparison in A'=L'A gives

      n rho_n = sum_{k=1}^n k ell_k rho_{n-k}.

    All operations below are exact SymPy rational operations.
    """

    if order < 0:
        raise ValueError("order must be nonnegative")
    rho: list[sp.Rational] = [sp.Rational(1)]
    ell: list[sp.Rational] = [sp.Rational(0)]
    for r in range(1, order + 1):
        bern = abs(sp.bernoulli(2 * r))
        value = -(
            sp.Integer(2) ** (2 * r - 1)
            * bern
            / (sp.Integer(r) * sp.factorial(2 * r))
            * (sp.Integer(4) ** r - 2)
            / (sp.Integer(4) ** r - 1)
        )
        ell.append(sp.factor(value))

    for n in range(1, order + 1):
        total = sum(sp.Integer(k) * ell[k] * rho[n - k]
                    for k in range(1, n + 1))
        rho.append(sp.factor(total / n))
    return rho


def v2(m: int) -> int:
    """Return the exponent of 2 in a positive integer m."""

    if m <= 0:
        raise ValueError("v2 is defined here only for positive integers")
    return (m & -m).bit_length() - 1


def binary_digit_sum(m: int) -> int:
    """Return s_2(m), the number of 1s in the binary expansion of m."""

    if m < 0:
        raise ValueError("m must be nonnegative")
    return m.bit_count()


def finite_zero_multiplicity(n: int, m: int) -> int:
    r"""Multiplicity of F_n at t=2*pi*m (m != 0).

    The exact formula is

      d_n(m) = v_2(m)+1,  if v_2(m) <= n-2,
               n+1,       if v_2(m) >= n-1.
    """

    if n < 1 or m == 0:
        raise ValueError("need n>=1 and m!=0")
    valuation = v2(abs(m))
    if valuation <= n - 2:
        return valuation + 1
    return n + 1


def up_even_moments(max_r: int) -> list[sp.Rational]:
    r"""Return E[X^(2r)] for the up density, 0<=r<=max_r.

    Phi(z) is the characteristic function E[e^{-izX}], so

      Phi(z) = sum_r (-1)^r E[X^(2r)] z^(2r)/(2r)!.

    The finite truncation of log Phi is obtained from

      log sinc z = -sum_{r>=1} 2^(2r-1)|B_{2r}| z^(2r)/(r(2r)!),

    followed by the dyadic geometric sum sum_{k>=1}4^{-rk}=1/(4^r-1).
    """

    x = sp.symbols("x")  # x stands for z^2
    log_phi = sp.Integer(0)
    for r in range(1, max_r + 1):
        coeff = -(
            sp.Integer(2) ** (2 * r - 1)
            * abs(sp.bernoulli(2 * r))
            / (sp.Integer(r) * sp.factorial(2 * r))
            / (sp.Integer(4) ** r - 1)
        )
        log_phi += coeff * x ** r
    series = sp.series(sp.exp(log_phi), x, 0, max_r + 1).removeO().expand()
    moments: list[sp.Rational] = []
    for r in range(0, max_r + 1):
        coeff = sp.Rational(series.coeff(x, r))
        moments.append(sp.factor((-1) ** r * sp.factorial(2 * r) * coeff))
    return moments


def combined_pair_moments(nodes: Sequence[sp.Rational],
                          pair_weights: Sequence[sp.Rational],
                          max_r: int) -> list[sp.Rational]:
    """Moments for a symmetric atomic law.

    `pair_weights[j]` is the *combined* mass at +nodes[j] and -nodes[j].
    A possible central mass contributes only to the zeroth moment and is not
    needed for positive even moments.
    """

    if len(nodes) != len(pair_weights):
        raise ValueError("nodes and pair_weights must have equal length")
    return [
        sp.factor(sum(w * a ** (2 * r) for a, w in zip(nodes, pair_weights)))
        for r in range(1, max_r + 1)
    ]


# ---------------------------------------------------------------------------
# Exact periodic mean-square constant I_n
# ---------------------------------------------------------------------------


def I_exact(n: int) -> sp.Rational:
    r"""Exact mean of sin^4(u) prod_{j=1}^{n-1} sin^2(2^j u).

    I_n = [2^(n+2)+(-1)^(n+1)]/[3*2^(2n+1)].
    """

    if n < 1:
        raise ValueError("n must be at least 1")
    return sp.Rational(2 ** (n + 2) + (-1) ** (n + 1), 3 * 2 ** (2 * n + 1))


def I_numeric(n: int) -> mp.mpf:
    """Numerically integrate I_n on [0,pi] using arbitrary precision."""

    def integrand(u: mp.mpf) -> mp.mpf:
        value = mp.sin(u) ** 4
        for j in range(1, n):
            value *= mp.sin(mp.power(2, j) * u) ** 2
        return value

    # Split into dyadic subintervals so the adaptive quadrature resolves the
    # highest oscillation without relying on chance sample placement.
    pieces = 2 ** max(0, n - 1)
    grid = [mp.pi * j / pieces for j in range(pieces + 1)]
    return mp.fsum(mp.quad(integrand, [grid[j], grid[j + 1]])
                   for j in range(pieces)) / mp.pi


# ---------------------------------------------------------------------------
# Plotting and tabulation
# ---------------------------------------------------------------------------


def write_coefficient_table(path: Path, rho: Sequence[sp.Rational],
                            phi_pi: mp.mpf) -> None:
    """Write exact and scaled Taylor coefficients to CSV."""

    limit = 2 / phi_pi
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow([
            "j", "rho_j_exact", "rho_j_decimal",
            "rho_j_times_(4pi)^(2j)", "scaled_minus_limit"
        ])
        for j, value in enumerate(rho):
            numeric = mp.mpf(str(sp.N(value, mp.mp.dps)))
            scaled = numeric * (4 * mp.pi) ** (2 * j)
            writer.writerow([
                j,
                str(value),
                mp.nstr(numeric, 30),
                mp.nstr(scaled, 30),
                mp.nstr(scaled - limit, 30),
            ])


def plot_coefficient_asymptotics(path: Path, rho: Sequence[sp.Rational],
                                 phi_pi: mp.mpf) -> None:
    """Plot convergence to the dominant-pole coefficient asymptotic."""

    js = np.arange(2, len(rho), dtype=int)
    limit_mp = 2 / phi_pi
    errors = np.array([
        float(abs(
            mp.mpf(str(sp.N(rho[j], 100))) * (4 * mp.pi) ** (2 * j)
            - limit_mp
        ))
        for j in js
    ])
    errors = np.maximum(errors, 1e-300)

    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ax.semilogy(js, errors, marker="o", markersize=3, linewidth=1,
                label=r"$|\rho_j(4\pi)^{2j}-2/\Phi(\pi)|$")
    ax.set_xlabel(r"coefficient index $j$")
    ax.set_ylabel("absolute asymptotic error")
    ax.set_title("Dominant-pole convergence of the correction coefficients")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(path, dpi=180)
    plt.close(fig)

def plot_divisor_arithmetic(path: Path, max_m: int = 64) -> None:
    """Plot divisor orders 1-v_2(m) and their digit-sum partial sums."""

    ms = np.arange(1, max_m + 1)
    orders = np.array([1 - v2(int(m)) for m in ms])
    partial = np.cumsum(orders)
    digit_sums = np.array([binary_digit_sum(int(m)) for m in ms])

    fig, ax = plt.subplots(figsize=(9.0, 5.0))
    ax.stem(ms, orders, linefmt="C0-", markerfmt="C0o", basefmt="k-",
            label=r"$\operatorname{ord}_{\pi m}A=1-v_2(m)$")
    ax.plot(ms, partial, linewidth=1.4,
            label=r"partial sum $=s_2(M)$")
    ax.plot(ms, digit_sums, linestyle="--", linewidth=1.0,
            label=r"binary digit sum $s_2(M)$")
    ax.set_xlabel(r"integer $m$ (or cutoff $M$)")
    ax.set_ylabel("order / cumulative order")
    ax.set_title("2-adic divisor arithmetic of the correction quotient")
    ax.grid(True, alpha=0.25)
    ax.legend(loc="upper left")
    fig.tight_layout()
    fig.savefig(path, dpi=180)
    plt.close(fig)


def plot_correction_profile(path: Path) -> None:
    """Plot A(x) up to the first real pole at 4*pi.

    The graph is clipped vertically for readability.  Exact zeros at odd
    multiples of pi, removable points at 2*pi times an odd integer, and the
    pole at 4*pi are annotated in the caption of the report.
    """

    eps = 1e-4
    xs = np.linspace(-4 * math.pi + eps, 4 * math.pi - eps, 3200)
    ys = []
    for x in xs:
        try:
            y = float(correction_A(mp.mpf(x)))
        except (ValueError, ZeroDivisionError, OverflowError):
            y = math.nan
        ys.append(y)
    ys_array = np.asarray(ys)
    ys_clipped = np.clip(ys_array, -12, 12)

    fig, ax = plt.subplots(figsize=(9.0, 5.0))
    ax.plot(xs / math.pi, ys_clipped, linewidth=1.0,
            label=r"$A(x)=\operatorname{sinc}x/\Phi(x)$ (clipped)")
    for integer in range(-4, 5):
        if integer == 0:
            continue
        ax.axvline(integer, linestyle=":" if abs(integer) < 4 else "--",
                   linewidth=0.8, alpha=0.6)
    ax.axhline(0, linewidth=0.8)
    ax.set_xlim(-4, 4)
    ax.set_ylim(-12, 12)
    ax.set_xlabel(r"$x/\pi$")
    ax.set_ylabel(r"$A(x)$")
    ax.set_title("Correction profile and the first spectral pole")
    ax.grid(True, alpha=0.2)
    ax.legend(loc="upper center")
    fig.tight_layout()
    fig.savefig(path, dpi=180)
    plt.close(fig)


def plot_relative_error_windows(path: Path) -> None:
    """Plot forward and inverse spectral conditioning profiles.

    Since F_n(t)/Phi(t)=A(2^{-n}t), the two curves are universal after the
    critical rescaling t=2^n z.  Zeros of A make the inverse multiplier
    singular; poles of A make the forward multiplier singular.
    """

    xs = np.linspace(0, 3.95 * math.pi, 2200)
    abs_a = []
    abs_inverse = []
    for x in xs:
        value = abs(float(correction_A(mp.mpf(x))))
        abs_a.append(max(value, 1e-14))
        abs_inverse.append(min(1 / max(value, 1e-14), 1e14))

    fig, ax = plt.subplots(figsize=(8.5, 4.8))
    ax.semilogy(xs / math.pi, abs_a, linewidth=1.2,
                label=r"forward multiplier $|A(z)|$")
    ax.semilogy(xs / math.pi, abs_inverse, linewidth=1.2,
                label=r"inverse multiplier $|A(z)|^{-1}$")
    ax.axvline(1, linestyle=":", linewidth=1.0,
               label=r"first inverse pole $z=\pi$")
    ax.axvline(4, linestyle="--", linewidth=1.0,
               label=r"first forward pole $z=4\pi$")
    ax.set_xlabel(r"critical variable $z=t/2^n$ in units of $\pi$")
    ax.set_ylabel("multiplier magnitude")
    ax.set_title("Universal forward/inverse conditioning boundary layer")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(loc="upper center", ncol=2)
    fig.tight_layout()
    fig.savefig(path, dpi=180)
    plt.close(fig)


def plot_transform_comparison(path: Path) -> None:
    """Compare |F_n(t)| with the limiting sinc product |Phi(t)|."""

    xs = np.linspace(0, 80, 1800)
    floor = 1e-18
    phi_values = np.array([
        max(abs(float(phi(mp.mpf(x)))), floor) for x in xs
    ])

    fig, ax = plt.subplots(figsize=(9.0, 5.0))
    ax.semilogy(xs, phi_values, linewidth=1.5,
                label=r"limit $|\Phi(t)|$")
    for n in (3, 5, 8):
        values = np.array([
            max(abs(float(finite_transform(n, mp.mpf(x)))), floor)
            for x in xs
        ])
        ax.semilogy(xs, values, linewidth=0.9, label=rf"$|F_{{{n}}}(t)|$")
    ax.set_xlabel(r"frequency $t$")
    ax.set_ylabel("Fourier magnitude")
    ax.set_title("Finite recursive splines versus the Rvachev limit")
    ax.grid(True, which="both", alpha=0.22)
    ax.legend()
    fig.tight_layout()
    fig.savefig(path, dpi=180)
    plt.close(fig)

def write_text_summary(path: Path, rho: Sequence[sp.Rational],
                       phi_pi: mp.mpf) -> None:
    """Write a human-readable record of all principal numerical checks."""

    moments = up_even_moments(5)

    # Explicit positive moment closures.  Pair weights are combined masses at
    # +/-node; the remaining mass is at zero.
    closures = {
        "r=1, nodes 1": (
            [sp.Rational(1)],
            [sp.Rational(1, 9)],
        ),
        "r=2, nodes 1,1/2": (
            [sp.Rational(1), sp.Rational(1, 2)],
            [sp.Rational(1, 2025), sp.Rational(896, 2025)],
        ),
        "r=3, nodes 1,1/2,1/4": (
            [sp.Rational(1), sp.Rational(1, 2), sp.Rational(1, 4)],
            [
                sp.Rational(10411, 2679075),
                sp.Rational(1003648, 2679075),
                sp.Rational(581632, 2679075),
            ],
        ),
    }

    with path.open("w", encoding="utf-8") as handle:
        handle.write("Rvachev finite-approximant Fourier experiments\n")
        handle.write("=" * 58 + "\n\n")
        handle.write(f"mpmath precision: {mp.mp.dps} decimal digits\n")
        handle.write(f"Phi(pi) = {mp.nstr(phi_pi, 60)}\n")
        handle.write(f"2/Phi(pi) = {mp.nstr(2/phi_pi, 60)}\n")
        handle.write(
            "1/(16*pi^2) = " + mp.nstr(1/(16*mp.pi**2), 60) + "\n\n"
        )

        handle.write("First exact Taylor coefficients A(z)=sum rho_j z^(2j):\n")
        for j, value in enumerate(rho[:12]):
            handle.write(f"  rho_{j} = {value}\n")
        handle.write("\nScaled coefficients rho_j(4*pi)^(2j):\n")
        for j in (2, 3, 4, 5, 10, 15, 20, 30, 40, 50):
            if j < len(rho):
                numeric = mp.mpf(str(sp.N(rho[j], mp.mp.dps)))
                scaled = numeric * (4 * mp.pi) ** (2 * j)
                handle.write(f"  j={j:2d}: {mp.nstr(scaled, 35)}\n")

        handle.write("\nExact periodic mean-square constants I_n:\n")
        for n in range(1, 9):
            exact = I_exact(n)
            numeric = I_numeric(n)
            error = numeric - mp.mpf(exact.p) / exact.q
            handle.write(
                f"  n={n}: exact={exact}, numerical={mp.nstr(numeric, 30)}, "
                f"error={mp.nstr(error, 8)}\n"
            )

        handle.write("\nEven moments of the up density:\n")
        for r, moment in enumerate(moments):
            handle.write(f"  E[X^{2*r}] = {moment}\n")

        handle.write("\nPositive dyadic atomic moment closures:\n")
        for name, (nodes, weights) in closures.items():
            matched = combined_pair_moments(nodes, weights, len(nodes))
            central = sp.factor(1 - sum(weights))
            handle.write(f"  {name}\n")
            handle.write(f"    combined pair weights: {weights}\n")
            handle.write(f"    central weight: {central}\n")
            for r, value in enumerate(matched, start=1):
                handle.write(
                    f"    moment {2*r}: closure={value}, up={moments[r]}, "
                    f"difference={sp.factor(value-moments[r])}\n"
                )

        handle.write("\nDivisor partial-sum check M-v2(M!)=s_2(M):\n")
        cumulative = 0
        for m in range(1, 33):
            cumulative += 1 - v2(m)
            assert cumulative == binary_digit_sum(m)
            handle.write(
                f"  M={m:2d}: cumulative order={cumulative}, "
                f"s_2(M)={binary_digit_sum(m)}\n"
            )

        handle.write("\nFinite zero multiplicities d_n(m):\n")
        for n in range(2, 7):
            row = [finite_zero_multiplicity(n, 2 ** v) for v in range(0, 9)]
            handle.write(f"  n={n}, valuations v=0..8: {row}\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("numerical_output"),
        help="directory for figures and tables (default: numerical_output)",
    )
    parser.add_argument(
        "--precision",
        type=int,
        default=100,
        help="mpmath decimal precision (default: 100)",
    )
    args = parser.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = args.precision

    # Fifty coefficients are enough to make the dominant-pole asymptotic
    # visually unmistakable while keeping exact rational arithmetic fast.
    rho = taylor_coefficients_A(50)
    phi_pi = phi(mp.pi)

    # Sanity checks for the identities used in the report.
    for sample in (mp.mpf("0.3"), mp.mpf("1.7"), mp.mpf("5.1")):
        lhs = correction_A(sample)
        rhs = sinc(sample) / phi(sample)
        assert mp.almosteq(lhs, rhs)
        functional_rhs = (sample / 2) / mp.tan(sample / 2) * correction_A(sample / 2)
        assert mp.almosteq(lhs, functional_rhs)

    # Exact low-order coefficients quoted in the report.
    expected = [
        sp.Rational(1),
        sp.Rational(-1, 9),
        sp.Rational(2, 2025),
        sp.Rational(1, 2679075),
        sp.Rational(58, 10247461875),
    ]
    assert rho[:5] == expected

    write_coefficient_table(args.out_dir / "taylor_coefficients.csv", rho, phi_pi)
    write_text_summary(args.out_dir / "numerical_results.txt", rho, phi_pi)
    plot_coefficient_asymptotics(
        args.out_dir / "coefficient_asymptotics.png", rho, phi_pi
    )
    plot_divisor_arithmetic(args.out_dir / "divisor_arithmetic.png")
    plot_correction_profile(args.out_dir / "correction_profile.png")
    plot_relative_error_windows(args.out_dir / "critical_boundary_layer.png")
    plot_transform_comparison(args.out_dir / "finite_transform_comparison.png")

    print(f"Wrote numerical outputs to {args.out_dir.resolve()}")
    print(f"Phi(pi) = {mp.nstr(phi_pi, 35)}")
    print(f"2/Phi(pi) = {mp.nstr(2/phi_pi, 35)}")
    print("All exact arithmetic and functional-equation checks passed.")


if __name__ == "__main__":
    main()
