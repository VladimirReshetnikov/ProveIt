#!/usr/bin/env python3
"""
Numerical experiments accompanying the Fabius/Rvachev frontier report.

The program focuses on identities that can be checked independently at high
precision:

  1. the sinc-product and the regrouped canonical product;
  2. the exact Fourier-zero counting law N(2*pi*M) = 2*M - s_2(M);
  3. the exact log-periodic decomposition of log M(t);
  4. the Fourier coefficients of the periodic fluctuation;
  5. the consistency of the refined inverse-Fabius expansion with exact
     cumulant-saddle data.

No floating-point value is used as a proof.  The calculations are diagnostic:
they detect normalization mistakes, sign errors, and missing factors of 2 or pi.

Run:
    python numerical_experiments.py --output-dir .

Dependencies:
    mpmath
    matplotlib (optional; tables are still produced without it)
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import Iterable

import mpmath as mp


def sinc(z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Entire normalized sinc, sin(z)/z, with its removable value at zero."""
    return mp.mpf(1) if z == 0 else mp.sin(z) / z


def log_sinhc(x: mp.mpf) -> mp.mpf:
    """log(sinh(x)/x) for positive real x, evaluated stably near zero."""
    x = mp.mpf(x)
    if abs(x) < mp.mpf("1e-8"):
        # Terms through x^10 are more than sufficient once the threshold is met.
        x2 = x * x
        return (
            x2 / 6
            - x2**2 / 180
            + x2**3 / 2835
            - x2**4 / 37800
            + x2**5 / 467775
        )
    return mp.log(mp.sinh(x) / x)


def phi_sinc_product(z: mp.mpf | mp.mpc, tol: mp.mpf | None = None) -> mp.mpf | mp.mpc:
    """Phi(z) = product_{n>=1} sinc(z/2^n)."""
    tol = tol or mp.power(10, -(mp.mp.dps - 15))
    product = mp.mpf(1)
    n = 1
    while True:
        x = z / mp.power(2, n)
        factor = sinc(x)
        product *= factor
        # sinc(x)-1 = O(x^2); this controls the remaining tail geometrically.
        if abs(x) < 1 and abs(x * x) < tol:
            break
        n += 1
        if n > 10000:
            raise RuntimeError("sinc product failed to converge")
    return product


def nu2(n: int) -> int:
    """The 2-adic valuation of a positive integer."""
    if n <= 0:
        raise ValueError("nu2 is defined here only for positive integers")
    return (n & -n).bit_length() - 1


def binary_digit_sum(n: int) -> int:
    """s_2(n), the number of 1 bits in n."""
    return n.bit_count()


def zero_count(M: int) -> int:
    """Total multiplicity of positive zeros 2*pi*m with 1 <= m <= M."""
    return sum(1 + nu2(m) for m in range(1, M + 1))


def spectral_zeta(s: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Z_Phi(s) = (2*pi)^(-s) zeta(s)/(1-2^(-s))."""
    return mp.power(2 * mp.pi, -s) * mp.zeta(s) / (1 - mp.power(2, -s))


def phi_canonical_product(
    z: mp.mpf | mp.mpc, M: int = 20000
) -> mp.mpf | mp.mpc:
    """
    Truncated canonical product
        product_{m>=1} (1-z^2/(2*pi*m)^2)^(1+nu2(m)).

    The paired quadratic factors give absolute local convergence.  The tail is
    O(|z|^2/M), so this form is intended for cross-checks rather than extreme
    precision.
    """
    product = mp.mpf(1)
    for m in range(1, M + 1):
        product *= (
            1 - z * z / mp.power(2 * mp.pi * m, 2)
        ) ** (1 + nu2(m))
    return product


def log_mgf(t: mp.mpf, tol: mp.mpf | None = None) -> mp.mpf:
    """K(t)=log M(t)=sum_{n>=1} log(sinh(t/2^n)/(t/2^n))."""
    t = mp.mpf(t)
    if t <= 0:
        raise ValueError("this real-valued implementation expects t>0")
    tol = tol or mp.power(10, -(mp.mp.dps - 15))
    total = mp.mpf(0)
    n = 1
    while True:
        x = t / mp.power(2, n)
        term = log_sinhc(x)
        total += term
        if x < 1 and abs(term) < tol:
            break
        n += 1
        if n > 10000:
            raise RuntimeError("log M series failed to converge")
    return total


def _f1(x: mp.mpf) -> mp.mpf:
    """Derivative of log(sinh x/x), stable near x=0."""
    if abs(x) < mp.mpf("1e-5"):
        x2 = x * x
        return x / 3 - x * x2 / 45 + 2 * x * x2**2 / 945 - x * x2**3 / 4725
    return mp.coth(x) - 1 / x


def _f2(x: mp.mpf) -> mp.mpf:
    """Second derivative of log(sinh x/x), stable near x=0."""
    if abs(x) < mp.mpf("1e-5"):
        x2 = x * x
        return mp.mpf(1) / 3 - x2 / 15 + 2 * x2**2 / 189 - x2**3 / 675
    return 1 / (x * x) - 1 / (mp.sinh(x) ** 2)


def K1(t: mp.mpf, tol: mp.mpf | None = None) -> mp.mpf:
    """First derivative K'(t), summed factor by factor."""
    t = mp.mpf(t)
    tol = tol or mp.power(10, -(mp.mp.dps - 15))
    total = mp.mpf(0)
    n = 1
    while True:
        scale = mp.power(2, -n)
        term = scale * _f1(t * scale)
        total += term
        if abs(term) < tol:
            break
        n += 1
        if n > 10000:
            raise RuntimeError("K' series failed to converge")
    return total


def K2(t: mp.mpf, tol: mp.mpf | None = None) -> mp.mpf:
    """Second derivative K''(t), i.e. the tilted variance."""
    t = mp.mpf(t)
    tol = tol or mp.power(10, -(mp.mp.dps - 15))
    total = mp.mpf(0)
    n = 1
    while True:
        scale = mp.power(2, -n)
        term = scale * scale * _f2(t * scale)
        total += term
        if abs(term) < tol:
            break
        n += 1
        if n > 10000:
            raise RuntimeError("K'' series failed to converge")
    return total


A = mp.log(2)


def psi_split(theta: mp.mpf, tol: mp.mpf | None = None) -> mp.mpf:
    """
    The exact 1-periodic fluctuation Psi(theta) from the split-sum formula.

    theta may be any real number; reducing modulo 1 also makes endpoint tests
    insensitive to tiny rounding errors.
    """
    theta = mp.frac(theta)
    tol = tol or mp.power(10, -(mp.mp.dps - 15))
    total = -mp.power(2, theta) + A * (theta * theta + theta) / 2

    j = 0
    while True:
        exponent = mp.power(2, j + theta + 1)
        term = mp.log1p(-mp.e ** (-exponent))
        total += term
        if abs(term) < tol:
            break
        j += 1
        if j > 10000:
            raise RuntimeError("large-argument part of Psi failed to converge")

    k = 1
    while True:
        x = mp.power(2, theta - k)
        term = log_sinhc(x)
        total += term
        if abs(term) < tol:
            break
        k += 1
        if k > 10000:
            raise RuntimeError("small-argument part of Psi failed to converge")
    return total


def transseries_remainder(t: mp.mpf, tol: mp.mpf | None = None) -> mp.mpf:
    """R(t)=-sum_{ell>=0} log(1-exp(-2^(ell+1)t))."""
    t = mp.mpf(t)
    tol = tol or mp.power(10, -(mp.mp.dps - 15))
    total = mp.mpf(0)
    ell = 0
    while True:
        term = -mp.log1p(-mp.e ** (-mp.power(2, ell + 1) * t))
        total += term
        if abs(term) < tol:
            break
        ell += 1
        if ell > 10000:
            raise RuntimeError("transseries remainder failed to converge")
    return total


def psi_c0() -> mp.mpf:
    """Mean Fourier coefficient of Psi."""
    gamma1 = mp.stieltjes(1)
    return (gamma1 + mp.euler**2 / 2 - mp.pi**2 / 12) / A - A / 12


def psi_ck(k: int) -> mp.mpc:
    """Nonzero Fourier coefficient c_k of Psi."""
    if k == 0:
        return mp.mpc(psi_c0())
    chi = 2 * mp.pi * 1j * k / A
    return (
        mp.pi
        * mp.power(2 * mp.pi, -chi)
        * mp.zeta(chi)
        / (A * chi * mp.sin(mp.pi * chi / 2))
    )


def psi_fourier(theta: mp.mpf, harmonics: int = 8) -> mp.mpf:
    """Psi reconstructed from c_0 and symmetric nonzero harmonics."""
    theta = mp.mpf(theta)
    value = mp.mpc(psi_c0())
    for k in range(1, harmonics + 1):
        value += 2 * mp.re(psi_ck(k) * mp.e ** (2 * mp.pi * 1j * k * theta))
    return mp.re(value)


def psi_prime(theta: mp.mpf, harmonics: int = 8) -> mp.mpf:
    """Derivative d Psi/d theta from the rapidly convergent Fourier series."""
    theta = mp.mpf(theta)
    value = mp.mpc(0)
    for k in range(1, harmonics + 1):
        term = (2 * mp.pi * 1j * k) * psi_ck(k)
        value += 2 * mp.re(term * mp.e ** (2 * mp.pi * 1j * k * theta))
    return mp.re(value)


def log_mgf_transseries(t: mp.mpf, harmonics: int = 8) -> mp.mpf:
    """Exact decomposition, with Psi evaluated by its Fourier series."""
    q = mp.log(t)
    theta = q / A
    return (
        t
        - q * q / (2 * A)
        - q / 2
        + psi_fourier(theta, harmonics)
        + transseries_remainder(t)
    )


def inverse_q_approximation(Y: mp.mpf, harmonics: int = 8) -> mp.mpf:
    """
    Refined asymptotic approximation to q=log t as a function of
    Y=-log F(x), using the theorem in the report.

    This routine evaluates the tiny periodic term at the leading phase.
    """
    Y = mp.mpf(Y)
    Q = mp.sqrt(2 * A * Y)
    c = 1 + A / 2
    theta0 = (Q + c) / A
    p = psi_prime(theta0, harmonics)
    C = (
        -mp.mpf("0.5")
        - psi_fourier(theta0, harmonics)
        + p / A
        + mp.log(2 * mp.pi / A) / 2
    )
    return Q + c + (-A * mp.log(Q) / 2 + c * c / 2 - A * C) / Q


def fmt(x: mp.mpf | mp.mpc, digits: int = 14) -> str:
    """Compact LaTeX-safe decimal/scientific rendering."""
    if isinstance(x, mp.mpc):
        return mp.nstr(x, digits)
    return mp.nstr(mp.mpf(x), digits)


def write_tables(out: Path) -> None:
    """Generate a LaTeX fragment containing reproducible numerical checks."""
    rows_trans = []
    for t in [mp.mpf("2.3"), mp.mpf("10"), mp.mpf("100"), mp.mpf("1000")]:
        direct = log_mgf(t)
        reconstructed = log_mgf_transseries(t, harmonics=8)
        rows_trans.append((t, direct, abs(direct - reconstructed)))

    rows_psi = []
    for theta in [mp.mpf(k) / 8 for k in range(8)]:
        split = psi_split(theta)
        fourier = psi_fourier(theta, harmonics=8)
        rows_psi.append((theta, split, abs(split - fourier)))

    rows_inverse = []
    # Use exact K, K', and K'' at prescribed saddle parameters.  The resulting
    # Y includes the leading Daniels saddle prefactor; this tests the inversion
    # algebra without pretending that the saddle approximation is exact data.
    for q in [mp.mpf("8"), mp.mpf("12"), mp.mpf("16"), mp.mpf("20")]:
        t = mp.e ** q
        x = 1 - K1(t)
        log_y_sp = log_mgf(t) - t * (1 - x) - mp.log(2 * mp.pi * K2(t)) / 2
        Y = -log_y_sp
        q_app = inverse_q_approximation(Y, harmonics=8)
        rows_inverse.append((q, x, Y, q_app - q))

    c1 = psi_ck(1)
    latex = [
        r"\begin{table}[tbp]",
        r"\centering",
        r"\caption{High-precision verification of the exact decomposition "
        r"$K(t)=t-(\log t)^2/(2\log2)-(\log t)/2+\Psi(\log_2t)+R(t)$.}",
        r"\label{tab:transseries-check}",
        r"\begin{tabular}{@{}rll@{}}",
        r"\toprule",
        r"$t$ & $K(t)$ from the defining product & absolute discrepancy \\",
        r"\midrule",
    ]
    for t, direct, err in rows_trans:
        latex.append(f"${fmt(t,8)}$ & ${fmt(direct,18)}$ & ${fmt(err,5)}$ \\\\")
    latex += [r"\bottomrule", r"\end{tabular}", r"\end{table}", ""]

    latex += [
        r"\begin{table}[tbp]",
        r"\centering",
        r"\caption{The split-sum definition of $\Psi$ versus its Fourier series "
        r"(eight positive harmonics).}",
        r"\label{tab:psi-check}",
        r"\begin{tabular}{@{}rll@{}}",
        r"\toprule",
        r"$\theta$ & $\Psi(\theta)$ & absolute discrepancy \\",
        r"\midrule",
    ]
    for theta, split, err in rows_psi:
        latex.append(f"${fmt(theta,5)}$ & ${fmt(split,18)}$ & ${fmt(err,5)}$ \\\\")
    latex += [
        r"\bottomrule", r"\end{tabular}", r"\end{table}", "",
        r"\begin{equation}",
        r"\begin{aligned}",
        r"c_0&=" + fmt(psi_c0(), 22) + r",\qquad"
        r" |c_1|=" + fmt(abs(c1), 12) + r",\\",
        r"\arg c_1&=" + fmt(mp.arg(c1), 12) + r".",
        r"\end{aligned}",
        r"\label{eq:numerical-c1}",
        r"\end{equation}",
        "",
    ]

    latex += [
        r"\begin{table}[tbp]",
        r"\centering",
        r"\caption{Internal consistency check for the explicit inverse expansion. "
        r"Here $q=\log t$ is prescribed, $x=1-K'(t)$, and $Y$ is obtained from "
        r"the exact cumulant function together with the leading saddle prefactor.}",
        r"\label{tab:inverse-check}",
        r"\begin{tabular}{@{}rlll@{}}",
        r"\toprule",
        r"$q$ & $x$ & $Y$ & $q_{\rm app}-q$ \\",
        r"\midrule",
    ]
    for q, x, Y, err in rows_inverse:
        latex.append(
            f"${fmt(q,5)}$ & ${fmt(x,10)}$ & ${fmt(Y,12)}$ & ${fmt(err,8)}$ \\\\"
        )
    latex += [r"\bottomrule", r"\end{tabular}", r"\end{table}", ""]

    (out / "numerical_results.tex").write_text("\n".join(latex), encoding="utf-8")


def make_plots(out: Path) -> None:
    """Create publication-ready diagnostic plots using Matplotlib defaults."""
    try:
        import matplotlib.pyplot as plt
    except Exception:
        return

    # Plot 1: the exact digit-sum discrepancy in the zero count.
    Ms = list(range(1, 2049))
    discrepancy = [2 * m - zero_count(m) for m in Ms]
    plt.figure(figsize=(8.0, 3.8))
    plt.plot(Ms, discrepancy, linewidth=0.8)
    plt.xlabel(r"$M$")
    plt.ylabel(r"$2M-N(2\pi M)=s_2(M)$")
    plt.tight_layout()
    plt.savefig(out / "zero_count_digit_sum.png", dpi=180)
    plt.close()

    # Plot 2: the minute but nonconstant log-periodic fluctuation.
    thetas = [i / 600 for i in range(601)]
    mean = psi_c0()
    centered = [float(psi_fourier(mp.mpf(th), 8) - mean) for th in thetas]
    plt.figure(figsize=(8.0, 3.8))
    plt.plot(thetas, centered, linewidth=1.0)
    plt.xlabel(r"$\theta$")
    plt.ylabel(r"$\Psi(\theta)-c_0$")
    plt.ticklabel_format(axis="y", style="sci", scilimits=(0, 0))
    plt.tight_layout()
    plt.savefig(out / "psi_periodic.png", dpi=180)
    plt.close()

    # Plot 3: exponential decay of the Fourier coefficients.
    ks = list(range(1, 13))
    coeffs = [float(abs(psi_ck(k))) for k in ks]
    plt.figure(figsize=(8.0, 3.8))
    plt.semilogy(ks, coeffs, marker="o")
    plt.xlabel(r"$k$")
    plt.ylabel(r"$|c_k|$")
    plt.tight_layout()
    plt.savefig(out / "psi_coefficients.png", dpi=180)
    plt.close()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, default=Path("."))
    parser.add_argument("--dps", type=int, default=80)
    args = parser.parse_args()

    args.output_dir.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = args.dps

    # Hard assertions catch the most common normalization errors.
    for M in [1, 2, 3, 7, 32, 257, 1024]:
        assert zero_count(M) == 2 * M - binary_digit_sum(M)

    # Check the two product representations at a generic complex point.
    z = mp.mpc("1.2", "0.7")
    p1 = phi_sinc_product(z)
    p2 = phi_canonical_product(z, M=40000)
    if abs(p1 - p2) > mp.mpf("2e-5"):
        raise AssertionError("canonical-product normalization check failed")

    write_tables(args.output_dir)
    make_plots(args.output_dir)

    summary = [
        "Numerical experiment summary",
        f"mpmath precision: {mp.mp.dps} decimal digits",
        f"c0 = {mp.nstr(psi_c0(), 40)}",
        f"c1 = {mp.nstr(psi_ck(1), 40)}",
        f"|c1| = {mp.nstr(abs(psi_ck(1)), 20)}",
    ]
    (args.output_dir / "numerical_summary.txt").write_text(
        "\n".join(summary) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
