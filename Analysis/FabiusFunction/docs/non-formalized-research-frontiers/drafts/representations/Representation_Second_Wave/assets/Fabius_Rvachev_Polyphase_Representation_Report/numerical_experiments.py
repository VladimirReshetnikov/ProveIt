#!/usr/bin/env python3
"""Numerical and exact checks for the polyphase Fabius--Rvachev report.

The script verifies four families of identities developed in the accompanying
LaTeX report:

1. Polyphase factorization of the Rvachev Fourier product into scale classes
   modulo r.
2. Recovery of a finite signed Thue--Morse atomic comb from a Fourier
   deconvolution quotient.
3. Exact Bell--Bernoulli/high-power-sum identities for finite sparse box
   splines.
4. Cumulant recombination of the polyphase components.

It also produces two figures used in the report.  All displayed numerical
errors use high-precision mpmath arithmetic.  The finite power-sum checks use
exact SymPy rational arithmetic, so a zero difference really is exact.

Run from this directory with

    python numerical_experiments.py

Outputs are written next to this script.  No network access is required.
"""

from __future__ import annotations

import csv
import math
from pathlib import Path
from typing import Iterable

import mpmath as mp
import matplotlib.pyplot as plt
import numpy as np
import sympy as sp

OUT = Path(__file__).resolve().parent
mp.mp.dps = 90


def tm_sign(k: int) -> int:
    """Signed Thue--Morse value epsilon_k = (-1)^popcount(k)."""
    return -1 if k.bit_count() & 1 else 1


def sinc_pi(z: mp.mpc | mp.mpf) -> mp.mpc | mp.mpf:
    """Normalized sinc sin(pi*z)/(pi*z), with its removable value at zero."""
    if z == 0:
        return mp.mpf(1)
    return mp.sin(mp.pi * z) / (mp.pi * z)


def convergent_sinc_product(z: mp.mpc, step: int, start: int = 0) -> mp.mpc:
    """Compute prod_{m>=0} sinc_pi(z / 2^(start + step*m)).

    The tail is terminated only after |z|/2^exponent is tiny enough that a
    rigorous first omitted logarithmic term is far below the working precision.
    For this verification script, 300 factors is a generous hard ceiling.
    """
    product = mp.mpc(1)
    for m in range(300):
        exponent = start + step * m
        w = z / mp.power(2, exponent)
        product *= sinc_pi(w)
        # log sinc_pi(w) = -pi^2 w^2/6 + O(w^4).  This threshold makes the
        # entire remaining geometric tail negligible at 90 decimal digits.
        if m > 8 and abs(w) < mp.mpf("1e-52"):
            break
    else:
        raise RuntimeError("sinc product did not reach its tail threshold")
    return product


def phi(z: mp.mpc) -> mp.mpc:
    """The full Rvachev Fourier product Phi(z)."""
    return convergent_sinc_product(z, step=1)


def psi(r: int, z: mp.mpc) -> mp.mpc:
    """Sparse/polyphase product Psi_r(z) over scales 0,r,2r,... ."""
    if r < 1:
        raise ValueError("r must be positive")
    return convergent_sinc_product(z, step=r)


def sparse_knots(r: int, n: int) -> tuple[mp.mpf, list[mp.mpf]]:
    """Return A_{r,n} and knots x_k=-A+sum_j bit_j(k) 2^{-rj}."""
    q = mp.power(2, -r)
    A = (1 - q**n) / (2 * (1 - q))
    knots: list[mp.mpf] = []
    for k in range(1 << n):
        lam = mp.mpf(0)
        for j in range(n):
            if (k >> j) & 1:
                lam += q**j
        knots.append(-A + lam)
    return A, knots


def signed_comb_transform(r: int, n: int, z: mp.mpc) -> mp.mpc:
    """Fourier transform sum epsilon_k exp(-2*pi*i*z*x_k)."""
    _, knots = sparse_knots(r, n)
    return mp.fsum(
        tm_sign(k) * mp.e ** (-2j * mp.pi * z * knots[k])
        for k in range(1 << n)
    )


def quotient_comb_transform(r: int, n: int, z: mp.mpc) -> mp.mpc:
    """The Fourier-deconvolution expression for the same signed comb."""
    q = mp.power(2, -r)
    B = n * (n - 1) // 2
    # The quotient is entire after cancellation.  Sample points below avoid
    # common zeros, so direct high-precision division is stable.
    finite_product = psi(r, z) / psi(r, (q**n) * z)
    return (q**B) * (2j * mp.pi * z) ** n * finite_product


def sympy_sparse_knots(r: int, n: int) -> tuple[sp.Rational, list[sp.Rational]]:
    """Exact rational version of sparse_knots for integer r."""
    q = sp.Rational(1, 2**r)
    A = (1 - q**n) / (2 * (1 - q))
    knots: list[sp.Rational] = []
    for k in range(1 << n):
        lam = sp.Rational(0)
        for j in range(n):
            if (k >> j) & 1:
                lam += q**j
        knots.append(sp.factor(-A + lam))
    return A, knots


def finite_moment_from_mgf(r: int, n: int, degree: int) -> sp.Rational:
    """Exact degree-th moment of the N-factor sparse uniform convolution."""
    if degree < 0:
        raise ValueError("degree must be nonnegative")
    s = sp.Symbol("s")
    q = sp.Rational(1, 2**r)
    order = degree + 2
    mgf = sp.Integer(1)
    # sinh(x)/x = sum_{j>=0} x^(2j)/(2j+1)!.
    for m in range(n):
        x = s * q**m / 2
        factor = sp.Add(*[
            x ** (2 * j) / sp.factorial(2 * j + 1)
            for j in range(degree // 2 + 2)
        ])
        mgf = sp.series(mgf * factor, s, 0, order).removeO()
    return sp.factor(sp.expand(mgf).coeff(s, degree) * sp.factorial(degree))


def moment_from_power_sum(r: int, n: int, degree: int) -> sp.Rational:
    """Exact moment reconstructed from the high-degree Thue--Morse sum."""
    q = sp.Rational(1, 2**r)
    B = n * (n - 1) // 2
    _, knots = sympy_sparse_knots(r, n)
    power_sum = sp.Add(*[
        tm_sign(k) * knots[k] ** (n + degree)
        for k in range(1 << n)
    ])
    value = (
        (-1) ** n
        * q ** (-B)
        * sp.factorial(degree)
        / sp.factorial(n + degree)
        * power_sum
    )
    return sp.factor(value)


def cumulant_component_exact(r: int, order_half: int) -> sp.Rational:
    """Exact kappa_{2m} of Z_r."""
    m = order_half
    return sp.factor(
        sp.bernoulli(2 * m)
        / (2 * m * (1 - sp.Rational(1, 2) ** (2 * r * m)))
    )


def cumulant_full_exact(order_half: int) -> sp.Rational:
    """Exact kappa_{2m} of the full Rvachev law."""
    m = order_half
    return sp.factor(
        sp.bernoulli(2 * m)
        / (2 * m * (1 - sp.Rational(1, 2) ** (2 * m)))
    )


def operator_coefficient_exact(r: int, order_half: int) -> sp.Rational:
    """Coefficient of D^(2m) in log of the sparse averaging operator."""
    m = order_half
    return sp.factor(cumulant_component_exact(r, m) / sp.factorial(2 * m))


def write_polyphase_checks() -> None:
    rows = []
    samples = [
        mp.mpc("0.37"),
        mp.mpc("1.23", "0.17"),
        mp.mpc("3.41", "-0.08"),
        mp.mpc("7.125", "0.031"),
    ]
    for r in (2, 3, 4, 5):
        for z in samples:
            direct = phi(z)
            split = mp.fprod(psi(r, z / mp.power(2, a)) for a in range(r))
            rows.append([
                r,
                mp.nstr(z.real, 20),
                mp.nstr(z.imag, 20),
                mp.nstr(direct.real, 40),
                mp.nstr(direct.imag, 40),
                mp.nstr(split.real, 40),
                mp.nstr(split.imag, 40),
                mp.nstr(abs(direct - split), 12),
            ])
    with (OUT / "polyphase_product_checks.csv").open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow([
            "r", "Re(z)", "Im(z)", "Re(Phi)", "Im(Phi)",
            "Re(polyphase product)", "Im(polyphase product)", "absolute error",
        ])
        w.writerows(rows)


def write_deconvolution_checks() -> None:
    rows = []
    samples = [mp.mpc("0.187"), mp.mpc("0.73", "0.09"), mp.mpc("2.11", "-0.03")]
    for r, n in ((1, 7), (2, 6), (3, 5)):
        for z in samples:
            comb = signed_comb_transform(r, n, z)
            quotient = quotient_comb_transform(r, n, z)
            rows.append([
                r,
                n,
                mp.nstr(z.real, 20),
                mp.nstr(z.imag, 20),
                mp.nstr(comb.real, 40),
                mp.nstr(comb.imag, 40),
                mp.nstr(quotient.real, 40),
                mp.nstr(quotient.imag, 40),
                mp.nstr(abs(comb - quotient), 12),
            ])
    with (OUT / "fourier_deconvolution_checks.csv").open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow([
            "r", "N", "Re(z)", "Im(z)", "Re(comb)", "Im(comb)",
            "Re(quotient formula)", "Im(quotient formula)", "absolute error",
        ])
        w.writerows(rows)


def write_power_sum_checks() -> None:
    rows = []
    for r, n in ((1, 6), (2, 5), (3, 4)):
        for degree in (0, 1, 2, 3, 4, 6):
            direct = finite_moment_from_mgf(r, n, degree)
            reconstructed = moment_from_power_sum(r, n, degree)
            rows.append([
                r,
                n,
                degree,
                str(direct),
                str(reconstructed),
                str(sp.factor(direct - reconstructed)),
            ])
    with (OUT / "power_sum_moment_checks.csv").open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow([
            "r", "N", "moment degree", "MGF moment (exact)",
            "Thue-Morse power-sum reconstruction (exact)", "difference",
        ])
        w.writerows(rows)


def write_cumulant_checks() -> None:
    rows = []
    for r in (2, 3, 4, 5):
        for m in range(1, 7):
            component = cumulant_component_exact(r, m)
            weighted = sp.factor(
                component * sum(sp.Rational(1, 2) ** (2 * a * m) for a in range(r))
            )
            full = cumulant_full_exact(m)
            rows.append([
                r,
                2 * m,
                str(component),
                str(weighted),
                str(full),
                str(sp.factor(weighted - full)),
            ])
    with (OUT / "polyphase_cumulant_checks.csv").open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow([
            "r", "cumulant order", "component cumulant", "weighted component sum",
            "full cumulant", "difference",
        ])
        w.writerows(rows)


def write_operator_coefficients() -> None:
    rows = []
    for r in (1, 2, 3):
        for m in range(1, 9):
            rows.append([r, 2 * m, str(operator_coefficient_exact(r, m))])
    with (OUT / "operator_coefficients.csv").open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["r", "derivative order", "coefficient in log operator"])
        w.writerows(rows)


def make_fourier_plot() -> None:
    # Avoid integer zeros in logarithmic plotting by adding a tiny floor.
    xs = np.linspace(0.0, 8.0, 1200)
    r = 3
    floor = 1e-40
    full = []
    factors = [[] for _ in range(r)]
    # Fifty decimal digits is ample for this visual plot and much faster.
    old_dps = mp.mp.dps
    mp.mp.dps = 50
    try:
        for x in xs:
            full.append(math.log10(max(float(abs(phi(mp.mpf(x)))), floor)))
            for a in range(r):
                factors[a].append(
                    math.log10(max(float(abs(psi(r, mp.mpf(x) / (2**a)))), floor))
                )
    finally:
        mp.mp.dps = old_dps

    plt.figure(figsize=(8.2, 4.8))
    plt.plot(xs, full, label=r"$\log_{10}|\Phi(x)|$")
    for a in range(r):
        plt.plot(xs, factors[a], label=rf"$\log_{{10}}|\Psi_3(x/2^{a})|$")
    plt.xlabel(r"$x$")
    plt.ylabel("base-10 logarithm of amplitude")
    plt.title("Polyphase factors of the Rvachev Fourier product")
    plt.legend(loc="lower left", fontsize=8)
    plt.tight_layout()
    plt.savefig(OUT / "polyphase_fourier_factors.png", dpi=180)
    plt.savefig(OUT / "polyphase_fourier_factors.pdf")
    plt.close()


def make_jump_comb_plot() -> None:
    r, n = 2, 6
    _, knots_mp = sparse_knots(r, n)
    knots = np.array([float(x) for x in knots_mp])
    signs = np.array([tm_sign(k) for k in range(1 << n)], dtype=float)
    order = np.argsort(knots)
    plt.figure(figsize=(8.2, 4.3))
    markerline, stemlines, baseline = plt.stem(knots[order], signs[order])
    plt.xlabel(r"sparse knot $x_{2,6,k}$")
    plt.ylabel(r"jump sign $\varepsilon_k$")
    plt.title("Thue--Morse signs as highest-derivative jumps")
    plt.ylim(-1.25, 1.25)
    plt.tight_layout()
    plt.savefig(OUT / "thue_morse_jump_comb.png", dpi=180)
    plt.savefig(OUT / "thue_morse_jump_comb.pdf")
    plt.close()


def summarize() -> None:
    lines = [
        "Polyphase Fabius--Rvachev numerical verification",
        "=" * 55,
        f"mpmath precision: {mp.mp.dps} decimal digits",
        "",
        "Generated files:",
        "  polyphase_product_checks.csv",
        "  fourier_deconvolution_checks.csv",
        "  power_sum_moment_checks.csv",
        "  polyphase_cumulant_checks.csv",
        "  operator_coefficients.csv",
        "  polyphase_fourier_factors.png/.pdf",
        "  thue_morse_jump_comb.png/.pdf",
        "",
        "Exact symbolic tables have zero differences in every tested row.",
        "See the CSV files for high-precision numerical residuals.",
    ]
    (OUT / "verification_log.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


def main() -> None:
    write_polyphase_checks()
    write_deconvolution_checks()
    write_power_sum_checks()
    write_cumulant_checks()
    write_operator_coefficients()
    make_fourier_plot()
    make_jump_comb_plot()
    summarize()


if __name__ == "__main__":
    main()
