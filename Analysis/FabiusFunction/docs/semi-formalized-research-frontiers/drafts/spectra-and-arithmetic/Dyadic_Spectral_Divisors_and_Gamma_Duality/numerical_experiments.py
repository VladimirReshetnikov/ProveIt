#!/usr/bin/env python3
"""Exact and high-precision experiments for the Fabius/Rvachev frontier report.

The report studies the Fourier transform

    Phi(xi) = prod_{j>=0} sinc(pi*xi/2^j)

of Rvachev's up-density, its reciprocal-integer-base analogues, and the
normalized root transform

    A_b(z) = prod_{m>=1} (1 + z/(pi^2 m^2))^(1+nu_b(m)).

This script reproduces all numerical tables and figures in the report:

* exact rational moment coefficients from a Bernoulli/zeta Newton recurrence;
* Jensen-polynomial root checks;
* the arithmetic heat trace and its log-periodic Mellin expansion;
* the exact Jacobi-theta beyond-all-orders remainder;
* the exact modular-dual representation of log A_b(z).

SymPy is used for exact rational arithmetic, mpmath for high precision, and
matplotlib for the figures.  The script has no network dependency.
"""

from __future__ import annotations

import argparse
import math
from functools import lru_cache
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
import sympy as sp

ROOT = Path(__file__).resolve().parent
FIG_DIR = ROOT / "figures"
GEN_DIR = ROOT / "generated"


def nu_b(n: int, b: int) -> int:
    """Whole-base valuation max{k: b^k divides n}; n>=1, b>=2."""
    if n < 1 or b < 2:
        raise ValueError("nu_b requires n>=1 and b>=2")
    value = 0
    while n % b == 0:
        n //= b
        value += 1
    return value


def p_exact(r: int, b: int = 2) -> sp.Rational:
    r"""Exact spectral power sum

        p_r(b)=zeta(2r)/(pi^(2r)(1-b^(-2r)))
              =sum_{m>=1}(1+nu_b(m))/(pi^(2r)m^(2r)).
    """
    expr = sp.zeta(2 * r) / (sp.pi ** (2 * r) * (1 - sp.Rational(1, b ** (2 * r))))
    return sp.Rational(sp.simplify(expr))


def coefficients(n_max: int, b: int = 2) -> list[sp.Rational]:
    r"""Return a_0,...,a_nmax for A_b(z)=sum a_n z^n.

    Differentiating log A_b gives the exact Newton recurrence

        n a_n = sum_{r=1}^n (-1)^(r-1) p_r(b) a_{n-r}.
    """
    a: list[sp.Rational] = [sp.Rational(1)]
    for n in range(1, n_max + 1):
        rhs = sum((-1) ** (r - 1) * p_exact(r, b) * a[n - r] for r in range(1, n + 1))
        a.append(sp.Rational(sp.simplify(rhs / n)))
    return a


def dyadic_moments(a: Sequence[sp.Rational]) -> list[sp.Rational]:
    r"""For b=2, recover mu_{2n}=E[X^(2n)] from a_n=4^n mu_{2n}/(2n)! ."""
    return [sp.Rational(sp.simplify(an * sp.factorial(2 * n) / 4**n)) for n, an in enumerate(a)]


def jensen_poly(a: Sequence[sp.Rational], degree: int, shift: int) -> sp.Poly:
    r"""J_{d,n}(x)=sum_{j=0}^d binom(d,j) gamma_{n+j} x^j, gamma_k=k!a_k."""
    x = sp.Symbol("x")
    expr = sum(
        sp.binomial(degree, j) * sp.factorial(shift + j) * a[shift + j] * x**j
        for j in range(degree + 1)
    )
    return sp.Poly(sp.expand(expr), x, domain=sp.QQ)


def jensen_diagnostics(a: Sequence[sp.Rational]) -> list[tuple[int, int, float, float, float]]:
    rows: list[tuple[int, int, float, float, float]] = []
    for degree in (2, 4, 6, 8, 10):
        for shift in (0, 3, 6):
            roots = jensen_poly(a, degree, shift).nroots(n=70, maxsteps=400)
            c_roots = [complex(sp.N(root, 30)) for root in roots]
            rows.append(
                (
                    degree,
                    shift,
                    max(abs(root.imag) for root in c_roots),
                    max(root.real for root in c_roots),
                    min(root.real for root in c_roots),
                )
            )
    return rows


def theta_direct(x: mp.mpf, b: int, tolerance: mp.mpf = mp.mpf("1e-65")) -> mp.mpf:
    r"""Direct Gaussian sum Theta_b(x)=sum (1+nu_b(m)) exp(-pi^2m^2x)."""
    cutoff = int(mp.ceil(mp.sqrt(-mp.log(tolerance) / (mp.pi**2 * x))))
    return mp.fsum((1 + nu_b(m, b)) * mp.exp(-mp.pi**2 * m * m * x) for m in range(1, cutoff + 1))


@lru_cache(maxsize=None)
def c_heat(k: int, b: int) -> mp.mpc:
    r"""Fourier coefficient of the log-periodic heat correction."""
    L = mp.log(b)
    s = mp.j * mp.pi * k / L
    return mp.gamma(s) * mp.pi ** (-2 * s) * mp.zeta(2 * s) / (2 * L)


def P_heat(u: mp.mpf, b: int, k_max: int = 45) -> mp.mpf:
    return 2 * mp.re(
        mp.fsum(c_heat(k, b) * mp.exp(2 * mp.pi * mp.j * k * u) for k in range(1, k_max + 1))
    )


def heat_skeleton(x: mp.mpf, b: int, k_max: int = 45) -> mp.mpf:
    r"""Algebraic/log-periodic part H_b(x) of the exact heat decomposition."""
    L = mp.log(b)
    u = mp.log(1 / x) / (2 * L)
    return (
        b / (2 * (b - 1) * mp.sqrt(mp.pi * x))
        - mp.log(1 / x) / (4 * L)
        - mp.mpf(1) / 4
        + (mp.euler - 2 * mp.log(2)) / (4 * L)
        + P_heat(u, b, k_max)
    )


def heat_dual_remainder(x: mp.mpf, b: int, tolerance: mp.mpf = mp.mpf("1e-65")) -> mp.mpf:
    r"""Exact negative remainder R_b(x)=Theta_b(x)-H_b(x).

    Jacobi inversion gives

      R_b(x)=-1/sqrt(pi*x) sum_{j>=1} b^j sum_{n>=1} exp(-b^(2j)n^2/x).
    """
    total = mp.mpf("0")
    j = 1
    while True:
        scale = b**j
        first = mp.exp(-(scale * scale) / x)
        if j > 2 and scale * first / mp.sqrt(mp.pi * x) < tolerance:
            break
        inner = mp.fsum(mp.exp(-(scale * scale) * n * n / x) for n in range(1, int(mp.sqrt(-mp.log(tolerance) * x / (scale * scale))) + 2))
        total += scale * inner
        j += 1
        if j > 1000:
            raise RuntimeError("heat dual sum failed to converge")
    return -total / mp.sqrt(mp.pi * x)


def log_A_direct(z: mp.mpf, b: int, tolerance: mp.mpf = mp.mpf("1e-65")) -> mp.mpf:
    r"""Direct scale-product evaluation of log A_b(z), z>0."""
    root = mp.sqrt(z)
    total = mp.mpf("0")
    for j in range(10000):
        y = root / (b**j)
        term = mp.log(mp.sinh(y) / y)
        total += term
        if j > 12 and abs(term) < tolerance:
            return total
    raise RuntimeError("log A scale product failed to converge")


def Q_large(v: mp.mpf, b: int, k_max: int = 45) -> mp.mpf:
    r"""Periodic term in the exact modular-dual formula for log A_b."""
    L = mp.log(b)
    return 2 * mp.re(
        mp.fsum(
            -c_heat(k, b)
            * mp.gamma(-mp.j * mp.pi * k / L)
            * mp.exp(2 * mp.pi * mp.j * k * v)
            for k in range(1, k_max + 1)
        )
    )


def dual_partition_log(z: mp.mpf, b: int, tolerance: mp.mpf = mp.mpf("1e-65")) -> mp.mpf:
    r"""-sum_{j>=1} log(1-exp(-2b^j sqrt(z)))."""
    root = mp.sqrt(z)
    total = mp.mpf("0")
    for j in range(1, 10000):
        q = mp.exp(-2 * (b**j) * root)
        term = -mp.log1p(-q)
        total += term
        if j > 4 and abs(term) < tolerance:
            return total
    raise RuntimeError("dual partition product failed to converge")


@lru_cache(maxsize=None)
def C_large(b: int) -> mp.mpf:
    r"""Constant C_b fixed by the modular-dual identity at z=1."""
    return log_A_direct(mp.mpf(1), b) - b / (b - 1) - Q_large(mp.mpf(0), b, 55) - dual_partition_log(mp.mpf(1), b)


def log_A_dual(z: mp.mpf, b: int, k_max: int = 55) -> mp.mpf:
    r"""Exact modular-dual representation of log A_b(z), z>0."""
    L = mp.log(b)
    lz = mp.log(z)
    return (
        b / (b - 1) * mp.sqrt(z)
        - lz**2 / (8 * L)
        - (mp.mpf(1) / 4 + mp.log(2) / (2 * L)) * lz
        + C_large(b)
        + Q_large(lz / (2 * L), b, k_max)
        + dual_partition_log(z, b)
    )


def write_tables(a: Sequence[sp.Rational], mu: Sequence[sp.Rational], diagnostics: Sequence[tuple[int, int, float, float, float]]) -> None:
    # Exact moments.
    lines = [
        r"\begin{tabular}{@{}rlll@{}}", r"\toprule",
        r"$n$ & $a_n=4^n\mu_{2n}/(2n)!$ & $\mu_{2n}$ & decimal $\mu_{2n}$ \\", r"\midrule",
    ]
    for n in range(8):
        lines.append(f"{n} & $\\displaystyle {sp.latex(a[n])}$ & $\\displaystyle {sp.latex(mu[n])}$ & {sp.N(mu[n], 12)} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (GEN_DIR / "moment_table.tex").write_text("\n".join(lines) + "\n")

    # Jensen roots.
    lines = [
        r"\begin{tabular}{@{}rrrrr@{}}", r"\toprule",
        r"degree & shift & max. $|\Im\rho|$ & nearest root to $0$ & leftmost root \\", r"\midrule",
    ]
    for d, n, im, near, left in diagnostics:
        lines.append(f"{d} & {n} & {im:.2e} & {near:.6g} & {left:.6g} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (GEN_DIR / "jensen_table.tex").write_text("\n".join(lines) + "\n")

    # Heat decomposition.
    lines = [
        r"\begin{tabular}{@{}rrllll@{}}", r"\toprule",
        r"$b$ & $x$ & direct $\Theta_b$ & skeleton $\mathcal H_b$ & dual remainder & closure error \\", r"\midrule",
    ]
    for b in (2, 3):
        for exponent in (2, 4, 6):
            x = mp.mpf(10) ** (-exponent)
            direct = theta_direct(x, b)
            skeleton = heat_skeleton(x, b, 55)
            remainder = heat_dual_remainder(x, b)
            error = abs(direct - skeleton - remainder)
            lines.append(
                f"{b} & $10^{{-{exponent}}}$ & {mp.nstr(direct, 13)} & {mp.nstr(skeleton, 13)} & {mp.nstr(remainder, 4)} & {mp.nstr(error, 3)} \\\\"
            )
    lines += [r"\bottomrule", r"\end{tabular}"]
    (GEN_DIR / "heat_validation_table.tex").write_text("\n".join(lines) + "\n")

    # Periodic coefficients.
    lines = [r"\begin{tabular}{@{}rrll@{}}", r"\toprule", r"$b$ & $k$ & $|c_{b,k}|$ & $\arg c_{b,k}$ \\", r"\midrule"]
    for b in (2, 3, 4):
        for k in (1, 2, 3):
            c = c_heat(k, b)
            lines.append(f"{b} & {k} & {mp.nstr(abs(c), 12)} & {mp.nstr(mp.arg(c), 10)} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (GEN_DIR / "heat_coefficients_table.tex").write_text("\n".join(lines) + "\n")

    # Modular-dual identity.
    lines = [
        r"\begin{tabular}{@{}rrlll@{}}", r"\toprule",
        r"$b$ & $z$ & direct $\log A_b(z)$ & modular-dual formula & absolute error \\", r"\midrule",
    ]
    for b in (2, 3):
        for z0 in (1, 10, 100, 1000):
            z = mp.mpf(z0)
            direct, dual = log_A_direct(z, b), log_A_dual(z, b)
            lines.append(f"{b} & {z0} & {mp.nstr(direct, 14)} & {mp.nstr(dual, 14)} & {mp.nstr(abs(direct-dual), 3)} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (GEN_DIR / "large_z_identity_table.tex").write_text("\n".join(lines) + "\n")

    lines = [r"\begin{tabular}{@{}rl@{}}", r"\toprule", r"$b$ & $C_b$ \\", r"\midrule"]
    for b in (2, 3, 4, 5):
        lines.append(f"{b} & {mp.nstr(C_large(b), 22)} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (GEN_DIR / "large_z_constants_table.tex").write_text("\n".join(lines) + "\n")


def make_figures(a: Sequence[sp.Rational]) -> None:
    # One full dyadic log-period: direct heat trace versus residue Fourier sum.
    phase = np.linspace(0.0, 1.0, 121)
    b, M = 2, 6
    L = mp.log(b)
    const = -mp.mpf(1) / 4 + (mp.euler - 2 * mp.log(2)) / (4 * L)
    direct_y, periodic_y = [], []
    for u0 in phase:
        u = mp.mpf(str(u0))
        x = mp.power(b, -2 * (M + u))
        theta = theta_direct(x, b, mp.mpf("1e-50"))
        detrended = theta - b / (2 * (b - 1) * mp.sqrt(mp.pi * x)) + mp.log(1 / x) / (4 * L) - const
        direct_y.append(float(detrended))
        periodic_y.append(float(P_heat(u, b, 40)))
    plt.figure(figsize=(7.2, 4.2))
    plt.plot(phase, direct_y, label="direct detrended heat trace")
    plt.plot(phase, periodic_y, "--", label="Fourier residue series")
    plt.xlabel(r"phase $u=\log(1/x)/(2\log 2)$ modulo $1$")
    plt.ylabel("periodic correction")
    plt.title("Dyadic heat trace: log-periodic correction")
    plt.legend(); plt.tight_layout()
    plt.savefig(FIG_DIR / "heat_trace_periodic_b2.pdf")
    plt.savefig(FIG_DIR / "heat_trace_periodic_b2.png", dpi=180)
    plt.close()

    # Exact exponential scale of the Jacobi-dual remainder.
    plt.figure(figsize=(7.2, 4.2))
    for b in (2, 3):
        xs = np.linspace(0.08 if b == 2 else 0.14, 0.32 if b == 2 else 0.45, 28)
        ys = []
        for x0 in xs:
            x = mp.mpf(str(x0))
            residual = abs(theta_direct(x, b, mp.mpf("1e-60")) - heat_skeleton(x, b, 55))
            ys.append(float(-x * mp.log(residual)))
        plt.plot(xs, ys, label=rf"$b={b}$")
        plt.axhline(b * b, linestyle="--", linewidth=0.9)
    plt.xlabel(r"$x$"); plt.ylabel(r"$-x\log|R_b(x)|$")
    plt.title(r"Beyond-all-orders remainder: first scale $e^{-b^2/x}$")
    plt.legend(); plt.tight_layout()
    plt.savefig(FIG_DIR / "heat_trace_remainder_scale.pdf")
    plt.savefig(FIG_DIR / "heat_trace_remainder_scale.png", dpi=180)
    plt.close()

    # Selected Jensen roots, displayed on a symmetric logarithmic coordinate.
    plt.figure(figsize=(7.2, 4.2))
    for row, d in enumerate((4, 6, 8, 10)):
        roots = [complex(sp.N(root, 35)) for root in jensen_poly(a, d, 4).nroots(n=65, maxsteps=400)]
        roots = sorted(root.real for root in roots)
        xcoords = [math.copysign(math.log10(1 + abs(root)), root) for root in roots]
        plt.scatter(xcoords, [row] * len(xcoords))
    plt.yticks(range(4), [r"$d=4$", r"$d=6$", r"$d=8$", r"$d=10$"])
    plt.xlabel(r"signed $\log_{10}(1+|\rho|)$; every root is negative")
    plt.title(r"Roots of Jensen polynomials $J_{d,4}$")
    plt.tight_layout()
    plt.savefig(FIG_DIR / "jensen_roots.pdf")
    plt.savefig(FIG_DIR / "jensen_roots.png", dpi=180)
    plt.close()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=75)
    parser.add_argument("--moments", type=int, default=28)
    args = parser.parse_args()
    mp.mp.dps = args.precision
    FIG_DIR.mkdir(exist_ok=True); GEN_DIR.mkdir(exist_ok=True)

    a = coefficients(max(args.moments, 20), 2)
    mu = dyadic_moments(a)
    diagnostics = jensen_diagnostics(a)
    write_tables(a, mu, diagnostics)
    make_figures(a)

    summary = [
        "Exact dyadic moment data", "=" * 50,
        *[f"n={n}: a_n={a[n]}, mu_{{2n}}={mu[n]}" for n in range(10)],
        "", "Modular-dual constants", "=" * 50,
        *[f"b={b}: C_b={mp.nstr(C_large(b), 35)}" for b in (2, 3, 4, 5)],
        "", f"maximum Jensen root imaginary part: {max(row[2] for row in diagnostics)}",
    ]
    (GEN_DIR / "experiment_summary.txt").write_text("\n".join(summary) + "\n")
    print("Generated tables and figures in", ROOT)
    print("Maximum Jensen root imaginary part:", max(row[2] for row in diagnostics))


if __name__ == "__main__":
    main()
