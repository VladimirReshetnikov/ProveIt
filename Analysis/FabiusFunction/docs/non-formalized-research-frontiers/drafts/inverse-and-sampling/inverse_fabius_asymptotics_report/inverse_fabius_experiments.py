#!/usr/bin/env python3
"""Symbolic and numerical checks for the inverse-Fabius endpoint report.

This script is intentionally self-contained.  It performs four independent tasks:

1. Generates the universal Gaussian-contraction coefficients C_n that occur in
   the saddle-point expansion of a Bromwich integral with the CDF factor 1/z.
2. Verifies the generalized Lagrange--Bürmann formula for the first three
   inverse phase coefficients d_n.
3. Checks the exact 2-adic expansion

       B(t) = -sum_{k>=0} log(1-exp(-2^k t))
            = sum_{n>=1} ((2^(v_2(n)+1)-1)/n) exp(-n t),

   together with its Dirichlet series and Mellin-residue expansion.
4. Produces two vector PDF figures used by the accompanying LaTeX report.

No repository code is required.  Python 3.11+, SymPy, mpmath, and matplotlib
are sufficient.  All calculations are deterministic.
"""

from __future__ import annotations

import argparse
import itertools
import math
from functools import lru_cache
from pathlib import Path
from typing import Dict, Iterable, Iterator, Mapping

import mpmath as mp
import sympy as sp


L = mp.log(2)


def v2(n: int) -> int:
    """Return the 2-adic valuation of a positive integer."""
    if n <= 0:
        raise ValueError("v2 is defined here only for positive integers")
    return (n & -n).bit_length() - 1


def arithmetic_weight(n: int) -> int:
    """f(n) = 2^(v_2(n)+1)-1, the integer saddle-map weight."""
    return (1 << (v2(n) + 1)) - 1


def bose_weight(n: int) -> mp.mpf:
    """b_n = f(n)/n, the exact coefficient in the dyadic Bose tail."""
    return mp.mpf(arithmetic_weight(n)) / n



def fabius_log_laplace(t: mp.mpf, tol: mp.mpf | None = None) -> mp.mpf:
    """Evaluate K(t)=log E exp(-tX) from the defining uniform-product law."""
    if t <= 0:
        raise ValueError("t must be positive")
    if tol is None:
        tol = mp.mpf(10) ** (-(mp.mp.dps - 10))
    total = mp.mpf("0")
    for j in range(1, 10000):
        u = t / mp.power(2, j)
        # -expm1(-u) avoids catastrophic cancellation when u is tiny.
        term = mp.log(-mp.expm1(-u)) - mp.log(u)
        total += term
        if abs(term) < tol:
            return total
    raise RuntimeError("Laplace product did not converge")


def exact_laplace_decomposition(t: mp.mpf, modes: int = 12) -> mp.mpf:
    """Right side of the exact quadratic-periodic-dyadic decomposition of K(t)."""
    log_t = mp.log(t)
    return (
        -log_t**2 / (2 * L)
        + log_t / 2
        - mellin_constant()
        + psi_fourier(mp.log(t, 2), modes=modes)
        + dyadic_bose_product(t)
    )

def dyadic_bose_product(t: mp.mpf, tol: mp.mpf | None = None) -> mp.mpf:
    """Evaluate B(t) from its rapidly convergent dyadic logarithmic product."""
    if t <= 0:
        raise ValueError("t must be positive")
    if tol is None:
        tol = mp.mpf(10) ** (-(mp.mp.dps - 10))
    total = mp.mpf("0")
    k = 0
    while True:
        u = mp.power(2, k) * t
        term = -mp.log1p(-mp.exp(-u))
        total += term
        if term < tol:
            return total
        k += 1
        if k > 10000:
            raise RuntimeError("dyadic product did not converge")


def dyadic_bose_series(t: mp.mpf, n_terms: int) -> mp.mpf:
    """Evaluate the first n_terms of the exact 2-adic exponential series."""
    return mp.fsum(bose_weight(n) * mp.exp(-n * t) for n in range(1, n_terms + 1))


@lru_cache(maxsize=None)
def _psi_positive_coefficients(modes: int, dps: int) -> tuple[mp.mpc, ...]:
    """Cache expensive Gamma--zeta Fourier coefficients at a fixed precision."""
    with mp.workdps(dps):
        return tuple(
            -mp.gamma(-(2 * mp.pi * 1j * k / L))
            * mp.zeta(1 - (2 * mp.pi * 1j * k / L))
            / L
            for k in range(1, modes + 1)
        )


def psi_fourier(u: mp.mpf, modes: int = 12) -> mp.mpf:
    r"""Evaluate the repository's centered periodic Gamma--zeta correction Psi.

    Psi-hat(k) = -Gamma(-chi_k) zeta(1-chi_k) / log(2),
    chi_k = 2*pi*i*k/log(2).
    """
    total = mp.mpc("0")
    coefficients = _psi_positive_coefficients(modes, mp.mp.dps)
    for k, coefficient in enumerate(coefficients, start=1):
        wave = coefficient * mp.exp(2 * mp.pi * 1j * k * u)
        total += wave + mp.conj(wave)
    return mp.re(total)


def mellin_constant() -> mp.mpf:
    r"""Constant from the order-three pole of Gamma(s)zeta(1+s)/(1-2^{-s})."""
    gamma = mp.euler
    gamma1 = mp.stieltjes(1)
    return L / 12 + (mp.pi**2 / 12 - gamma1 - gamma**2 / 2) / L


def power_residue_coefficient(m: int) -> mp.mpf:
    r"""Coefficient of t^m from the Mellin pole at s=-m."""
    if m <= 0:
        raise ValueError("m must be positive")
    return ((-1) ** m) * mp.zeta(1 - m) / (mp.factorial(m) * (1 - mp.power(2, m)))


def mellin_small_t_approximation(t: mp.mpf, power_terms: int = 10, modes: int = 12) -> mp.mpf:
    """All-residue approximation of B(t) through O(t^(power_terms+1))."""
    r = mp.log(1 / t)
    value = r**2 / (2 * L) + r / 2 + mellin_constant()
    value -= psi_fourier(mp.log(t, 2), modes=modes)
    value += mp.fsum(power_residue_coefficient(m) * t**m for m in range(1, power_terms + 1))
    return value


def constrained_multiindices(n: int) -> Iterator[tuple[int, Dict[int, int]]]:
    """Yield (m_0, {r:m_r}) with m_0 + sum (r-2)m_r = 2n."""
    target = 2 * n
    max_r = 2 * n + 2

    def rec(r: int, remaining: int, current: Dict[int, int]) -> Iterator[tuple[int, Dict[int, int]]]:
        if r > max_r:
            yield remaining, dict(current)
            return
        weight = r - 2
        for multiplicity in range(remaining // weight + 1):
            if multiplicity:
                current[r] = multiplicity
            else:
                current.pop(r, None)
            yield from rec(r + 1, remaining - weight * multiplicity, current)
        current.pop(r, None)

    yield from rec(3, target, {})


def saddle_coefficient(n: int) -> sp.Expr:
    r"""Return the explicit constrained-partition coefficient C_n.

    rho_r denotes beta_r/beta_2.  The formula includes the CDF denominator
    (1+iZ/sqrt(beta_2))^{-1}; omitting it would generate density rather than CDF
    coefficients.
    """
    if n < 1:
        raise ValueError("n must be positive")
    rho = {r: sp.Symbol(f"rho_{r}") for r in range(3, 2 * n + 3)}
    total = sp.Integer(0)
    for m0, multiplicities in constrained_multiindices(n):
        gaussian_degree = m0 + sum(r * m for r, m in multiplicities.items())
        if gaussian_degree % 2:
            raise AssertionError("the weight constraint must force even Gaussian degree")
        sign = (-1) ** (m0 + gaussian_degree // 2)
        term = sp.Integer(sign) * sp.factorial2(gaussian_degree - 1)
        for r, multiplicity in multiplicities.items():
            term *= rho[r] ** multiplicity
            term /= sp.factorial(multiplicity) * sp.factorial(r) ** multiplicity
        total += term
    return sp.expand(total)


def logarithmic_saddle_coefficients(c_values: list[sp.Expr]) -> list[sp.Expr]:
    """Convert S=1+sum C_n x^n into log(S)=sum Lambda_n x^n."""
    x = sp.Symbol("x")
    series = 1 + sum(c * x ** (index + 1) for index, c in enumerate(c_values))
    logarithm = sp.series(sp.log(series), x, 0, len(c_values) + 1).removeO().expand()
    return [sp.expand(logarithm.coeff(x, n)) for n in range(1, len(c_values) + 1)]


def verify_lagrange_burmann() -> Mapping[str, sp.Expr]:
    """Symbolically verify d_1,d_2,d_3 from the closed coefficient extractor."""
    z, u, ell, beta, log2, csharp = sp.symbols("z u ell beta L C_sharp")
    psi0, psi1, psi2, psi3 = sp.symbols("Psi Psi1 Psi2 Psi3")
    a10, a11, a12, a20, a21 = sp.symbols("A1 A1p A1pp A2 A2p")

    # Taylor jets in the displacement variable u.  Terms beyond the displayed
    # order cannot affect d_1,d_2,d_3.
    psi = psi0 + psi1 * u + psi2 * u**2 / 2 + psi3 * u**3 / 6
    a1 = a10 + a11 * u + a12 * u**2 / 2
    a2 = a20 + a21 * u
    w = beta * z + z * u
    residual = (
        -log2 * beta**2 / 2
        + log2 * u**2 / 2
        + ell / 2
        + sp.log(1 + w) / 2
        - csharp
        - psi
        - a1 * z * (1 + w) ** (-1)
        - a2 * z**2 * (1 + w) ** (-2)
    )
    residual = sp.series(residual, z, 0, 4).removeO()
    residual = sp.series(residual, u, 0, 4).removeO().expand()
    phi = -residual / log2

    def d_closed(n: int) -> sp.Expr:
        answer = 0
        for k in range(1, n + 1):
            term = sp.expand(phi**k).coeff(z, n - k).coeff(u, k - 1) / k
            answer += term
        return sp.simplify(answer)

    d1 = d_closed(1)
    d2 = d_closed(2)
    d3 = d_closed(3)

    expected_d1 = beta**2 / 2 + (csharp + psi0 - ell / 2) / log2
    expected_d2 = (psi1 * expected_d1 + a10 - beta / 2) / log2
    expected_d3 = (
        psi1 * expected_d2
        + psi2 * expected_d1**2 / 2
        + a11 * expected_d1
        - beta * a10
        + a20
        - log2 * expected_d1**2 / 2
        - expected_d1 / 2
        + beta**2 / 4
    ) / log2

    checks = {
        "d1_difference": sp.simplify(d1 - expected_d1),
        "d2_difference": sp.simplify(d2 - expected_d2),
        "d3_difference": sp.simplify(d3 - expected_d3),
        "d1": sp.factor(d1),
        "d2": sp.factor(d2),
        "d3": sp.factor(d3),
    }
    return checks


def numerical_checks() -> list[str]:
    """Run high-precision checks and return human-readable lines."""
    mp.mp.dps = 70
    lines: list[str] = []

    # Exact Laplace decomposition and product/series identity.
    for t_text in ("0.1", "1", "3", "10"):
        t = mp.mpf(t_text)
        direct = fabius_log_laplace(t)
        decomposed = exact_laplace_decomposition(t, modes=12)
        lines.append(
            f"Exact K decomposition at t={t_text}: "
            f"abs error = {mp.nstr(abs(direct-decomposed), 12)}"
        )

    for t_text, n_terms in [("0.7", 120), ("1.5", 80), ("4", 40)]:
        t = mp.mpf(t_text)
        product = dyadic_bose_product(t)
        series = dyadic_bose_series(t, n_terms)
        lines.append(
            f"B product vs 2-adic series at t={t_text}: "
            f"abs error = {mp.nstr(abs(product-series), 12)}"
        )

    # Dirichlet identity at a non-real point in its absolute convergence half-plane.
    s = mp.mpf("2.30") + mp.mpf("0.41") * 1j
    partial = mp.fsum(bose_weight(n) / mp.power(n, s) for n in range(1, 50000))
    closed = mp.zeta(s + 1) / (1 - mp.power(2, -s))
    lines.append(
        "Dirichlet identity (50000 terms, s=2.30+0.41i): "
        f"abs error = {mp.nstr(abs(partial-closed), 12)}"
    )

    # Mellin bridge.  The error shown is after ten algebraic residues and twelve
    # positive/negative Fourier modes.
    for t_text in ["0.2", "0.1", "0.05", "0.02"]:
        t = mp.mpf(t_text)
        exact = dyadic_bose_product(t)
        approx = mellin_small_t_approximation(t, power_terms=10, modes=12)
        lines.append(
            f"Mellin bridge at t={t_text}: abs error = {mp.nstr(abs(exact-approx), 12)}"
        )

    # Coefficient bounds b_n <= 2 and the first values.
    first = [mp.nstr(bose_weight(n), 8) for n in range(1, 17)]
    lines.append("First b_n values: " + ", ".join(first))
    lines.append(f"max(b_n, 1<=n<=100000) = {mp.nstr(max(bose_weight(n) for n in range(1,100001)), 12)}")
    return lines


def make_figures(output_dir: Path) -> None:
    """Generate vector PDF plots used by the report."""
    import matplotlib.pyplot as plt
    import numpy as np

    mp.mp.dps = 50
    output_dir.mkdir(parents=True, exist_ok=True)

    # Periodic correction: scale by 10^6 so its shape is visible.
    u_values = np.linspace(0.0, 1.0, 401)
    psi_values = np.array([float(1e6 * psi_fourier(mp.mpf(str(u)), modes=10)) for u in u_values])
    fig = plt.figure(figsize=(7.1, 3.5))
    ax = fig.add_subplot(111)
    ax.plot(u_values, psi_values)
    ax.set_xlabel(r"phase $u$")
    ax.set_ylabel(r"$10^6\,\Psi(u)$")
    ax.set_title("Gamma--zeta periodic correction")
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(output_dir / "psi_periodic.pdf", bbox_inches="tight")
    plt.close(fig)

    # Large-t convergence of the exact exponential expansion.
    t_values = np.linspace(0.8, 6.0, 180)
    exact_values = [dyadic_bose_product(mp.mpf(str(t))) for t in t_values]
    fig = plt.figure(figsize=(7.1, 3.8))
    ax = fig.add_subplot(111)
    for n_terms in (1, 2, 4, 8):
        errors = []
        for t, exact in zip(t_values, exact_values):
            approx = dyadic_bose_series(mp.mpf(str(t)), n_terms)
            errors.append(float(abs(exact - approx) / exact))
        ax.semilogy(t_values, errors, label=f"N={n_terms}")
    ax.set_xlabel(r"$t$")
    ax.set_ylabel("relative truncation error")
    ax.set_title(r"Exact 2-adic exponential tail $B(t)$")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(output_dir / "dyadic_tail_convergence.pdf", bbox_inches="tight")
    plt.close(fig)


def write_generated_tex(output_dir: Path, c_values: list[sp.Expr], lambda_values: list[sp.Expr]) -> None:
    """Write machine-generated coefficient snippets for archival inspection."""
    lines = [
        "% Generated by inverse_fabius_experiments.py; do not edit by hand.",
        "\\begin{align*}",
    ]
    for index, value in enumerate(c_values, start=1):
        suffix = r"\\" if index != len(c_values) else ""
        lines.append(f"C_{{{index}}}&={sp.latex(value)}{suffix}")
    lines.extend(["\\end{align*}", "", "\\begin{align*}"])
    for index, value in enumerate(lambda_values, start=1):
        suffix = r"\\" if index != len(lambda_values) else ""
        lines.append(f"\\Lambda_{{{index}}}&={sp.latex(value)}{suffix}")
    lines.append("\\end{align*}")
    (output_dir / "generated_coefficients.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory for figures and generated text",
    )
    parser.add_argument("--max-saddle-order", type=int, default=3)
    parser.add_argument("--no-figures", action="store_true")
    args = parser.parse_args()

    args.output_dir.mkdir(parents=True, exist_ok=True)

    c_values = [saddle_coefficient(n) for n in range(1, args.max_saddle_order + 1)]
    lambda_values = logarithmic_saddle_coefficients(c_values)
    write_generated_tex(args.output_dir, c_values, lambda_values)

    checks = verify_lagrange_burmann()
    if any(checks[name] != 0 for name in ("d1_difference", "d2_difference", "d3_difference")):
        raise AssertionError("generalized Lagrange--Bürmann verification failed")

    report_lines = [
        "Universal saddle coefficients:",
        *[f"C_{n} = {sp.sstr(value)}" for n, value in enumerate(c_values, start=1)],
        "",
        "Logarithmic saddle coefficients:",
        *[f"Lambda_{n} = {sp.sstr(value)}" for n, value in enumerate(lambda_values, start=1)],
        "",
        "Lagrange--Bürmann symbolic differences:",
        *[f"{name} = {sp.sstr(checks[name])}" for name in ("d1_difference", "d2_difference", "d3_difference")],
        "",
        "High-precision numerical checks:",
        *numerical_checks(),
    ]
    text = "\n".join(report_lines) + "\n"
    (args.output_dir / "verification_output.txt").write_text(text, encoding="utf-8")
    print(text)

    if not args.no_figures:
        make_figures(args.output_dir)


if __name__ == "__main__":
    main()
