#!/usr/bin/env python3
"""Exact and numerical experiments for the Legendre--Rvachev closed loop.

This script is intentionally self-contained and works without network access.
It has four independent layers:

1. exact rational arithmetic for moments of Rvachev's up distribution,
   reciprocal-MGF coefficients, Legendre coefficients, and the deconvolved
   Legendre polynomials Q_n = M_up(D)^{-1} P_n;
2. exact rational polynomial integration for the clipped affine Legendre
   connection coefficients C_{m,r}(c) and the spectral closure constants
   T_{m,l,r}^{(M)};
3. high-precision evaluation of Legendre coefficients through degree 200,
   resolving the severe cancellation in their finite moment formula;
4. an independent inverse-FFT evaluation of the infinite sinc product, used
   only to check the finite shifted-up synthesis numerically.

Generated files are written next to this script.  They are reproducible with
Python 3.11+ and the packages listed in README.txt.
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
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent


# ---------------------------------------------------------------------------
# Exact rational scalar sequences
# ---------------------------------------------------------------------------

def up_even_moments_exact(max_m: int) -> list[Fraction]:
    """Return [mu_0, mu_2, ..., mu_{2 max_m}] exactly.

    If Z has density up, then Z = (V + Z')/2 in distribution, where V is
    uniform on [-1,1] and Z' is an independent copy.  Comparing 2m-th moments
    gives

      (4^m - 1) mu_{2m}
        = sum_{r=1}^m binom(2m,2r) mu_{2m-2r}/(2r+1).
    """
    mu = [Fraction(1)]
    for m in range(1, max_m + 1):
        rhs = sum(
            Fraction(math.comb(2 * m, 2 * r), 2 * r + 1) * mu[m - r]
            for r in range(1, m + 1)
        )
        mu.append(rhs / (4**m - 1))
    return mu


def reciprocal_mgf_even_coefficients(
    max_m: int, mu_even: Sequence[Fraction]
) -> list[Fraction]:
    """Return [gamma_0, gamma_2, ..., gamma_{2 max_m}] exactly.

    The exponential generating functions satisfy

      (sum mu_n z^n/n!) (sum gamma_n z^n/n!) = 1.

    Odd moments and odd reciprocal coefficients vanish, so the recurrence can
    be written entirely in even indices.
    """
    gamma = [Fraction(1)]
    for m in range(1, max_m + 1):
        value = -sum(
            Fraction(math.comb(2 * m, 2 * r))
            * mu_even[r]
            * gamma[m - r]
            for r in range(1, m + 1)
        )
        gamma.append(value)
    return gamma


def legendre_coefficient_exact(n: int, mu_even: Sequence[Fraction]) -> Fraction:
    """Return u_n in up(x) = sum_{n>=0} u_n P_{2n}(x), exactly."""
    total = Fraction(0)
    for s in range(n + 1):
        # Coefficient of x^(2s) in P_{2n}(x).
        coeff = Fraction(
            (-1) ** (n - s) * math.factorial(2 * n + 2 * s),
            2 ** (2 * n)
            * math.factorial(n - s)
            * math.factorial(n + s)
            * math.factorial(2 * s),
        )
        total += coeff * mu_even[s]
    return Fraction(4 * n + 1, 2) * total


def v2_integer(n: int) -> int:
    """2-adic valuation of a nonzero integer."""
    if n == 0:
        raise ValueError("v2(0) is infinite")
    n = abs(n)
    return (n & -n).bit_length() - 1


def v2_fraction(x: Fraction) -> int:
    """2-adic valuation of a nonzero rational."""
    if x == 0:
        raise ValueError("v2(0) is infinite")
    return v2_integer(x.numerator) - v2_integer(x.denominator)


# ---------------------------------------------------------------------------
# Exact polynomial algebra, coefficients in ascending powers
# ---------------------------------------------------------------------------

def poly_trim(p: list[Fraction]) -> list[Fraction]:
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def poly_add(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    n = max(len(a), len(b))
    out = [Fraction(0) for _ in range(n)]
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return poly_trim(out)


def poly_scale(a: Sequence[Fraction], c: Fraction) -> list[Fraction]:
    return poly_trim([c * x for x in a])


def poly_mul(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    out = [Fraction(0) for _ in range(len(a) + len(b) - 1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return poly_trim(out)


def poly_shift(a: Sequence[Fraction], c: Fraction) -> list[Fraction]:
    """Return coefficients of p(x-c) when a are coefficients of p(x)."""
    out = [Fraction(0) for _ in range(len(a))]
    for j, aj in enumerate(a):
        for q in range(j + 1):
            out[q] += aj * math.comb(j, q) * (-c) ** (j - q)
    return poly_trim(out)


def poly_eval(a: Sequence[Fraction], x: Fraction) -> Fraction:
    value = Fraction(0)
    for coeff in reversed(a):
        value = value * x + coeff
    return value


def poly_integral_between(
    a: Sequence[Fraction], lo: Fraction, hi: Fraction
) -> Fraction:
    total = Fraction(0)
    for j, aj in enumerate(a):
        total += aj * (hi ** (j + 1) - lo ** (j + 1)) / (j + 1)
    return total


def legendre_polynomial_exact(n: int) -> list[Fraction]:
    """Return P_n in the monomial basis exactly, using the three-term recurrence."""
    if n == 0:
        return [Fraction(1)]
    if n == 1:
        return [Fraction(0), Fraction(1)]
    pnm1 = [Fraction(1)]
    pn = [Fraction(0), Fraction(1)]
    for k in range(1, n):
        xpn = [Fraction(0)] + pn
        pnp1 = poly_add(
            poly_scale(xpn, Fraction(2 * k + 1, k + 1)),
            poly_scale(pnm1, Fraction(-k, k + 1)),
        )
        pnm1, pn = pn, pnp1
    return pn


def deconvolved_legendre_exact(
    ell: int, gamma_even: Sequence[Fraction]
) -> list[Fraction]:
    """Return Q_ell = M_up(D)^(-1) P_ell exactly.

    Acting on a monomial x^j, gamma_s D^s/s! contributes
    gamma_s * binom(j,s) x^(j-s).  Only even s occur.
    """
    p = legendre_polynomial_exact(ell)
    q = [Fraction(0) for _ in range(ell + 1)]
    for j, aj in enumerate(p):
        if aj == 0:
            continue
        for r in range(j // 2 + 1):
            s = 2 * r
            q[j - s] += aj * gamma_even[r] * math.comb(j, s)
    return poly_trim(q)


def polynomial_to_latex(p: Sequence[Fraction], variable: str = "x") -> str:
    """Pretty exact polynomial, highest degree first."""
    terms: list[str] = []
    for power in range(len(p) - 1, -1, -1):
        c = p[power]
        if c == 0:
            continue
        sign = "-" if c < 0 else "+"
        a = abs(c)
        if a.denominator == 1:
            scalar = str(a.numerator)
        else:
            scalar = rf"\frac{{{a.numerator}}}{{{a.denominator}}}"
        if power == 0:
            body = scalar
        else:
            if a == 1:
                scalar = ""
            power_part = variable if power == 1 else rf"{variable}^{{{power}}}"
            body = scalar + power_part
        if not terms:
            terms.append(("-" if sign == "-" else "") + body)
        else:
            terms.append(f" {sign} {body}")
    return "".join(terms) if terms else "0"


# ---------------------------------------------------------------------------
# Clipped affine connection coefficients and spectral closure constants
# ---------------------------------------------------------------------------

def clipped_connection_exact(m: int, r: int, c: Fraction) -> Fraction:
    r"""Return C_{m,r}(c) exactly.

      C_{m,r}(c) = (2m+1)/2 * integral_{[-1,1] intersect [c-1,c+1]}
                                  P_m(x) P_{2r}(x-c) dx.

    For |c| >= 2 the intersection has zero length.  All calls used here have
    dyadic c, so the result is rational.
    """
    if abs(c) >= 2:
        return Fraction(0)
    lo = max(Fraction(-1), c - 1)
    hi = min(Fraction(1), c + 1)
    if lo >= hi:
        return Fraction(0)
    pm = legendre_polynomial_exact(m)
    p2r_shift = poly_shift(legendre_polynomial_exact(2 * r), c)
    integrand = poly_mul(pm, p2r_shift)
    return Fraction(2 * m + 1, 2) * poly_integral_between(integrand, lo, hi)


def spectral_closure_T_exact(
    m: int,
    ell: int,
    r: int,
    q_ell: Sequence[Fraction],
) -> Fraction:
    r"""Return T_{m,ell,r}^{(M)}, M=2^ell, exactly."""
    M = 2**ell
    total = Fraction(0)
    for k in range(-2 * M + 1, 2 * M):
        c = Fraction(k, M)
        total += poly_eval(q_ell, c) * clipped_connection_exact(m, r, c)
    return total / M


# ---------------------------------------------------------------------------
# Multiprecision high-degree coefficients
# ---------------------------------------------------------------------------

def up_even_moments_mp(max_m: int) -> list[mp.mpf]:
    mu = [mp.mpf(1)]
    for m in range(1, max_m + 1):
        rhs = mp.mpf(0)
        for r in range(1, m + 1):
            rhs += mp.mpf(math.comb(2 * m, 2 * r)) * mu[m - r] / (2 * r + 1)
        mu.append(rhs / (mp.mpf(4) ** m - 1))
    return mu


def legendre_coefficient_mp(n: int, mu_even: Sequence[mp.mpf]) -> mp.mpf:
    """Multiprecision coefficient, with a stable coefficient recurrence."""
    # Start with coefficient of x^(2n) in P_{2n}.
    coeff = mp.mpf(math.factorial(4 * n)) / (
        mp.mpf(2) ** (2 * n)
        * math.factorial(2 * n)
        * math.factorial(2 * n)
    )
    total = coeff * mu_even[n]
    # Descend from x^(2s) to x^(2s-2).  The exact ratio follows from the
    # closed coefficient formula and avoids repeated huge factorials.
    for s in range(n, 0, -1):
        # a_{s-1}/a_s, where a_s is coefficient of x^(2s).
        ratio = -mp.mpf((n + s) * (2 * s) * (2 * s - 1)) / (
            (n - s + 1) * (2 * n + 2 * s) * (2 * n + 2 * s - 1)
        )
        coeff *= ratio
        total += coeff * mu_even[s - 1]
    return mp.mpf(4 * n + 1) * total / 2


# ---------------------------------------------------------------------------
# Independent Fourier-product evaluator for up
# ---------------------------------------------------------------------------
class UpFFT:
    """Periodic inverse-FFT approximation of the compactly supported up density."""

    def __init__(self, period: float = 8.0, power: int = 18, factors: int = 42):
        self.period = float(period)
        self.count = 1 << power
        dx = self.period / self.count
        freq = np.fft.fftfreq(self.count, d=dx)
        transform = np.ones(self.count, dtype=np.float64)
        for j in range(factors):
            transform *= np.sinc(freq / (2.0**j))
        self.values = np.fft.ifft(transform).real * (self.count / self.period)
        self.dx = dx

    def __call__(self, x: np.ndarray | float) -> np.ndarray:
        x_arr = np.asarray(x, dtype=np.float64)
        y = np.mod(x_arr, self.period) / self.dx
        i0 = np.floor(y).astype(np.int64) % self.count
        frac = y - np.floor(y)
        i1 = (i0 + 1) % self.count
        return (1.0 - frac) * self.values[i0] + frac * self.values[i1]


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------

def write_exact_outputs(
    mu: Sequence[Fraction],
    gamma: Sequence[Fraction],
    u_exact: Sequence[Fraction],
    q_polys: Sequence[Sequence[Fraction]],
) -> None:
    with (HERE / "legendre_coefficients_exact.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["n", "numerator", "denominator", "decimal", "v2"])
        for n, value in enumerate(u_exact):
            w.writerow([
                n,
                value.numerator,
                value.denominator,
                f"{float(value):.17g}",
                v2_fraction(value),
            ])

    with (HERE / "moments_and_reciprocal_coefficients.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow([
            "m", "mu_2m_num", "mu_2m_den", "v2(mu_2m-1)",
            "gamma_2m_num", "gamma_2m_den",
        ])
        for m in range(min(len(mu), len(gamma))):
            delta = mu[m] - 1
            delta_v2 = "inf" if delta == 0 else v2_fraction(delta)
            w.writerow([
                m,
                mu[m].numerator,
                mu[m].denominator,
                delta_v2,
                gamma[m].numerator,
                gamma[m].denominator,
            ])

    lines = ["% Generated by experiments.py", r"\begin{align*}"]
    for ell, q in enumerate(q_polys):
        ending = r",\\" if ell + 1 < len(q_polys) else r"."
        lines.append(rf"Q_{{{ell}}}(x)&={polynomial_to_latex(q)}{ending}")
    lines.append(r"\end{align*}")
    (HERE / "low_degree_Q.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")

    lines = [
        "% Generated by experiments.py",
        r"\begin{tabular}{@{}rllr@{}}",
        r"\toprule",
        r"$n$ & exact $u_n$ & decimal value & $v_2(u_n)$ \\",
        r"\midrule",
    ]
    for n, value in enumerate(u_exact[:12]):
        if value.denominator == 1:
            exact = str(value.numerator)
        else:
            sign = "-" if value < 0 else ""
            exact = sign + rf"\frac{{{abs(value.numerator)}}}{{{value.denominator}}}"
        lines.append(rf"{n} & ${exact}$ & ${float(value):.10g}$ & ${v2_fraction(value)}$ \\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (HERE / "legendre_coefficients_table.tex").write_text(
        "\n".join(lines) + "\n", encoding="utf-8"
    )


def write_spectral_outputs(
    cases: Sequence[tuple[int, int]],
    max_r: int,
    u_exact: Sequence[Fraction],
    q_by_ell: dict[int, Sequence[Fraction]],
) -> dict[tuple[int, int], list[float]]:
    partials: dict[tuple[int, int], list[float]] = {}
    with (HERE / "spectral_sum_rules.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow([
            "ell", "m", "r", "T_num", "T_den", "u_num", "u_den",
            "term_decimal", "partial_sum_decimal", "target",
        ])
        for ell, m in cases:
            running = Fraction(0)
            values: list[float] = []
            target = 1 if ell == m else 0
            for r in range(max_r + 1):
                T = spectral_closure_T_exact(m, ell, r, q_by_ell[ell])
                term = u_exact[r] * T
                running += term
                values.append(float(running))
                w.writerow([
                    ell, m, r, T.numerator, T.denominator,
                    u_exact[r].numerator, u_exact[r].denominator,
                    f"{float(term):.17g}", f"{float(running):.17g}", target,
                ])
            partials[(ell, m)] = values
    return partials


def high_precision_decay(max_n: int, dps: int) -> tuple[list[mp.mpf], list[float]]:
    mp.mp.dps = dps
    mu_mp = up_even_moments_mp(max_n)
    coeffs: list[mp.mpf] = []
    ratios: list[float] = []
    with (HERE / "legendre_decay_high_precision.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["n", "u_n_scientific", "minus_log_abs", "ratio_log_squared"])
        for n in range(max_n + 1):
            value = legendre_coefficient_mp(n, mu_mp)
            coeffs.append(value)
            if n >= 2 and value != 0:
                minus_log = -mp.log(abs(value))
                ratio = minus_log / (mp.log(n) ** 2)
                ratios.append(float(ratio))
                w.writerow([
                    n,
                    mp.nstr(value, 25),
                    mp.nstr(minus_log, 25),
                    mp.nstr(ratio, 25),
                ])
            else:
                ratios.append(float("nan"))
                w.writerow([n, mp.nstr(value, 25), "", ""])
    return coeffs, ratios


def synthesis_checks(q_polys: Sequence[Sequence[Fraction]], max_ell: int) -> list[float]:
    evaluator = UpFFT()
    x = np.linspace(-1.0, 1.0, 2001)
    errors: list[float] = []
    with (HERE / "finite_synthesis_checks.csv").open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["ell", "M", "atom_count", "max_abs_error"])
        for ell in range(max_ell + 1):
            M = 2**ell
            q = q_polys[ell]
            reconstruction = np.zeros_like(x)
            for k in range(-2 * M + 1, 2 * M):
                qval = float(poly_eval(q, Fraction(k, M)))
                reconstruction += (qval / M) * evaluator(x - k / M)
            truth = np.polynomial.legendre.Legendre.basis(ell)(x)
            err = float(np.max(np.abs(reconstruction - truth)))
            errors.append(err)
            w.writerow([ell, M, 4 * M - 1, f"{err:.17g}"])
    return errors


def make_plots(
    ratios: Sequence[float],
    partials: dict[tuple[int, int], list[float]],
    synthesis_errors: Sequence[float],
) -> None:
    # Plot 1: normalized logarithmic decay of the exact high-precision coefficients.
    n = np.arange(len(ratios))
    mask = n >= 5
    plt.figure(figsize=(8.2, 4.8))
    plt.plot(n[mask], np.asarray(ratios)[mask], linewidth=1.0)
    plt.axhline(1.0 / (2.0 * math.log(2.0)), linestyle="--", linewidth=1.0,
                label=r"$1/(2\log 2)$ rigorous lower benchmark")
    plt.xlabel(r"Legendre block index $n$")
    plt.ylabel(r"$-\log |u_n|/(\log n)^2$")
    plt.title("Log-square normalization of the Fourier--Legendre coefficients")
    plt.grid(True, alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(HERE / "legendre_decay_ratios.png", dpi=180)
    plt.close()

    # Plot 2: exact rational spectral sum rules, displayed as decimal partial sums.
    plt.figure(figsize=(8.2, 4.8))
    for (ell, m), values in partials.items():
        plt.plot(range(len(values)), values, marker="o", markersize=3,
                 label=rf"$(\ell,m)=({ell},{m})$")
    plt.axhline(0.0, linewidth=0.8)
    plt.axhline(1.0, linewidth=0.8)
    plt.xlabel(r"truncation index $R$")
    plt.ylabel(r"$\sum_{r=0}^{R}u_rT_{m\ell r}^{(2^\ell)}$")
    plt.title("Convergence of the arithmetic spectral closure identities")
    plt.grid(True, alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(HERE / "spectral_sum_convergence.png", dpi=180)
    plt.close()

    # Plot 3: independent numerical residual of the finite synthesis formula.
    plt.figure(figsize=(8.2, 4.8))
    degrees = np.arange(len(synthesis_errors))
    plt.semilogy(degrees, synthesis_errors, marker="o")
    plt.xlabel(r"Legendre degree $\ell$")
    plt.ylabel("maximum absolute residual on 2001 points")
    plt.title("Independent FFT check of finite shifted-up synthesis")
    plt.grid(True, alpha=0.25)
    plt.tight_layout()
    plt.savefig(HERE / "finite_synthesis_residuals.png", dpi=180)
    plt.close()


def write_summary(
    u_exact: Sequence[Fraction],
    ratios: Sequence[float],
    synthesis_errors: Sequence[float],
    partials: dict[tuple[int, int], list[float]],
) -> None:
    lines = [
        "Legendre--Rvachev experiment summary",
        "=====================================",
        "",
        f"Exact coefficients checked: n=0..{len(u_exact)-1}",
        "Observed v2(u_n): " + ", ".join(str(v2_fraction(x)) for x in u_exact),
        "",
        "Selected normalized decay ratios -log|u_n|/(log n)^2:",
    ]
    for n in [20, 40, 60, 80, 100, 120, 140, 160, 180, 200]:
        if n < len(ratios):
            lines.append(f"  n={n:3d}: {ratios[n]:.12f}")
    lines += [
        f"  rigorous benchmark 1/(2 log 2): {1/(2*math.log(2)):.12f}",
        "",
        "Finite synthesis maximum residuals:",
    ]
    for ell, err in enumerate(synthesis_errors):
        lines.append(f"  ell={ell}: {err:.6e}")
    lines += ["", "Spectral closure final displayed partial sums:"]
    for key, values in partials.items():
        lines.append(f"  (ell,m)={key}: {values[-1]:.16g}")
    (HERE / "experiment_summary.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exact-n", type=int, default=80,
                        help="largest exact rational Legendre coefficient")
    parser.add_argument("--decay-n", type=int, default=200,
                        help="largest multiprecision Legendre coefficient")
    parser.add_argument("--dps", type=int, default=2300,
                        help="mpmath decimal precision for high-degree cancellation")
    parser.add_argument("--spectral-r", type=int, default=14,
                        help="largest r in spectral sum-rule tables")
    parser.add_argument("--synthesis-degree", type=int, default=5,
                        help="largest degree in independent FFT synthesis check")
    parser.add_argument("--no-plots", action="store_true")
    args = parser.parse_args()

    max_exact = max(args.exact_n, args.spectral_r, args.synthesis_degree, 8)
    mu = up_even_moments_exact(max_exact)
    gamma = reciprocal_mgf_even_coefficients(max_exact, mu)
    u_exact = [legendre_coefficient_exact(n, mu) for n in range(args.exact_n + 1)]
    q_polys = [deconvolved_legendre_exact(ell, gamma) for ell in range(max(args.synthesis_degree, 8) + 1)]
    write_exact_outputs(mu, gamma, u_exact, q_polys[:7])

    cases = [(1, 1), (2, 2), (2, 0), (2, 1)]
    q_by_ell = {ell: q_polys[ell] for ell, _ in cases}
    partials = write_spectral_outputs(cases, args.spectral_r, u_exact, q_by_ell)

    _, ratios = high_precision_decay(args.decay_n, args.dps)
    errors = synthesis_checks(q_polys, args.synthesis_degree)

    if not args.no_plots:
        make_plots(ratios, partials, errors)
    write_summary(u_exact, ratios, errors, partials)

    print((HERE / "experiment_summary.txt").read_text(encoding="utf-8"))


if __name__ == "__main__":
    main()
