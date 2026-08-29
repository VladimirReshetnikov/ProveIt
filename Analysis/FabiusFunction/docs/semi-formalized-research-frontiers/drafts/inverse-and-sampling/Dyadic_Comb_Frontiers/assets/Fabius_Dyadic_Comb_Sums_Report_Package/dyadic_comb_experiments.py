#!/usr/bin/env python3
"""Exact and high-precision experiments for dyadic Fabius/Rvachev comb sums.

This script accompanies the report

    Dyadic-Comb Sums for the Fabius--Rvachev System

It intentionally implements the formulas in several independent ways:

* exact dyadic Fabius samples from the moment--Thue--Morse convolution;
* direct monomial comb sums from those samples;
* a Bernoulli/Faulhaber closed form after exchanging the two finite sums;
* the Bell--Prouhet collapse of a full Thue--Morse block;
* the rational ordinary generating function of a complete sample row;
* the reduction of an n-fold prefix sum to shifted one-fold comb moments;
* high-precision complex-power sums and Euler--Maclaurin extrapolation.

All integer calculations use fractions.Fraction.  SymPy is used only for
symbolic Bernoulli polynomials, polynomial coefficient extraction, and the
rational generating-function checks.  mpmath is used for nonintegral powers.

Run, for example,

    python dyadic_comb_experiments.py --outdir generated --max-level 8

The output directory receives CSV files and small LaTeX table fragments used
by the paper.  The default calculation is deliberately modest and should run
comfortably on an ordinary laptop.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
from typing import Iterable, Sequence

import mpmath as mp
import sympy as sp


# ---------------------------------------------------------------------------
# Elementary exact data
# ---------------------------------------------------------------------------


def thue_morse_sign(n: int) -> int:
    """Return epsilon_n = (-1)^(binary digit sum of n)."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    return -1 if n.bit_count() & 1 else 1


@lru_cache(maxsize=None)
def rvachev_even_moments(max_index: int) -> tuple[Fraction, ...]:
    """Return c_r = integral_{-1}^1 x^(2r) up(x) dx, 0 <= r <= max_index.

    The recurrence is

      (2r+1)(2^(2r)-1)c_r = sum_{j<r} binom(2r+1,2j)c_j.

    It is one of the standard exact interfaces in the ProveIt corpus.
    """
    if max_index < 0:
        return tuple()
    c = [Fraction(0)] * (max_index + 1)
    c[0] = Fraction(1)
    for r in range(1, max_index + 1):
        numerator = sum(Fraction(comb(2 * r + 1, 2 * j)) * c[j] for j in range(r))
        denominator = (2 * r + 1) * (2 ** (2 * r) - 1)
        c[r] = numerator / denominator
    return tuple(c)


def fabius_moment(n: int) -> Fraction:
    """Return d_n = E[Y^n] for the Fabius random variable Y in [0,1].

    If X=2Y-1 has density up, symmetry gives

      d_n = 2^(-n) sum_j binom(n,2j)c_j.
    """
    if n < 0:
        raise ValueError("n must be nonnegative")
    c = rvachev_even_moments(n // 2)
    return sum(Fraction(comb(n, 2 * j)) * c[j] for j in range(n // 2 + 1)) / (2**n)


def continuous_fabius_integral_integer(p: int) -> Fraction:
    """Return I_p = integral_0^1 x^p F(x) dx for p a nonnegative integer."""
    if p < 0:
        raise ValueError("p must be nonnegative")
    return (Fraction(1) - fabius_moment(p + 1)) / Fraction(p + 1)


# ---------------------------------------------------------------------------
# Exact dyadic samples and direct comb sums
# ---------------------------------------------------------------------------


@lru_cache(maxsize=None)
def dyadic_fabius_samples(level: int) -> tuple[Fraction, ...]:
    """Return (F(k/2^level))_{k=0}^{2^level} exactly.

    The implementation is the finite convolution

      F(k/M) = C_N sum_{a=0}^{k-1} epsilon_a P_N(2(k-a)-1),

    with M=2^N and

      P_N(y) = sum_j binom(N,2j)c_j y^(N-2j),
      C_N    = 2^(-N(N+1)/2)/N!.

    This is O(M^2) exact arithmetic and is intended for verification levels,
    not for very large N.
    """
    if level < 0:
        raise ValueError("level must be nonnegative")
    n = level
    m = 1 << n
    c = rvachev_even_moments(n // 2)
    scale = Fraction(1, factorial(n) * 2 ** (n * (n + 1) // 2))

    kernel = [Fraction(0)] * (m + 1)
    for r in range(1, m + 1):
        y = 2 * r - 1
        kernel[r] = scale * sum(
            Fraction(comb(n, 2 * j)) * c[j] * y ** (n - 2 * j)
            for j in range(n // 2 + 1)
        )

    values = [Fraction(0)] * (m + 1)
    for k in range(1, m + 1):
        values[k] = sum(thue_morse_sign(a) * kernel[k - a] for a in range(k))

    assert values[0] == 0
    assert values[m] == 1
    assert all(values[k] + values[m - k] == 1 for k in range(m + 1))
    return tuple(values)


def left_comb_integer(level: int, p: int) -> Fraction:
    """L_{N,p} = M^(-1) sum_{k=0}^{M-1}(k/M)^p F(k/M), exactly."""
    if p < 0:
        raise ValueError("use left_comb_complex for negative powers")
    m = 1 << level
    samples = dyadic_fabius_samples(level)
    return sum(Fraction(k, m) ** p * samples[k] for k in range(m)) / m


# ---------------------------------------------------------------------------
# Bernoulli/Faulhaber closed form
# ---------------------------------------------------------------------------


@lru_cache(maxsize=None)
def power_sum(k: int, exponent: int) -> Fraction:
    """Return sum_{r=1}^k r^exponent by Bernoulli polynomials."""
    if k <= 0:
        return Fraction(0)
    if exponent < 0:
        raise ValueError("exponent must be nonnegative")
    # B_n(k+1)-B_n(1), rather than B_n(0), handles exponent=0 uniformly.
    value = (
        sp.bernoulli(exponent + 1, k + 1) - sp.bernoulli(exponent + 1, 1)
    ) / (exponent + 1)
    value = sp.cancel(value)
    return Fraction(int(sp.numer(value)), int(sp.denom(value)))


def left_comb_bernoulli(level: int, p: int) -> Fraction:
    """Evaluate the explicit Bernoulli--Thue--Morse closed form for L_{N,p}.

    This exchanges the dyadic-value convolution with the monomial comb sum.
    The remaining inner sum is a Faulhaber power sum.  It is independent of
    dyadic_fabius_samples(), so equality is a meaningful cross-check.
    """
    if p < 0:
        raise ValueError("p must be nonnegative")
    n = level
    m = 1 << n
    c = rvachev_even_moments(n // 2)
    scale = Fraction(1, factorial(n) * 2 ** (n * (n + 1) // 2))
    total = Fraction(0)

    for a in range(m):
        upper = m - 1 - a
        if upper <= 0:
            continue
        block = Fraction(0)
        for j in range(n // 2 + 1):
            degree = n - 2 * j
            moment_factor = Fraction(comb(n, 2 * j)) * c[j]
            for alpha in range(p + 1):
                left_factor = Fraction(comb(p, alpha)) * a ** (p - alpha)
                for beta in range(degree + 1):
                    odd_power_factor = (
                        Fraction(comb(degree, beta))
                        * 2**beta
                        * (-1) ** (degree - beta)
                    )
                    block += (
                        moment_factor
                        * left_factor
                        * odd_power_factor
                        * power_sum(upper, alpha + beta)
                    )
        total += thue_morse_sign(a) * block

    return scale * total / (m ** (p + 1))


# ---------------------------------------------------------------------------
# Bell--Prouhet collapse of a complete signed dyadic block
# ---------------------------------------------------------------------------


def complete_bell_values(x: Sequence[Fraction]) -> list[Fraction]:
    """Return Y_0,...,Y_n for complete exponential Bell polynomials.

    The recurrence is

      Y_n = sum_{k=1}^n binom(n-1,k-1)x_k Y_{n-k}.
    """
    result = [Fraction(1)]
    for n in range(1, len(x) + 1):
        value = sum(
            Fraction(comb(n - 1, k - 1)) * x[k - 1] * result[n - k]
            for k in range(1, n + 1)
        )
        result.append(value)
    return result


def thue_morse_log_jets(level: int, count: int) -> list[Fraction]:
    """Return lambda_1,...,lambda_count in the Bell expansion of Theta_N(e^t)."""
    n = level
    m = 1 << n
    jets: list[Fraction] = []
    for r in range(1, count + 1):
        if r == 1:
            jets.append(Fraction(m - 1, 2))
        elif r & 1:
            jets.append(Fraction(0))
        else:
            q = r // 2
            b = sp.bernoulli(2 * q)
            bernoulli = Fraction(int(b.p), int(b.q))
            jets.append(
                bernoulli
                / Fraction(2 * q)
                * Fraction(2 ** (2 * q * n) - 1, 2 ** (2 * q) - 1)
            )
    return jets


def signed_thue_morse_power_bell(level: int, exponent: int) -> Fraction:
    """Return sum_{a<2^N} epsilon_a a^exponent via Bell polynomials."""
    n = level
    if exponent < n:
        return Fraction(0)
    s = exponent - n
    bell = complete_bell_values(thue_morse_log_jets(n, s))[s]
    return (
        (-1) ** n
        * 2 ** (n * (n - 1) // 2)
        * Fraction(factorial(exponent), factorial(s))
        * bell
    )


def left_comb_bell(level: int, p: int) -> Fraction:
    """Evaluate L_{N,p} after collapsing the full a-sum to at most p+2 Bell terms."""
    if p < 0:
        raise ValueError("p must be nonnegative")
    n = level
    m = 1 << n
    a = sp.symbols("a")
    c = rvachev_even_moments(n // 2)
    h_poly = sp.Integer(0)

    for j in range(n // 2 + 1):
        degree = n - 2 * j
        moment_factor = sp.Rational(comb(n, 2 * j)) * sp.Rational(
            c[j].numerator, c[j].denominator
        )
        for alpha in range(p + 1):
            left_factor = sp.binomial(p, alpha) * a ** (p - alpha)
            for beta in range(degree + 1):
                odd_power_factor = (
                    sp.binomial(degree, beta)
                    * 2**beta
                    * (-1) ** (degree - beta)
                )
                power = alpha + beta
                faulhaber = (
                    sp.bernoulli(power + 1, m - a) - sp.bernoulli(power + 1, 1)
                ) / (power + 1)
                h_poly += moment_factor * left_factor * odd_power_factor * faulhaber

    polynomial = sp.Poly(sp.expand(h_poly), a)
    signed_sum = Fraction(0)
    for (degree,), coefficient in polynomial.terms():
        coefficient = sp.Rational(coefficient)
        coeff_fraction = Fraction(int(coefficient.p), int(coefficient.q))
        signed_sum += coeff_fraction * signed_thue_morse_power_bell(n, degree)

    scale = Fraction(1, factorial(n) * 2 ** (n * (n + 1) // 2))
    return scale * signed_sum / (m ** (p + 1))


# ---------------------------------------------------------------------------
# Rational sample-row generating function
# ---------------------------------------------------------------------------


def apply_two_euler_minus_one(expr: sp.Expr, repetitions: int, z: sp.Symbol) -> sp.Expr:
    """Apply (2 z d/dz - 1)^repetitions to expr."""
    result = expr
    for _ in range(repetitions):
        result = sp.cancel(2 * z * sp.diff(result, z) - result)
    return result


def sample_generating_functions(level: int) -> tuple[sp.Expr, sp.Poly]:
    """Return the infinite row OGF and the finite sample polynomial A_N(z).

    The infinite OGF has coefficients F(k/2^N) for 0<=k<=2^N and then
    coefficient 1 forever.  Subtracting z^M/(1-z) gives the finite polynomial
    A_N(z)=sum_{k=0}^{M-1}F(k/M)z^k.
    """
    n = level
    m = 1 << n
    z = sp.symbols("z")
    c = rvachev_even_moments(n // 2)
    theta = sp.prod(1 - z ** (1 << j) for j in range(n))
    base = z / (1 - z)

    kernel_ogf = sp.Integer(0)
    for j in range(n // 2 + 1):
        coeff = sp.Rational(comb(n, 2 * j)) * sp.Rational(
            c[j].numerator, c[j].denominator
        )
        kernel_ogf += coeff * apply_two_euler_minus_one(base, n - 2 * j, z)

    scale = sp.Rational(1, factorial(n) * 2 ** (n * (n + 1) // 2))
    infinite = sp.factor(sp.cancel(scale * theta * kernel_ogf))
    finite = sp.cancel(infinite - z**m / (1 - z))
    finite_poly = sp.Poly(sp.cancel(finite), z)

    samples = dyadic_fabius_samples(n)
    expected = sp.Poly(
        sum(sp.Rational(v.numerator, v.denominator) * z**k for k, v in enumerate(samples[:-1])),
        z,
    )
    assert finite_poly == expected
    return infinite, finite_poly


# ---------------------------------------------------------------------------
# Exact Euler--Maclaurin collapse
# ---------------------------------------------------------------------------


def falling_integer(p: int, count: int) -> int:
    result = 1
    for j in range(count):
        result *= p - j
    return result


def exact_euler_maclaurin_value(level: int, p: int) -> Fraction:
    """The finite Euler--Maclaurin expression predicted for L_{N,p}."""
    m = 1 << level
    value = continuous_fabius_integral_integer(p) - Fraction(1, 2 * m)
    for r in range(1, (p + 2) // 2 + 1):
        derivative_order = 2 * r - 1
        if derivative_order > p:
            break
        b = sp.bernoulli(2 * r)
        bernoulli = Fraction(int(b.p), int(b.q))
        value += (
            bernoulli
            * falling_integer(p, derivative_order)
            / Fraction(factorial(2 * r) * m ** (2 * r))
        )
    return value


def guaranteed_exact_degree(level: int) -> int:
    """d_N=2 floor(N/2), the degree proved exact in the report."""
    return 2 * (level // 2)


# ---------------------------------------------------------------------------
# Iterated sums
# ---------------------------------------------------------------------------


def unsigned_stirling_first(n: int, k: int) -> int:
    """Unsigned Stirling number [n k]."""
    return int(sp.functions.combinatorial.numbers.stirling(n, k, kind=1, signed=False))


def iterated_comb_direct(level: int, p: int, order: int) -> Fraction:
    """Normalized order-fold prefix sum evaluated at the last grid point."""
    if order < 1:
        raise ValueError("order must be positive")
    m = 1 << level
    samples = dyadic_fabius_samples(level)
    total = Fraction(0)
    for k in range(1, m):
        kernel = comb(m - k + order - 2, order - 1)
        total += Fraction(kernel) * Fraction(k, m) ** p * samples[k]
    return total / (m**order)


def iterated_comb_reduced(level: int, p: int, order: int) -> Fraction:
    """Reduce the order-fold sum to shifted one-fold L_{N,p+ell}."""
    if order < 1:
        raise ValueError("order must be positive")
    m = 1 << level
    total = Fraction(0)
    for j in range(order):
        stirling = unsigned_stirling_first(order - 1, j)
        if stirling == 0:
            continue
        finite_difference = sum(
            Fraction((-1) ** ell * comb(j, ell)) * left_comb_integer(level, p + ell)
            for ell in range(j + 1)
        )
        total += Fraction(stirling * m**j) * finite_difference
    return Fraction(1, factorial(order - 1) * m ** (order - 1)) * total


# ---------------------------------------------------------------------------
# Complex powers and Euler--Maclaurin extrapolation
# ---------------------------------------------------------------------------


def mp_from_fraction(value: Fraction) -> mp.mpf:
    return mp.mpf(value.numerator) / value.denominator


def left_comb_complex(level: int, alpha: complex | mp.mpf | mp.mpc) -> mp.mpc:
    """Direct finite entire function L_N(alpha), using exact rational samples."""
    m = 1 << level
    samples = dyadic_fabius_samples(level)
    alpha_mp = mp.mpc(alpha)
    total = mp.mpc(0)
    for k in range(1, m):
        x = mp.mpf(k) / m
        total += mp.power(x, alpha_mp) * mp_from_fraction(samples[k])
    return total / m


def falling_complex(alpha: mp.mpc, count: int) -> mp.mpc:
    value = mp.mpc(1)
    for j in range(count):
        value *= alpha - j
    return value


def em_extrapolated_integral(level: int, alpha: complex, terms: int = 6) -> mp.mpc:
    """Estimate I(alpha) from L_N(alpha) by reversing Euler--Maclaurin."""
    m = 1 << level
    h = mp.mpf(1) / m
    alpha_mp = mp.mpc(alpha)
    value = left_comb_complex(level, alpha_mp) + h / 2
    for r in range(1, terms + 1):
        b = mp.mpf(str(sp.N(sp.bernoulli(2 * r), mp.mp.dps)))
        value -= b / factorial(2 * r) * falling_complex(alpha_mp, 2 * r - 1) * h ** (2 * r)
    return value


def rvachev_fourier_mp(x: mp.mpf, factors: int = 120) -> mp.mpf:
    """Truncate Phi(x)=prod_{j>=0} sinc_pi(x/2^j) at high precision.

    The omitted tail is harmless for the verification levels below because each
    factor differs from 1 by O(4^{-j}).  This routine is intentionally independent
    of the exact dyadic evaluator.
    """
    value = mp.mpf(1)
    for j in range(factors):
        y = x / mp.power(2, j)
        value *= mp.sin(mp.pi * y) / (mp.pi * y) if y else 1
    return value


def odd_level_defect_fourier(level: int, terms: int = 180, factors: int = 120) -> mp.mpf:
    """Numerically evaluate the half-integer Fourier series for R_{N,N}.

    This formula applies only to odd N.  It is checked against the exact rational
    comb defect in run_self_checks().
    """
    if level < 1 or level % 2 == 0:
        raise ValueError("level must be a positive odd integer")
    series = mp.fsum(
        rvachev_fourier_mp(mp.mpf(2 * m + 1) / 2, factors)
        / mp.power(2 * m + 1, level + 1)
        for m in range(terms)
    )
    prefactor = (
        2
        * (-1) ** ((level + 1) // 2)
        * mp.factorial(level)
        / ((2 * mp.pi) ** (level + 1) * mp.power(2, level * (level + 1)))
    )
    return prefactor * series


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------


def fraction_tex(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return rf"\frac{{{value.numerator}}}{{{value.denominator}}}"


def correction_tex(p: int) -> str:
    terms: list[str] = []
    for r in range(1, (p + 2) // 2 + 1):
        derivative_order = 2 * r - 1
        if derivative_order > p:
            break
        b = sp.bernoulli(2 * r)
        coeff = Fraction(int(b.p), int(b.q)) * falling_integer(p, derivative_order) / factorial(2 * r)
        if coeff == 0:
            continue
        sign = "+" if coeff > 0 else "-"
        mag = abs(coeff)
        if mag == 1:
            body = rf"h^{{{2*r}}}"
        else:
            body = rf"{fraction_tex(mag)}h^{{{2*r}}}"
        terms.append(f" {sign} {body}")
    return "".join(terms) if terms else ""


def write_integer_table(outdir: Path, max_p: int = 8) -> None:
    csv_path = outdir / "integer_closed_forms.csv"
    tex_path = outdir / "integer_closed_forms.tex"
    rows = []
    for p in range(max_p + 1):
        rows.append(
            {
                "p": p,
                "I_p": str(continuous_fabius_integral_integer(p)),
                "minimum_level": 2 * ((p + 1) // 2),
                "correction": correction_tex(p),
            }
        )
    with csv_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)

    with tex_path.open("w", encoding="utf-8") as f:
        f.write("% Generated by dyadic_comb_experiments.py\n")
        f.write("\\begin{tabular}{c c c l}\n\\toprule\n")
        f.write("$p$ & $I_p$ & sufficient $N$ & exact $L_{N,p}$ \\\\\n")
        f.write("\\midrule\n")
        for row in rows:
            p = int(row["p"])
            ip = continuous_fabius_integral_integer(p)
            formula = rf"{fraction_tex(ip)}-\frac{{h}}{{2}}{correction_tex(p)}"
            f.write(f"{p} & ${fraction_tex(ip)}$ & ${row['minimum_level']}$ & ${formula}$ \\\\\n")
        f.write("\\bottomrule\n\\end{tabular}\n")


def write_exactness_matrix(outdir: Path, max_level: int, max_p: int = 10) -> None:
    csv_path = outdir / "exactness_matrix.csv"
    tex_path = outdir / "exactness_matrix.tex"
    matrix: list[list[str]] = []
    for n in range(max_level + 1):
        row = []
        for p in range(max_p + 1):
            exact = left_comb_integer(n, p) == exact_euler_maclaurin_value(n, p)
            row.append("1" if exact else "0")
        matrix.append(row)

    with csv_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["N/p", *range(max_p + 1)])
        for n, row in enumerate(matrix):
            writer.writerow([n, *row])

    with tex_path.open("w", encoding="utf-8") as f:
        f.write("% Generated by dyadic_comb_experiments.py\n")
        f.write("\\begin{tabular}{c " + "c" * (max_p + 1) + "}\n\\toprule\n")
        f.write("$N\\backslash p$ & " + " & ".join(map(str, range(max_p + 1))) + " \\\\\n")
        f.write("\\midrule\n")
        for n, row in enumerate(matrix):
            marks = [r"$\checkmark$" if item == "1" else r"$\cdot$" for item in row]
            f.write(f"{n} & " + " & ".join(marks) + " \\\\\n")
        f.write("\\bottomrule\n\\end{tabular}\n")


def write_first_defects(outdir: Path, max_level: int) -> None:
    csv_path = outdir / "first_defects.csv"
    tex_path = outdir / "first_defects.tex"
    rows = []
    for n in range(1, max_level + 1):
        p = n if n & 1 else n + 1
        defect = left_comb_integer(n, p) - exact_euler_maclaurin_value(n, p)
        rows.append((n, p, defect))

    with csv_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["N", "first_tested_p", "defect"])
        for n, p, defect in rows:
            writer.writerow([n, p, str(defect)])

    with tex_path.open("w", encoding="utf-8") as f:
        f.write("% Generated by dyadic_comb_experiments.py\n")
        f.write("\\begingroup\n\\renewcommand{\\arraystretch}{1.25}\n")
        f.write("\\begin{tabular}{c c r}\n\\toprule\n")
        f.write(r"$N$ & first degree beyond the proved range & exact defect \\" + "\n" + r"\midrule" + "\n")
        for n, p, defect in rows:
            f.write(f"{n} & {p} & ${{{defect.numerator}}}/{{{defect.denominator}}}$ " + r"\\" + "\n")
        f.write("\\bottomrule\n\\end{tabular}\n\\endgroup\n")


def write_generating_examples(outdir: Path, levels: Iterable[int] = (1, 2, 3)) -> None:
    path = outdir / "generating_functions.txt"
    with path.open("w", encoding="utf-8") as f:
        for n in levels:
            infinite, finite = sample_generating_functions(n)
            f.write(f"N={n}\n")
            f.write(f"infinite OGF: {sp.sstr(infinite)}\n")
            f.write(f"finite A_N:   {sp.sstr(finite.as_expr())}\n\n")


def write_fractional_table(outdir: Path, levels: Sequence[int]) -> None:
    mp.mp.dps = 70
    alphas = [-1, -0.5, 0.5, 1.5, 3.5]
    csv_path = outdir / "fractional_values.csv"
    tex_path = outdir / "fractional_values.tex"
    reference_level = max(levels)

    rows = []
    for alpha in alphas:
        reference = em_extrapolated_integral(reference_level, alpha, terms=6)
        values = [left_comb_complex(n, alpha) for n in levels]
        rows.append((alpha, values, reference))

    with csv_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["alpha", *[f"L_{n}" for n in levels], "EM_reference"])
        for alpha, values, reference in rows:
            writer.writerow(
                [alpha, *[mp.nstr(v, 25) for v in values], mp.nstr(reference, 25)]
            )

    with tex_path.open("w", encoding="utf-8") as f:
        f.write("% Generated by dyadic_comb_experiments.py\n")
        f.write("\\begin{tabular}{c " + "r" * len(levels) + " r}\n\\toprule\n")
        f.write(r"$\alpha$ & " + " & ".join(rf"$L_{{{n},\alpha}}$" for n in levels) + r" & EM estimate of $I(\alpha)$ \\" + "\n")
        f.write("\\midrule\n")
        for alpha, values, reference in rows:
            fields = [mp.nstr(mp.re(v), 12) for v in values]
            f.write(f"{alpha:g} & " + " & ".join(fields) + f" & {mp.nstr(mp.re(reference), 12)} \\\\\n")
        f.write("\\bottomrule\n\\end{tabular}\n")


def run_self_checks(max_level: int) -> None:
    """Run independent exact checks used by the report."""
    for n in range(max_level + 1):
        for p in range(0, min(8, max_level + 2) + 1):
            direct = left_comb_integer(n, p)
            assert direct == left_comb_bernoulli(n, p), (n, p, direct, left_comb_bernoulli(n, p))
            # Bell coefficient extraction is much more expensive; check a representative range.
            if n <= 5 and p <= 5:
                assert direct == left_comb_bell(n, p), (n, p)
        for p in range(0, guaranteed_exact_degree(n) + 1):
            assert left_comb_integer(n, p) == exact_euler_maclaurin_value(n, p), (n, p)

    for n in range(1, min(max_level, 6) + 1):
        for p in range(0, 5):
            for order in range(1, 5):
                assert iterated_comb_direct(n, p, order) == iterated_comb_reduced(n, p, order)

    mp.mp.dps = 70
    for n in (1, 3, 5):
        if n <= max_level:
            exact = left_comb_integer(n, n) - exact_euler_maclaurin_value(n, n)
            numerical = odd_level_defect_fourier(n)
            assert abs(numerical - mp_from_fraction(exact)) < mp.mpf("1e-18"), (n, exact, numerical)

    for n in range(1, min(max_level, 6) + 1):
        sample_generating_functions(n)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--outdir", type=Path, default=Path("generated"))
    parser.add_argument("--max-level", type=int, default=8)
    args = parser.parse_args()

    if args.max_level < 1:
        raise SystemExit("--max-level must be at least 1")
    args.outdir.mkdir(parents=True, exist_ok=True)

    run_self_checks(args.max_level)
    write_integer_table(args.outdir)
    write_exactness_matrix(args.outdir, args.max_level)
    write_first_defects(args.outdir, args.max_level)
    write_generating_examples(args.outdir)
    fractional_levels = tuple(n for n in (4, 6, 8) if n <= args.max_level)
    if not fractional_levels:
        fractional_levels = (args.max_level,)
    write_fractional_table(args.outdir, fractional_levels)

    print(f"All checks passed.  Generated files are in {args.outdir.resolve()}")


if __name__ == "__main__":
    main()
