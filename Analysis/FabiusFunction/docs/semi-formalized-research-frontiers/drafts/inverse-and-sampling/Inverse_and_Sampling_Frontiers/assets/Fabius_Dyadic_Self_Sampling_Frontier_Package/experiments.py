#!/usr/bin/env python3
"""Reproducible experiments for the Fabius--Rvachev self-sampling report.

The script has four independent purposes.

1.  It computes exact dyadic values of the Fabius function from the
    moment--Thue--Morse formula in the ProveIt exposition.  All arithmetic in
    this part uses fractions.Fraction; no floating-point approximation enters.
2.  It verifies the shifted self-sampling quadrature identities for several
    scales and phases, again exactly.
3.  It evaluates the half-integer Fourier alias series at high precision and
    compares it with the exact first quadrature defect.
4.  It constructs the Rvachev--Appell polynomials from their Bernoulli
    cumulants, checks their roots, and creates the tables and figures used by
    the accompanying LaTeX report.

The only non-standard packages are mpmath, sympy, and matplotlib.  They are
used solely for high-precision numerics, exact symbolic polynomial algebra,
and figures.  The quadrature identities themselves are verified with rational
arithmetic.
"""

from __future__ import annotations

import argparse
import csv
from functools import lru_cache
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
from typing import Iterable

import mpmath as mp
import sympy as sp

# Matplotlib is imported lazily in make_figures() so that exact verification can
# be run on a headless machine without importing a plotting backend.


# ---------------------------------------------------------------------------
# Exact moments and exact dyadic Fabius/up values
# ---------------------------------------------------------------------------


def thue_morse_sign(n: int) -> int:
    """Return epsilon_n = (-1)^(binary digit sum of n)."""

    if n < 0:
        raise ValueError("the Thue--Morse index must be nonnegative")
    return -1 if n.bit_count() & 1 else 1


@lru_cache(maxsize=None)
def even_moments(max_index: int) -> tuple[Fraction, ...]:
    """Return c_j = integral x^(2j) up(x) dx for 0 <= j <= max_index.

    The recurrence is

      (2j+1)(2^(2j)-1)c_j = sum_{k<j} binom(2j+1,2k)c_k.

    It is the exact rational recurrence in the primary ProveIt exposition.
    """

    if max_index < 0:
        return tuple()
    values = [Fraction(1)]
    for j in range(1, max_index + 1):
        numerator = sum(
            Fraction(comb(2 * j + 1, 2 * k)) * values[k]
            for k in range(j)
        )
        denominator = (2 * j + 1) * (2 ** (2 * j) - 1)
        values.append(numerator / denominator)
    return tuple(values)


@lru_cache(maxsize=None)
def fabius_dyadic(a: int, n: int) -> Fraction:
    """Return the exact value F(a/2^n), 0 <= a <= 2^n.

    This is the finite moment--Thue--Morse formula

      F(a/2^n) = 2^{-n(n+1)/2}/n! *
        sum_{h<a} epsilon_h sum_k binom(n,2k)
        (2a-2h-1)^{n-2k} c_k.

    The formula is intentionally implemented directly: it is slower than the
    highest-bit evaluator but mirrors the theorem used in the report and makes
    the arithmetic provenance of every quadrature weight transparent.
    """

    if n < 0 or a < 0 or a > 2**n:
        raise ValueError("require n >= 0 and 0 <= a <= 2^n")
    moments = even_moments(n // 2)
    outer = Fraction(0)
    for h in range(a):
        inner = Fraction(0)
        for k in range(n // 2 + 1):
            inner += (
                Fraction(comb(n, 2 * k))
                * (2 * a - 2 * h - 1) ** (n - 2 * k)
                * moments[k]
            )
        outer += thue_morse_sign(h) * inner
    return outer / (factorial(n) * 2 ** (n * (n + 1) // 2))


@lru_cache(maxsize=None)
def up_dyadic(numerator: int, denominator_power: int) -> Fraction:
    """Return up(numerator/2^denominator_power) exactly.

    On [-1,1], evenness and F(x)=up(x-1) imply

      up(x) = F(1-|x|).
    """

    if denominator_power < 0:
        raise ValueError("denominator_power must be nonnegative")
    denominator = 2**denominator_power
    if abs(numerator) >= denominator:
        return Fraction(0)
    return fabius_dyadic(denominator - abs(numerator), denominator_power)


def true_moment(degree: int) -> Fraction:
    """Return integral x^degree up(x) dx exactly."""

    if degree < 0:
        raise ValueError("degree must be nonnegative")
    if degree & 1:
        return Fraction(0)
    return even_moments(degree // 2)[degree // 2]


def shifted_quadrature_moment(
    scale: int, degree: int, shift_numerator: int = 0, shift_power: int = 0
) -> Fraction:
    """Evaluate the shifted self-sampling rule on x^degree exactly.

    The mesh is h=2^{-scale}; the phase is theta=shift_numerator/2^shift_power.
    Thus the nodes are

      x_k = (2^shift_power*k + shift_numerator) / 2^(scale+shift_power)

    and the weights are h*up(x_k).  Compact support makes the sum finite.
    """

    if scale < 0 or shift_power < 0:
        raise ValueError("scale and shift_power must be nonnegative")
    d = scale + shift_power
    denominator = 2**d
    step_multiplier = 2**shift_power

    # The support restriction |x_k|<1 implies approximately 2^(scale+1)
    # contributing integers.  The two extra endpoints make the loop robust for
    # every phase; up vanishes at |x|=1.
    total = Fraction(0)
    for k in range(-2**scale - 2, 2**scale + 3):
        numerator = step_multiplier * k + shift_numerator
        if abs(numerator) < denominator:
            x = Fraction(numerator, denominator)
            total += (
                Fraction(1, 2**scale)
                * up_dyadic(numerator, d)
                * x**degree
            )
    return total


def nonzero_node_count(scale: int, shift_numerator: int, shift_power: int) -> int:
    """Count strictly positive weights in a shifted rule."""

    d = scale + shift_power
    denominator = 2**d
    step_multiplier = 2**shift_power
    count = 0
    for k in range(-2**scale - 2, 2**scale + 3):
        numerator = step_multiplier * k + shift_numerator
        if abs(numerator) < denominator and up_dyadic(numerator, d) > 0:
            count += 1
    return count


# ---------------------------------------------------------------------------
# High-precision Fourier product and the first alias defect
# ---------------------------------------------------------------------------


def sinc_pi(x: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Normalized sinc sin(pi*x)/(pi*x), with the removable value at zero."""

    if x == 0:
        return mp.mpf(1)
    return mp.sin(mp.pi * x) / (mp.pi * x)


def phi(x: mp.mpf | mp.mpc, tail_digits: int = 20) -> mp.mpf | mp.mpc:
    """Evaluate Phi(x)=prod_{j>=0}sinc_pi(x/2^j).

    The loop stops when the first omitted argument is so small that the
    quadratic logarithmic tail is far below the working precision.
    """

    x = mp.mpc(x)
    product = mp.mpc(1)
    # A conservative threshold based on |log sinc(y)|=O(|y|^2).
    threshold = mp.power(10, -(mp.mp.dps + tail_digits) / 2)
    for j in range(2000):
        product *= sinc_pi(x / (2**j))
        if abs(x) / (2 ** (j + 1)) < threshold:
            return product
    raise RuntimeError("Fourier product did not converge within 2000 factors")


def first_alias_defect(
    scale: int, theta: mp.mpf, positive_odd_terms: int = 80
) -> mp.mpf:
    """Evaluate the exact first-error spectral series.

    For r=scale+1,

      Q_{scale,theta}(x^r)-mu_r
       = -r!/[(-2*pi*i)^r 2^(scale*r)]
         sum_{ell odd, ell != 0} Phi(ell/2)e^(2*pi*i*ell*theta)/ell^r.

    Positive and negative frequencies are paired explicitly.  The half-integer
    Fourier product decays very rapidly, so a modest number of odd frequencies
    gives far more digits than displayed in the report.
    """

    r = scale + 1
    spectral_sum = mp.mpc(0)
    for j in range(positive_odd_terms):
        ell = 2 * j + 1
        value = phi(mp.mpf(ell) / 2)
        angle = 2 * mp.pi * ell * theta
        if r & 1:
            spectral_sum += 2j * value * mp.sin(angle) / (mp.mpf(ell) ** r)
        else:
            spectral_sum += 2 * value * mp.cos(angle) / (mp.mpf(ell) ** r)
    prefactor = -mp.factorial(r) / (
        (-2 * mp.pi * 1j) ** r * 2 ** (scale * r)
    )
    return mp.re(prefactor * spectral_sum)


def first_harmonic_tail_ratio(r: int, positive_odd_terms: int = 120) -> mp.mpf:
    """Return the absolute tail / first-harmonic ratio in the r-th defect."""

    if r < 1:
        raise ValueError("r must be positive")
    first = abs(phi(mp.mpf("0.5")))
    tail = mp.mpf(0)
    for j in range(1, positive_odd_terms):
        ell = 2 * j + 1
        tail += abs(phi(mp.mpf(ell) / 2)) / (mp.mpf(ell) ** r)
    return tail / first


# ---------------------------------------------------------------------------
# Rvachev--Appell polynomials
# ---------------------------------------------------------------------------


X = sp.symbols("x")


def cumulant(order: int) -> sp.Rational:
    """Return the exact cumulant kappa_order of the up distribution."""

    if order < 1:
        raise ValueError("order must be positive")
    if order & 1:
        return sp.Rational(0)
    j = order // 2
    return (
        sp.bernoulli(2 * j)
        * sp.Rational(2 ** (2 * j), 2 * j * (2 ** (2 * j) - 1))
    )


def appell_polynomials(max_degree: int) -> list[sp.Expr]:
    """Construct A_n from exp(x z)/M(z) by the cumulant recurrence."""

    if max_degree < 0:
        raise ValueError("max_degree must be nonnegative")
    polynomials: list[sp.Expr] = [sp.Integer(1)]
    for n in range(max_degree):
        next_polynomial = X * polynomials[n]
        for j in range(1, n + 2):
            next_polynomial -= (
                sp.binomial(n, j - 1)
                * cumulant(j)
                * polynomials[n - j + 1]
            )
        polynomials.append(sp.expand(next_polynomial))
    return polynomials


def nonreal_root_count(polynomial: sp.Expr, tolerance: float = 1e-20) -> int:
    """Count nonreal zeros numerically, with high-precision SymPy roots."""

    degree = sp.degree(polynomial, X)
    if degree <= 0:
        return 0
    roots = sp.nroots(polynomial, n=55, maxsteps=300)
    return sum(abs(complex(root).imag) > tolerance for root in roots)


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------


def fraction_tex(value: Fraction) -> str:
    """Convert a Fraction to compact LaTeX."""

    if value.denominator == 1:
        return str(value.numerator)
    return rf"\frac{{{value.numerator}}}{{{value.denominator}}}"


def sympy_tex(expr: sp.Expr) -> str:
    """LaTeX with a few typography choices suited to the report."""

    return sp.latex(expr, order="lex")


def write_tables(output_directory: Path, max_scale: int = 8) -> None:
    """Write CSV and LaTeX tables used in the report."""

    output_directory.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = 90

    # Exact phase-adapted quadrature table.
    rows: list[dict[str, str]] = []
    for n in range(max_scale + 1):
        if n & 1:
            shift_numerator, shift_power, phase_label = 1, 2, r"1/4"
        else:
            shift_numerator, shift_power, phase_label = 0, 0, r"0"
        exact_through = n + 1
        first_test_degree = n + 2
        defect = shifted_quadrature_moment(
            n, first_test_degree, shift_numerator, shift_power
        ) - true_moment(first_test_degree)
        # Verify all promised moments exactly before writing the row.
        for degree in range(exact_through + 1):
            observed = shifted_quadrature_moment(
                n, degree, shift_numerator, shift_power
            )
            assert observed == true_moment(degree), (
                n,
                degree,
                observed,
                true_moment(degree),
            )
        rows.append(
            {
                "N": str(n),
                "phase": phase_label,
                "nodes": str(
                    nonzero_node_count(n, shift_numerator, shift_power)
                ),
                "exact_degree": str(exact_through),
                "next_defect_fraction": str(defect),
                "next_defect_decimal": mp.nstr(
                    mp.mpf(defect.numerator) / defect.denominator, 8
                ),
            }
        )

    with (output_directory / "quadrature_table.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    with (output_directory / "quadrature_table.tex").open(
        "w", encoding="utf-8"
    ) as handle:
        handle.write("% Generated exactly by experiments.py\n")
        handle.write("\\begin{tabular}{@{}rrrrr@{}}\n")
        handle.write("\\toprule\n")
        handle.write(
            "$N$ & phase $\\theta_N$ & positive nodes & proved degree & "
            "$Q_{N,\\theta_N}(x^{N+2})-\\mu_{N+2}$\\\\\n"
        )
        handle.write("\\midrule\n")
        for row in rows:
            defect = Fraction(row["next_defect_fraction"])
            handle.write(
                f"{row['N']} & ${row['phase']}$ & {row['nodes']} & "
                f"{row['exact_degree']} & ${fraction_tex(defect)}$\\\\\n"
            )
        handle.write("\\bottomrule\n\\end{tabular}\n")

    # A compact display version avoids stacking very tall exact fractions in
    # the PDF.  The exact numerators and denominators remain in the CSV and in
    # quadrature_table.tex.
    with (output_directory / "quadrature_table_display.tex").open(
        "w", encoding="utf-8"
    ) as handle:
        handle.write("% Generated by experiments.py; exact values are in the CSV\n")
        handle.write("\\begin{tabular}{@{}rrrrr@{}}\n\\toprule\n")
        handle.write(
            "$N$ & phase $\\theta_N$ & positive nodes & proved degree & "
            "next defect (decimal display)\\\\\n"
        )
        handle.write("\\midrule\n")
        for row in rows:
            handle.write(
                f"{row['N']} & ${row['phase']}$ & {row['nodes']} & "
                f"{row['exact_degree']} & ${row['next_defect_decimal']}$\\\\\n"
            )
        handle.write("\\bottomrule\n\\end{tabular}\n")

    # Spectral verification table at a generic dyadic phase theta=1/8.  This
    # phase avoids the parity-forced superconvergence zeros for both parities.
    spectral_rows = []
    theta = mp.mpf(1) / 8
    for n in range(0, 8):
        exact = shifted_quadrature_moment(n, n + 1, 1, 3) - true_moment(n + 1)
        spectral = first_alias_defect(n, theta, 220)
        exact_mp = mp.mpf(exact.numerator) / exact.denominator
        spectral_rows.append(
            {
                "N": n,
                "exact": exact,
                "spectral": spectral,
                "absolute_difference": abs(exact_mp - spectral),
            }
        )
        assert abs(exact_mp - spectral) < mp.mpf("2e-18")

    with (output_directory / "spectral_check.tex").open(
        "w", encoding="utf-8"
    ) as handle:
        handle.write("% Generated by experiments.py at 90 decimal digits\n")
        handle.write("\\begin{tabular}{@{}rrrr@{}}\n\\toprule\n")
        handle.write(
            "$N$ & exact rational defect & spectral series & absolute difference\\\\\n"
        )
        handle.write("\\midrule\n")
        for row in spectral_rows:
            handle.write(
                f"{row['N']} & ${fraction_tex(row['exact'])}$ & "
                f"${mp.nstr(row['spectral'], 10)}$ & "
                f"${mp.nstr(row['absolute_difference'], 3)}$\\\\\n"
            )
        handle.write("\\bottomrule\n\\end{tabular}\n")

    # Compact decimal display for the report; spectral_check.tex retains the
    # exact rational fractions.
    with (output_directory / "spectral_check_display.tex").open(
        "w", encoding="utf-8"
    ) as handle:
        handle.write("% Generated by experiments.py at 90 decimal digits\n")
        handle.write("\\begin{tabular}{@{}rrrr@{}}\n\\toprule\n")
        handle.write(
            "$N$ & exact defect (decimal) & spectral series & "
            "absolute difference\\\\\n"
        )
        handle.write("\\midrule\n")
        for row in spectral_rows:
            exact_mp = mp.mpf(row["exact"].numerator) / row["exact"].denominator
            handle.write(
                f"{row['N']} & ${mp.nstr(exact_mp, 12)}$ & "
                f"${mp.nstr(row['spectral'], 12)}$ & "
                f"${mp.nstr(row['absolute_difference'], 3)}$\\\\\n"
            )
        handle.write("\\bottomrule\n\\end{tabular}\n")

    # First-harmonic dominance.
    with (output_directory / "harmonic_tail_table.tex").open(
        "w", encoding="utf-8"
    ) as handle:
        handle.write("% Generated by experiments.py\n")
        handle.write("\\begin{tabular}{@{}rrr@{}}\n\\toprule\n")
        handle.write(
            "$r=N+1$ & $N$ & absolute tail / first harmonic\\\\\n\\midrule\n"
        )
        for r in range(2, 11):
            ratio = first_harmonic_tail_ratio(r)
            handle.write(f"{r} & {r-1} & ${mp.nstr(ratio, 8)}$\\\\\n")
        handle.write("\\bottomrule\n\\end{tabular}\n")

    # Appell polynomials and root counts.
    polynomials = appell_polynomials(30)
    with (output_directory / "appell_polynomials.tex").open(
        "w", encoding="utf-8"
    ) as handle:
        handle.write("% Generated exactly by experiments.py\n")
        handle.write("\\begin{align*}\n")
        for n in range(0, 11):
            line_end = r"\\" if n < 10 else ""
            handle.write(
                rf"A_{{{n}}}(x)&={sympy_tex(polynomials[n])}{line_end}" + "\n"
            )
        handle.write("\\end{align*}\n")

    root_rows = []
    for n in range(1, 31):
        count = nonreal_root_count(polynomials[n])
        root_rows.append((n, count))
    with (output_directory / "appell_root_counts.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.writer(handle)
        writer.writerow(["degree", "nonreal_roots"])
        writer.writerows(root_rows)

    # Exact Sturm count for the first failure of real-rootedness.
    real_roots_a8 = sp.Poly(polynomials[8], X, domain=sp.QQ).count_roots(
        -sp.oo, sp.oo
    )
    assert real_roots_a8 == 4
    with (output_directory / "appell_root_certificate.txt").open(
        "w", encoding="utf-8"
    ) as handle:
        handle.write("A_8 exact polynomial:\n")
        handle.write(str(polynomials[8]) + "\n\n")
        handle.write(
            "SymPy exact Sturm count on (-infinity,+infinity): "
            f"{real_roots_a8} real roots.\n"
        )
        handle.write(
            "Since A_8 has degree 8 and real coefficients, the remaining four "
            "zeros are nonreal and occur in conjugate pairs.\n"
        )


def make_figures(output_directory: Path) -> None:
    """Create three standalone figures, each in its own file."""

    import matplotlib.pyplot as plt

    output_directory.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = 60

    # Figure 1: normalized first-defect profiles.  Each curve is divided by its
    # maximum absolute sampled value so that parity and phase zeros are visible.
    import math

    theta_values = [j / 512 for j in range(513)]
    plt.figure(figsize=(7.2, 4.3))
    for n in range(1, 5):
        r = n + 1
        # Compute the expensive Fourier products only once per frequency.
        coefficients = []
        for j in range(45):
            ell = 2 * j + 1
            coefficients.append(float(mp.re(phi(mp.mpf(ell) / 2))) / ell**r)
        prefactor = -mp.factorial(r) / ((-2 * mp.pi * 1j) ** r * 2 ** (n * r))
        values = []
        for t in theta_values:
            if r & 1:
                spectral = sum(
                    2j * coefficient * math.sin(2 * math.pi * (2 * j + 1) * t)
                    for j, coefficient in enumerate(coefficients)
                )
            else:
                spectral = sum(
                    2 * coefficient * math.cos(2 * math.pi * (2 * j + 1) * t)
                    for j, coefficient in enumerate(coefficients)
                )
            values.append(float(mp.re(prefactor * spectral)))
        scale = max(abs(value) for value in values)
        normalized = [value / scale for value in values]
        plt.plot(theta_values, normalized, label=rf"$N={n}$")
    plt.xlabel(r"phase $\theta$")
    plt.ylabel("normalized first defect")
    plt.title("Parity-forced superconvergent phases")
    plt.grid(True, alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_directory / "defect_profiles.png", dpi=220)
    plt.close()

    # Figure 2: exact positive weights of a representative phase-adapted rule.
    n = 5
    shift_numerator, shift_power = 1, 2
    d = n + shift_power
    xs = []
    weights = []
    for k in range(-2**n - 2, 2**n + 3):
        numerator = 2**shift_power * k + shift_numerator
        if abs(numerator) < 2**d:
            weight = Fraction(1, 2**n) * up_dyadic(numerator, d)
            if weight:
                xs.append(float(Fraction(numerator, 2**d)))
                weights.append(float(weight))
    plt.figure(figsize=(7.2, 4.3))
    plt.vlines(xs, 0, weights)
    plt.xlabel("quadrature node")
    plt.ylabel("exact positive weight (decimal display)")
    plt.title(r"Phase-adapted self-sampling weights: $N=5$, $\theta=1/4$")
    plt.tight_layout()
    plt.savefig(output_directory / "quadrature_weights.png", dpi=220)
    plt.close()

    # Figure 3: complex roots of the Rvachev--Appell polynomials A_1,...,A_20.
    polynomials = appell_polynomials(16)
    plt.figure(figsize=(7.2, 4.8))
    for n in range(1, 17):
        roots = sp.nroots(polynomials[n], n=45, maxsteps=300)
        plt.scatter(
            [float(sp.re(root)) for root in roots],
            [float(sp.im(root)) for root in roots],
            s=10,
            label=None,
        )
    plt.axhline(0, linewidth=0.8)
    plt.xlabel("real part")
    plt.ylabel("imaginary part")
    plt.title(r"Zeros of $A_1,\ldots,A_{16}$: real-rootedness fails at $A_8$")
    plt.tight_layout()
    plt.savefig(output_directory / "appell_roots.png", dpi=220)
    plt.close()


def run_all(output_directory: Path, make_plots: bool = True) -> None:
    """Run exact checks, write tables, and optionally generate figures."""

    write_tables(output_directory)
    if make_plots:
        make_figures(output_directory)
    print(f"Wrote reproducibility outputs to {output_directory}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory for generated tables and figures",
    )
    parser.add_argument(
        "--no-plots",
        action="store_true",
        help="run exact and high-precision checks without matplotlib figures",
    )
    arguments = parser.parse_args()
    run_all(arguments.output, make_plots=not arguments.no_plots)
