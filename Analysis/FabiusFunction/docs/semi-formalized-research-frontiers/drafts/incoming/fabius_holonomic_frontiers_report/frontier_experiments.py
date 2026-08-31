#!/usr/bin/env python3
"""Exact and high-precision experiments for the Fabius--Rvachev
holonomic-rank report.

The script studies finite geometric sinc products

    Phi_{q,N}(z) = product_{j=1}^N sinc(q^j z)

through the signed frequency expansion of z^N Phi_{q,N}.  The important
point is that frequency collisions are detected in *exact arithmetic*.
No tolerance-based clustering is used for the rank calculations.

Outputs
-------
The output directory receives:

* rank_table.csv
    Exact holonomic ranks for q=1/2, q=2/3, and q=(sqrt(5)-1)/2.
* golden_support_N3.csv
    The complete level-3 signed support at the golden overlap parameter.
* golden_recurrence_check.txt
    Exact verification of the experimentally discovered rank recurrence.
* dyadic_ode_coefficients.csv and dyadic_ode_examples.tex
    Exact coefficients of the minimal dyadic differential operators.
* ode_residuals.csv
    Multiprecision residual checks of those operators.
* dyadic_discriminant.csv
    Logarithms of the exact arithmetic-progression discriminants.
* separation_table.csv
    Exact or high-precision minimum spacings of signed sums.
* several PDF/PNG figures used by the report.

Only the standard library, SymPy, mpmath, and matplotlib are required.
The calculations are deterministic.
"""

from __future__ import annotations

import argparse
import csv
import math
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, Iterator, Mapping, MutableMapping, Sequence, Tuple

import matplotlib.pyplot as plt

# Embed TrueType outlines in generated PDF figures.  This avoids Type-3
# plot fonts while preserving deterministic vector graphics.
plt.rcParams["pdf.fonttype"] = 42
plt.rcParams["ps.fonttype"] = 42

import mpmath as mp
import sympy as sp


Frequency = Fraction
GoldenFrequency = Tuple[int, int]  # Represents a + b*q, q^2 = 1-q.


def ensure_directory(path: Path) -> None:
    """Create *path* and its parents if necessary."""

    path.mkdir(parents=True, exist_ok=True)


def write_csv(path: Path, fieldnames: Sequence[str], rows: Iterable[Mapping[str, object]]) -> None:
    """Write rows to a UTF-8 CSV file with a stable column order."""

    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


# ---------------------------------------------------------------------------
# Exact signed-frequency aggregation
# ---------------------------------------------------------------------------


def rational_signed_support(q: Fraction, n_max: int) -> list[Dict[Frequency, int]]:
    """Return the exact signed supports through level ``n_max``.

    At level N the dictionary maps

        omega = sum_{j=1}^N epsilon_j q^j

    to the aggregated coefficient product(epsilon_j).  A zero aggregate is
    removed immediately.  The number of dictionary entries is therefore the
    exact minimal holonomic rank proved in the report.
    """

    support: Dict[Frequency, int] = {Fraction(0): 1}
    result: list[Dict[Frequency, int]] = []
    power = Fraction(1)

    for _level in range(1, n_max + 1):
        power *= q
        updated: MutableMapping[Frequency, int] = defaultdict(int)
        for omega, coefficient in support.items():
            # Choosing epsilon=+1 preserves the current coefficient.
            updated[omega + power] += coefficient
            # Choosing epsilon=-1 reverses it.
            updated[omega - power] -= coefficient
        support = {omega: coefficient for omega, coefficient in updated.items() if coefficient != 0}
        result.append(support)

    return result


def golden_powers(n_max: int) -> list[GoldenFrequency]:
    """Return q^j as exact pairs a+b*q for q=(sqrt(5)-1)/2.

    Since q^2=1-q,

        (a+b*q)q = b + (a-b)q.
    """

    powers: list[GoldenFrequency] = [(1, 0)]
    if n_max >= 1:
        powers.append((0, 1))
    for _j in range(2, n_max + 1):
        a, b = powers[-1]
        powers.append((b, a - b))
    return powers


def golden_signed_support(n_max: int) -> list[Dict[GoldenFrequency, int]]:
    """Exact signed supports for the golden overlap parameter."""

    powers = golden_powers(n_max)
    support: Dict[GoldenFrequency, int] = {(0, 0): 1}
    result: list[Dict[GoldenFrequency, int]] = []

    for level in range(1, n_max + 1):
        va, vb = powers[level]
        updated: MutableMapping[GoldenFrequency, int] = defaultdict(int)
        for (a, b), coefficient in support.items():
            updated[(a + va, b + vb)] += coefficient
            updated[(a - va, b - vb)] -= coefficient
        support = {omega: coefficient for omega, coefficient in updated.items() if coefficient != 0}
        result.append(support)

    return result


def golden_distinct_sum_sets(n_max: int) -> list[set[GoldenFrequency]]:
    """All distinct signed sums, without signed cancellation.

    This differs from ``golden_signed_support``: a frequency can be reached by
    several sign words whose parity-weighted coefficients cancel.  The two
    cardinalities quantify unsigned overlap and signed holonomic rank,
    respectively.
    """

    powers = golden_powers(n_max)
    sums: set[GoldenFrequency] = {(0, 0)}
    result: list[set[GoldenFrequency]] = []
    for level in range(1, n_max + 1):
        va, vb = powers[level]
        sums = {(a + sign * va, b + sign * vb) for (a, b) in sums for sign in (-1, +1)}
        result.append(sums)
    return result


def golden_numeric(value: GoldenFrequency, dps: int = 80) -> mp.mpf:
    """Evaluate a+b*q at high precision."""

    mp.mp.dps = dps
    q = (mp.sqrt(5) - 1) / 2
    a, b = value
    return mp.mpf(a) + mp.mpf(b) * q


# ---------------------------------------------------------------------------
# Dyadic minimal differential operator
# ---------------------------------------------------------------------------


def dyadic_operator_polynomial(level: int) -> sp.Poly:
    """Return P_N(D)=prod_{ell=1}^{2^(N-1)}(D^2+(2ell-1)^2/4^N)."""

    if level < 1:
        raise ValueError("level must be positive")
    d = sp.Symbol("D")
    half_rank = 2 ** (level - 1)
    expression = sp.prod(
        d**2 + sp.Rational((2 * ell - 1) ** 2, 4**level)
        for ell in range(1, half_rank + 1)
    )
    return sp.Poly(sp.expand(expression), d, domain=sp.QQ)


def dyadic_thue_morse_terms(level: int) -> Iterator[Tuple[Fraction, int]]:
    """Yield (frequency, Thue--Morse coefficient) for the dyadic expansion."""

    for k in range(2**level):
        frequency = Fraction(2**level - 1 - 2 * k, 2**level)
        coefficient = -1 if k.bit_count() % 2 else 1
        yield frequency, coefficient


def evaluate_even_operator_residual(level: int, z: mp.mpf, dps: int = 100) -> Tuple[mp.mpf, mp.mpf]:
    """Evaluate a normalized residual of P_N(D)E_N at one point.

    E_N is the unscaled Thue--Morse exponential polynomial.  The calculation
    differentiates the exponential sum term by term and combines derivatives
    with the exact rational operator coefficients.  The returned pair is
    (absolute residual, residual divided by the 1-norm of all summands).
    """

    mp.mp.dps = dps
    polynomial = dyadic_operator_polynomial(level)
    # Map derivative degree -> exact coefficient.  Odd degrees are absent.
    coefficients = {monomial[0]: mp.mpf(str(coefficient.p)) / mp.mpf(str(coefficient.q))
                    for monomial, coefficient in polynomial.terms()}

    residual = mp.mpc(0)
    scale = mp.mpf(0)
    for derivative_order, operator_coefficient in coefficients.items():
        derivative_value = mp.mpc(0)
        for frequency, thue_morse in dyadic_thue_morse_terms(level):
            omega = mp.mpf(frequency.numerator) / frequency.denominator
            derivative_value += thue_morse * (1j * omega) ** derivative_order * mp.e ** (1j * omega * z)
        term = operator_coefficient * derivative_value
        residual += term
        scale += abs(term)

    absolute = abs(residual)
    relative = absolute / scale if scale else mp.mpf(0)
    return absolute, relative


# ---------------------------------------------------------------------------
# Separation and discriminant diagnostics
# ---------------------------------------------------------------------------


def minimum_fraction_spacing(values: Iterable[Fraction]) -> Fraction:
    """Minimum positive gap in an exact rational set."""

    ordered = sorted(set(values))
    return min(b - a for a, b in zip(ordered, ordered[1:]))


def minimum_golden_spacing(values: Iterable[GoldenFrequency], dps: int = 100) -> mp.mpf:
    """Minimum positive gap after a high-precision ordering of exact Q(q) values."""

    evaluated = sorted(golden_numeric(value, dps=dps) for value in set(values))
    return min(b - a for a, b in zip(evaluated, evaluated[1:]))


def log_dyadic_discriminant(level: int, dps: int = 100) -> mp.mpf:
    """Log absolute discriminant of the dyadic characteristic polynomial.

    There are n=2^N equally spaced roots with step 2/n on the imaginary axis,
    hence

        |Disc| = (2/n)^(n(n-1)) * product_{j=1}^{n-1} (j!)^2.
    """

    mp.mp.dps = dps
    n = 2**level
    return n * (n - 1) * mp.log(mp.mpf(2) / n) + 2 * mp.log(mp.barnesg(n + 1))


# ---------------------------------------------------------------------------
# Output generation
# ---------------------------------------------------------------------------


def generate_rank_data(output: Path, n_max: int = 25) -> tuple[list[int], list[int], list[int], list[int]]:
    """Generate exact rank tables and return the plotted sequences."""

    # Dyadic and q=2/3 are collision-free; exact dictionaries are nevertheless
    # constructed through level 16 as an independent verification.
    rational_limit = min(n_max, 16)
    dyadic_support = rational_signed_support(Fraction(1, 2), rational_limit)
    two_thirds_support = rational_signed_support(Fraction(2, 3), rational_limit)

    golden_support = golden_signed_support(n_max)
    golden_distinct = golden_distinct_sum_sets(n_max)

    rows = []
    for level in range(1, n_max + 1):
        dyadic_rank = len(dyadic_support[level - 1]) if level <= rational_limit else 2**level
        two_thirds_rank = len(two_thirds_support[level - 1]) if level <= rational_limit else 2**level
        g_support = golden_support[level - 1]
        rows.append(
            {
                "N": level,
                "rank_q_1_2": dyadic_rank,
                "rank_q_2_3": two_thirds_rank,
                "rank_q_golden": len(g_support),
                "distinct_sums_q_golden": len(golden_distinct[level - 1]),
                "max_abs_coefficient_q_golden": max(abs(value) for value in g_support.values()),
                "normalized_entropy_q_golden": f"{math.log(len(g_support), 2) / level:.16g}",
            }
        )

    write_csv(
        output / "rank_table.csv",
        [
            "N",
            "rank_q_1_2",
            "rank_q_2_3",
            "rank_q_golden",
            "distinct_sums_q_golden",
            "max_abs_coefficient_q_golden",
            "normalized_entropy_q_golden",
        ],
        rows,
    )

    # Complete exact N=3 certificate for q=(sqrt(5)-1)/2.
    n3_rows = []
    for (a, b), coefficient in sorted(
        golden_support[2].items(), key=lambda item: float(golden_numeric(item[0]))
    ):
        n3_rows.append(
            {
                "a": a,
                "b": b,
                "frequency_a_plus_bq": f"{mp.nstr(golden_numeric((a, b)), 30)}",
                "aggregated_coefficient": coefficient,
            }
        )
    write_csv(
        output / "golden_support_N3.csv",
        ["a", "b", "frequency_a_plus_bq", "aggregated_coefficient"],
        n3_rows,
    )

    ranks = [1] + [len(support) for support in golden_support]
    recurrence_failures = []
    for level in range(3, n_max + 1):
        expected = 2 * ranks[level - 1] - 2 * ranks[level - 2] + 2 * ranks[level - 3]
        if ranks[level] != expected:
            recurrence_failures.append((level, ranks[level], expected))

    dominant_root = max(
        root for root in sp.nroots(sp.Symbol("x") ** 3 - 2 * sp.Symbol("x") ** 2 + 2 * sp.Symbol("x") - 2)
        if abs(sp.im(root)) < sp.Float("1e-30")
    )
    with (output / "golden_recurrence_check.txt").open("w", encoding="utf-8") as stream:
        stream.write("Golden-ratio signed holonomic-rank experiment\n")
        stream.write("q = (sqrt(5)-1)/2, with exact arithmetic in Z[q]/(q^2+q-1).\n\n")
        stream.write(f"Levels checked: 0 through {n_max}\n")
        stream.write("Ranks: " + ", ".join(str(value) for value in ranks) + "\n")
        stream.write("Candidate recurrence for N>=3:\n")
        stream.write("    r_N = 2 r_{N-1} - 2 r_{N-2} + 2 r_{N-3}.\n")
        stream.write(f"Failures: {recurrence_failures or 'none'}\n")
        stream.write("All surviving coefficients had absolute value 1: "
                     + str(all(max(abs(c) for c in support.values()) == 1 for support in golden_support))
                     + "\n")
        stream.write(f"Dominant characteristic root: {dominant_root}\n")
        stream.write("This file is computational evidence, not a proof of the recurrence.\n")

    return (
        list(range(1, n_max + 1)),
        [2**level for level in range(1, n_max + 1)],
        [len(support) for support in golden_support],
        [len(values) for values in golden_distinct],
    )


def generate_operator_data(output: Path, max_level: int = 5) -> None:
    """Generate exact dyadic operator coefficients and residual checks."""

    coefficient_rows = []
    latex_lines = [
        "% Generated by frontier_experiments.py; do not edit by hand.",
        "\\begin{align*}",
    ]

    for level in range(1, max_level + 1):
        polynomial = dyadic_operator_polynomial(level)
        for monomial, coefficient in polynomial.terms():
            coefficient_rows.append(
                {
                    "N": level,
                    "derivative_order": monomial[0],
                    "coefficient": str(coefficient),
                    "numerator": int(coefficient.p),
                    "denominator": int(coefficient.q),
                }
            )
        if level <= 3:
            latex_lines.append(
                rf"\mathcal P_{{{level}}}(D)&={sp.latex(polynomial.as_expr())}\\"
            )
    latex_lines.append("\\end{align*}")

    write_csv(
        output / "dyadic_ode_coefficients.csv",
        ["N", "derivative_order", "coefficient", "numerator", "denominator"],
        coefficient_rows,
    )
    (output / "dyadic_ode_examples.tex").write_text("\n".join(latex_lines) + "\n", encoding="utf-8")

    residual_rows = []
    for level in range(1, min(max_level, 6) + 1):
        for point in (mp.mpf("0.37"), mp.mpf("1.1"), mp.mpf("2.7")):
            absolute, relative = evaluate_even_operator_residual(level, point, dps=120)
            residual_rows.append(
                {
                    "N": level,
                    "z": mp.nstr(point, 10),
                    "absolute_residual": mp.nstr(absolute, 12),
                    "relative_residual": mp.nstr(relative, 12),
                }
            )
    write_csv(
        output / "ode_residuals.csv",
        ["N", "z", "absolute_residual", "relative_residual"],
        residual_rows,
    )


def generate_discriminant_data(output: Path, max_level: int = 12) -> None:
    """Generate exact-formula discriminant diagnostics."""

    rows = []
    for level in range(1, max_level + 1):
        n = 2**level
        exact_log = log_dyadic_discriminant(level, dps=120)
        asymptotic = (
            n**2 * (mp.log(2) - mp.mpf("1.5"))
            + n * mp.log(mp.pi * n)
            - mp.log(n) / 6
            + 2 * mp.diff(lambda s: mp.zeta(s), -1)
        )
        rows.append(
            {
                "N": level,
                "rank_n": n,
                "log_abs_discriminant": mp.nstr(exact_log, 24),
                "two_term_asymptotic": mp.nstr(asymptotic, 24),
                "difference": mp.nstr(exact_log - asymptotic, 16),
            }
        )
    write_csv(
        output / "dyadic_discriminant.csv",
        ["N", "rank_n", "log_abs_discriminant", "two_term_asymptotic", "difference"],
        rows,
    )


def generate_separation_data(output: Path, max_level: int = 16) -> tuple[list[int], list[float], list[float], list[float]]:
    """Compute exact/high-precision minimum signed-sum spacings."""

    dyadic = rational_signed_support(Fraction(1, 2), max_level)
    two_thirds = rational_signed_support(Fraction(2, 3), max_level)
    golden_sets = golden_distinct_sum_sets(max_level)

    rows = []
    dyadic_logs: list[float] = []
    two_thirds_logs: list[float] = []
    golden_logs: list[float] = []

    for level in range(1, max_level + 1):
        d_gap = minimum_fraction_spacing(dyadic[level - 1].keys())
        t_gap = minimum_fraction_spacing(two_thirds[level - 1].keys())
        g_gap = minimum_golden_spacing(golden_sets[level - 1], dps=140)

        d_log = -math.log2(float(d_gap))
        t_log = -math.log2(float(t_gap))
        g_log = float(-mp.log(g_gap, 2))
        dyadic_logs.append(d_log)
        two_thirds_logs.append(t_log)
        golden_logs.append(g_log)

        rows.append(
            {
                "N": level,
                "dyadic_gap_exact": str(d_gap),
                "q_2_3_gap_exact": str(t_gap),
                "golden_distinct_gap_80_digits": mp.nstr(g_gap, 80),
                "minus_log2_dyadic_gap": f"{d_log:.16g}",
                "minus_log2_q_2_3_gap": f"{t_log:.16g}",
                "minus_log2_golden_gap": f"{g_log:.16g}",
            }
        )

    write_csv(
        output / "separation_table.csv",
        [
            "N",
            "dyadic_gap_exact",
            "q_2_3_gap_exact",
            "golden_distinct_gap_80_digits",
            "minus_log2_dyadic_gap",
            "minus_log2_q_2_3_gap",
            "minus_log2_golden_gap",
        ],
        rows,
    )
    return list(range(1, max_level + 1)), dyadic_logs, two_thirds_logs, golden_logs


def save_figure(fig: plt.Figure, output: Path, stem: str) -> None:
    """Save a figure in vector PDF and high-resolution PNG formats."""

    fig.tight_layout()
    fig.savefig(output / f"{stem}.pdf", bbox_inches="tight")
    fig.savefig(output / f"{stem}.png", dpi=220, bbox_inches="tight")
    plt.close(fig)


def generate_figures(
    output: Path,
    rank_data: tuple[list[int], list[int], list[int], list[int]],
    separation_data: tuple[list[int], list[float], list[float], list[float]],
) -> None:
    """Create the figures included in the report."""

    levels, full_ranks, golden_ranks, golden_distinct = rank_data

    fig, axis = plt.subplots(figsize=(7.2, 4.6))
    axis.plot(levels, [math.log2(value) for value in full_ranks], marker="o", label=r"collision-free rank $2^N$")
    axis.plot(levels, [math.log2(value) for value in golden_distinct], marker="s", label="golden distinct sums")
    axis.plot(levels, [math.log2(value) for value in golden_ranks], marker="^", label="golden signed rank")
    axis.set_xlabel("truncation level N")
    axis.set_ylabel(r"$\log_2$ cardinality")
    axis.set_title("Holonomic rank and exact-overlap compression")
    axis.grid(True, alpha=0.3)
    axis.legend()
    save_figure(fig, output, "rank_growth")

    fig, axis = plt.subplots(figsize=(7.2, 4.6))
    axis.plot(levels, [math.log(value) / level for level, value in zip(levels, golden_ranks)], marker="o", label=r"$N^{-1}\log r_N$")
    axis.axhline(math.log(2), linestyle="--", label=r"collision-free value $\log 2$")
    dominant = 1.5436890126920764
    axis.axhline(math.log(dominant), linestyle=":", label="candidate golden limit")
    axis.set_xlabel("truncation level N")
    axis.set_ylabel("normalized logarithmic rank")
    axis.set_title("Golden-overlap holonomic entropy")
    axis.grid(True, alpha=0.3)
    axis.legend()
    save_figure(fig, output, "golden_entropy")

    # Thue--Morse frequency coefficients at one moderate dyadic level.
    level = 7
    terms = sorted(dyadic_thue_morse_terms(level))
    frequencies = [float(omega) for omega, _coefficient in terms]
    coefficients = [coefficient for _omega, coefficient in terms]
    fig, axis = plt.subplots(figsize=(8.0, 4.2))
    markerline, stemlines, baseline = axis.stem(frequencies, coefficients, basefmt=" ")
    axis.set_xlabel("frequency")
    axis.set_ylabel("aggregated coefficient")
    axis.set_yticks([-1, 0, 1])
    axis.set_title(r"Dyadic level 7: Thue--Morse signs on the odd frequency lattice")
    axis.grid(True, axis="x", alpha=0.2)
    save_figure(fig, output, "dyadic_thue_morse_spectrum")

    # Direct comparison of the level-3 top-derivative atomic supports.
    dyadic_n3 = sorted(dyadic_thue_morse_terms(3))
    golden_n3 = golden_signed_support(3)[2]
    golden_terms = sorted(
        ((float(golden_numeric(omega)), coefficient) for omega, coefficient in golden_n3.items()),
        key=lambda pair: pair[0],
    )
    fig, axis = plt.subplots(figsize=(7.4, 4.4))
    axis.scatter([float(value) for value, _ in dyadic_n3], [coefficient for _, coefficient in dyadic_n3], marker="o", label="q=1/2: rank 8")
    axis.scatter([value for value, _ in golden_terms], [coefficient for _, coefficient in golden_terms], marker="x", label="golden q: rank 6")
    axis.axvline(0.0, linewidth=0.8)
    axis.set_xlabel("atomic knot / exponential frequency")
    axis.set_ylabel("signed coefficient")
    axis.set_yticks([-1, 0, 1])
    axis.set_title("First exact-overlap rank defect")
    axis.grid(True, alpha=0.25)
    axis.legend()
    save_figure(fig, output, "level3_rank_defect")

    sep_levels, dyadic_logs, two_thirds_logs, golden_logs = separation_data
    fig, axis = plt.subplots(figsize=(7.2, 4.6))
    axis.plot(sep_levels, dyadic_logs, marker="o", label="q=1/2")
    axis.plot(sep_levels, two_thirds_logs, marker="s", label="q=2/3")
    axis.plot(sep_levels, golden_logs, marker="^", label="golden q (distinct sums)")
    axis.set_xlabel("truncation level N")
    axis.set_ylabel(r"$-\log_2 \Delta_N(q)$")
    axis.set_title("Frequency separation and near-overlap conditioning")
    axis.grid(True, alpha=0.3)
    axis.legend()
    save_figure(fig, output, "frequency_separation")


def write_readme(output: Path) -> None:
    """Write reproducibility notes for the numerical package."""

    text = """# Numerical experiment package

Run from this directory with

```bash
python frontier_experiments.py --output-dir data
```

The report build uses the already generated tables and figures under `data/`.
All holonomic-rank and collision computations use exact rational or exact
quadratic-field arithmetic. Floating point is used only for presentation,
minimum-gap ordering after exact deduplication, ODE residual diagnostics, and
plots.

Tested with Python 3.13, SymPy 1.14, mpmath 1.3, and matplotlib 3.10.
The golden-ratio recurrence reported by the script is explicitly classified in
the paper as computational evidence/conjecture, not as a proved theorem.
"""
    (output / "NUMERICAL_README.md").write_text(text, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("data"),
        help="directory for generated tables and figures (default: data)",
    )
    parser.add_argument(
        "--rank-levels",
        type=int,
        default=25,
        help="maximum level for exact rank calculations (default: 25)",
    )
    args = parser.parse_args()

    output = args.output_dir.resolve()
    ensure_directory(output)

    rank_data = generate_rank_data(output, n_max=args.rank_levels)
    generate_operator_data(output, max_level=5)
    generate_discriminant_data(output, max_level=12)
    separation_data = generate_separation_data(output, max_level=16)
    generate_figures(output, rank_data, separation_data)
    write_readme(output.parent)

    print(f"Generated experiment outputs in {output}")


if __name__ == "__main__":
    main()
