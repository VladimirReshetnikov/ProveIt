#!/usr/bin/env python3
"""Exact experiments for the repeated signed Thue--Morse sum table.

This script accompanies the article

    Diagonal Polynomials and Dyadic Block Geometry in Repeated
    Thue--Morse Prefix Summation.

It uses exact integer/rational arithmetic.  SymPy is used only for symbolic
polynomial expansion and factorization; all checks of the discrete table are
performed independently with Python integers.

The main notation is as follows.

* eps(j) = (-1)^(binary digit sum of j).
* sigma_r(q) is the r-fold inclusive prefix sum of eps.
* s[n,k] is the table from the Wolfram Language program in the prompt.
* q = k-n-1 is the shifted column coordinate.
* D_q(x) is the polynomial satisfying s[n,n+q+1] = D_q(n).

The central closed formula is

    D_q(x) = sum_{j=0}^{floor(q/2)} eps(j)
             * rising_factorial(2*x, q-2*j)/(q-2*j)!.

Run this file directly to reproduce the verification report, CSV tables, and
normalized row-pulse figure used in the article.
"""

from __future__ import annotations

import argparse
import csv
import math
import platform
import shutil
from dataclasses import dataclass
from functools import lru_cache, reduce
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import sympy as sp

X = sp.Symbol("x")


def tm_sign(n: int) -> int:
    """Return the signed Thue--Morse value eps(n) in {+1,-1}."""

    if n < 0:
        raise ValueError("tm_sign expects n >= 0")
    return -1 if n.bit_count() & 1 else 1


def multiset_binomial(alpha: int, m: int) -> int:
    """Coefficient of z^m in (1-z)^(-alpha), for alpha,m >= 0.

    This convention handles alpha=0 without invoking a generalized binomial
    routine: the series is then 1, so only m=0 has a nonzero coefficient.
    """

    if alpha < 0 or m < 0:
        raise ValueError("multiset_binomial expects nonnegative arguments")
    if m == 0:
        return 1
    if alpha == 0:
        return 0
    return math.comb(alpha + m - 1, m)


@lru_cache(maxsize=None)
def diagonal_polynomial(q: int) -> sp.Poly:
    """Return D_q(x) as an exact SymPy polynomial over the rationals."""

    if q < 0:
        raise ValueError("q must be nonnegative")
    expression = sp.Integer(0)
    for j in range(q // 2 + 1):
        m = q - 2 * j
        expression += tm_sign(j) * sp.rf(2 * X, m) / sp.factorial(m)
    return sp.Poly(sp.expand(expression), X, domain=sp.QQ)


def diagonal_value(q: int, n: int) -> int:
    """Evaluate D_q(n) by the sparse binomial sum, using Python integers."""

    if q < 0 or n < 0:
        raise ValueError("q and n must be nonnegative")
    return sum(
        tm_sign(j) * multiset_binomial(2 * n, q - 2 * j)
        for j in range(q // 2 + 1)
    )


def closed_table_entry(n: int, k: int) -> int:
    """Evaluate the table element s[n,k] from the closed diagonal formula."""

    if n < 0 or k < 0:
        raise ValueError("n and k must be nonnegative")
    q = k - n - 1
    return 0 if q < 0 else diagonal_value(q, n)


def iterated_prefix_row(order: int, max_index: int) -> list[int]:
    """Compute sigma_order(0..max_index) by literal repeated prefix sums."""

    if order < 0 or max_index < 0:
        raise ValueError("order and max_index must be nonnegative")
    row = [tm_sign(j) for j in range(max_index + 1)]
    for _ in range(order):
        running = 0
        next_row: list[int] = []
        for value in row:
            running += value
            next_row.append(running)
        row = next_row
    return row


def reference_table_entry(n: int, k: int) -> int:
    """Evaluate s[n,k] through the independent repeated-prefix definition."""

    q = k - n - 1
    if q < 0:
        return 0
    return iterated_prefix_row(2 * n + 1, q)[q]


@lru_cache(maxsize=None)
def pulse_coefficients(order: int) -> tuple[int, ...]:
    """Coefficients of A_order(z) = product_{j=1}^{order-1}(1+...+z^(2^j-1)).

    The convolution with each all-ones factor is implemented by a sliding
    window, so producing a full dyadic pulse is linear in the output size.
    """

    if order < 1:
        raise ValueError("order must be at least 1")
    coeffs = [1]
    for j in range(1, order):
        width = 1 << j
        out_length = len(coeffs) + width - 1
        out = [0] * out_length
        window_sum = 0
        for index in range(out_length):
            if index < len(coeffs):
                window_sum += coeffs[index]
            if index - width >= 0:
                window_sum -= coeffs[index - width]
            out[index] = window_sum
        coeffs = out
    return tuple(coeffs)


def block_prefix_value(order: int, q: int) -> int:
    """Evaluate sigma_order(q) using the exact signed dyadic block law."""

    if order < 1 or q < 0:
        raise ValueError("order >= 1 and q >= 0 are required")
    block_size = 1 << order
    block, residue = divmod(q, block_size)
    pulse = pulse_coefficients(order)
    coefficient = pulse[residue] if residue < len(pulse) else 0
    return tm_sign(block) * coefficient


def block_table_entry(n: int, k: int) -> int:
    """Evaluate s[n,k] by reducing q=k-n-1 to one dyadic pulse block."""

    q = k - n - 1
    if q < 0:
        return 0
    return block_prefix_value(2 * n + 1, q)


def half_grid_root_indices(q: int) -> list[int]:
    """Return all m >= 0 for which D_q(m/2)=0.

    The theorem in the article gives the exact criterion

        q mod 2^(m+1) >= 2^(m+1) - (m+1).

    No m >= q can satisfy it when q > 0, so the finite scan is complete.
    """

    if q < 0:
        raise ValueError("q must be nonnegative")
    if q == 0:
        return []
    roots: list[int] = []
    for m in range(q):
        block_size = 1 << (m + 1)
        if q % block_size >= block_size - (m + 1):
            roots.append(m)
    return roots


def half_grid_sample(q: int, m: int) -> int:
    """Evaluate D_q(m/2) exactly from K(z^2)/(1-z)^m."""

    if q < 0 or m < 0:
        raise ValueError("q and m must be nonnegative")
    return sum(
        tm_sign(j) * multiset_binomial(m, q - 2 * j)
        for j in range(q // 2 + 1)
    )


def negative_half_grid_sample(q: int, m: int) -> int:
    """Evaluate D_q(-m/2) by a finite backward difference of eps.

    For m >= 1, the diagonal generating function gives

        D_q(-m/2) = [z^q] K(z) (1-z)^(m-1)
                    = sum_j (-1)^j C(m-1,j) eps(q-j),

    where eps(t)=0 for t<0.  This is an exact integer computation.
    """

    if q < 0 or m < 1:
        raise ValueError("q >= 0 and m >= 1 are required")
    return sum(
        (-1) ** j * math.comb(m - 1, j) * tm_sign(q - j)
        for j in range(min(m - 1, q) + 1)
    )


def predicted_minimal_denominator(q: int) -> int:
    """Least positive integer clearing all monomial coefficients of D_q."""

    if q < 0:
        raise ValueError("q must be nonnegative")
    c = (q + 1) // 2
    two_adic_factorial = 0
    value = math.factorial(q)
    while value and value % 2 == 0:
        two_adic_factorial += 1
        value //= 2
    return math.factorial(q) // (1 << min(two_adic_factorial, c))


def actual_minimal_denominator(poly: sp.Poly) -> int:
    """LCM of reduced denominators of all coefficients of a QQ polynomial."""

    denominators = [int(coefficient.q) for coefficient in poly.all_coeffs()]
    return reduce(math.lcm, denominators, 1)


def recurrence_entry(n: int, k: int) -> int:
    """Evaluate the right side of the user's two-prefix recurrence."""

    if n < 1:
        raise ValueError("the recurrence comparison requires n >= 1")
    return sum((k - j) * closed_table_entry(n - 1, j) for j in range(k))


@dataclass(frozen=True)
class VerificationSummary:
    max_n: int
    max_k: int
    max_q: int
    max_half_index: int
    denominator_max_q: int


def verify_identities(summary: VerificationSummary) -> list[str]:
    """Run independent exact checks and return human-readable status lines."""

    lines: list[str] = []

    # 1. Compare the closed formula with literal repeated prefix summation.
    for n in range(summary.max_n + 1):
        for k in range(summary.max_k + 1):
            lhs = closed_table_entry(n, k)
            rhs = reference_table_entry(n, k)
            assert lhs == rhs, ("prefix comparison", n, k, lhs, rhs)
    lines.append(
        f"PASS: closed formula = literal repeated prefix sums for "
        f"0 <= n <= {summary.max_n}, 0 <= k <= {summary.max_k}."
    )

    # 2. Compare with the exact signed block law.
    for n in range(summary.max_n + 1):
        for k in range(summary.max_k + 1):
            lhs = closed_table_entry(n, k)
            rhs = block_table_entry(n, k)
            assert lhs == rhs, ("block comparison", n, k, lhs, rhs)
    lines.append(
        f"PASS: closed formula = signed dyadic block formula on the same grid."
    )

    # 3. Verify the user's fallback recurrence wherever n >= 1.
    for n in range(1, summary.max_n + 1):
        for k in range(summary.max_k + 1):
            lhs = closed_table_entry(n, k)
            rhs = recurrence_entry(n, k)
            assert lhs == rhs, ("table recurrence", n, k, lhs, rhs)
    lines.append("PASS: the weighted recurrence reproduces every tested table entry.")

    # 4. Check symbolic polynomial evaluation against integer formula.
    for q in range(summary.max_q + 1):
        poly = diagonal_polynomial(q)
        for n in range(summary.max_n + 1):
            lhs = int(poly.eval(n))
            rhs = diagonal_value(q, n)
            assert lhs == rhs, ("polynomial evaluation", q, n, lhs, rhs)
    lines.append(
        f"PASS: D_q(n) matches the sparse integer formula for 0 <= q <= {summary.max_q}."
    )

    # 5. Check the exact nonnegative half-grid root criterion.
    for q in range(summary.max_q + 1):
        predicted = set(half_grid_root_indices(q))
        for m in range(summary.max_half_index + 1):
            actual_zero = half_grid_sample(q, m) == 0
            predicted_zero = m in predicted
            assert actual_zero == predicted_zero, (
                "half-grid root criterion",
                q,
                m,
                half_grid_sample(q, m),
                predicted_zero,
            )
    lines.append(
        f"PASS: exact half-grid root criterion for 0 <= q <= {summary.max_q}, "
        f"0 <= m <= {summary.max_half_index}."
    )

    # 6. Check negative half-grid finite differences against the polynomial.
    negative_m_max = 16
    for q in range(summary.max_q + 1):
        poly = diagonal_polynomial(q)
        for m in range(1, negative_m_max + 1):
            lhs = poly.eval(sp.Rational(-m, 2))
            rhs = negative_half_grid_sample(q, m)
            assert lhs == rhs, ("negative half-grid", q, m, lhs, rhs)
    lines.append(
        f"PASS: negative half-grid finite-difference formula for "
        f"0 <= q <= {summary.max_q}, 1 <= m <= {negative_m_max}."
    )

    # 7. Check the infinite trailing-ones family of negative integer roots.
    for a in range(2, 10):
        modulus = 1 << a
        for block in range(4):
            q = block * modulus + modulus - 1
            for ell in range(1, a, 2):
                m = 1 << (ell + 1)  # -m/2 = -2^ell
                assert negative_half_grid_sample(q, m) == 0, (
                    "trailing-ones root", a, block, q, ell
                )
    lines.append(
        "PASS: trailing-ones negative-root family for a=2..9 and four blocks."
    )

    # 8. Check the exact minimal coefficient denominator.
    for q in range(summary.denominator_max_q + 1):
        actual = actual_minimal_denominator(diagonal_polynomial(q))
        predicted = predicted_minimal_denominator(q)
        assert actual == predicted, ("denominator", q, actual, predicted)
    lines.append(
        f"PASS: minimal monomial denominator formula for 0 <= q <= "
        f"{summary.denominator_max_q}."
    )

    # 9. Check the row-pulse support, symmetry, mass, and plateau formula.
    for order in range(1, 11):
        pulse = pulse_coefficients(order)
        degree = (1 << order) - order - 1
        assert len(pulse) == degree + 1
        assert all(value > 0 for value in pulse)
        assert pulse == tuple(reversed(pulse))
        assert sum(pulse) == 1 << (order * (order - 1) // 2)
        peak = 1 << ((order - 1) * (order - 2) // 2)
        assert max(pulse) == peak
        assert sum(1 for value in pulse if value == peak) == order
    lines.append("PASS: support, positivity, palindromy, mass, and plateau for orders 1..10.")

    return lines


def write_polynomial_csv(path: Path, max_q: int) -> None:
    """Write expanded and factored diagonal polynomials to a CSV file."""

    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(
            [
                "diagonal_offset_d",
                "q=d-1",
                "degree",
                "minimal_denominator",
                "expanded_D_q(x)",
                "factored_D_q(x)",
            ]
        )
        for q in range(max_q + 1):
            poly = diagonal_polynomial(q)
            writer.writerow(
                [
                    q + 1,
                    q,
                    poly.degree(),
                    actual_minimal_denominator(poly),
                    sp.sstr(poly.as_expr()),
                    sp.sstr(sp.factor(poly.as_expr())),
                ]
            )


def write_root_csv(path: Path, max_q: int) -> None:
    """Write the exact nonnegative rational roots D_q(m/2)=0 to CSV."""

    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["q", "diagonal_offset_d", "m_indices", "roots_x=m/2"])
        for q in range(max_q + 1):
            indices = half_grid_root_indices(q)
            roots = [str(sp.Rational(m, 2)) for m in indices]
            writer.writerow([q, q + 1, " ".join(map(str, indices)), " ".join(roots)])


def plot_normalized_pulses(path_pdf: Path, path_png: Path) -> None:
    """Plot normalized first-block pulses for rows n=1,2,3,4."""

    figure, axis = plt.subplots(figsize=(8.6, 5.2))
    for n in range(1, 5):
        order = 2 * n + 1
        block_size = 1 << order
        pulse = pulse_coefficients(order)
        shift = n + 1
        peak = 1 << ((order - 1) * (order - 2) // 2)
        abscissas = [(shift + index) / block_size for index in range(len(pulse))]
        ordinates = [value / peak for value in pulse]
        axis.plot(abscissas, ordinates, label=f"row n={n} (order {order})")

    axis.set_xlabel(r"normalized column $k/2^{2n+1}$")
    axis.set_ylabel("entry divided by the row peak")
    axis.set_title("Normalized positive pulse in the first dyadic block")
    axis.set_xlim(0.0, 1.0)
    axis.set_ylim(bottom=0.0)
    axis.grid(True, alpha=0.3)
    axis.legend()
    figure.tight_layout()
    figure.savefig(path_pdf)
    figure.savefig(path_png, dpi=180)
    plt.close(figure)


def build_report(output_dir: Path, summary: VerificationSummary, max_table_q: int) -> str:
    """Run checks and return a complete textual report."""

    status = verify_identities(summary)
    lines = [
        "Exact verification report",
        "=========================",
        "",
        f"Python: {platform.python_version()}",
        f"SymPy: {sp.__version__}",
        "",
        *status,
        "",
        "First diagonal polynomials",
        "--------------------------",
    ]
    for q in range(max_table_q + 1):
        poly = diagonal_polynomial(q)
        lines.append(
            f"d={q+1:2d}, q={q:2d}, denominator="
            f"{actual_minimal_denominator(poly):>8d}: "
            f"{sp.sstr(sp.factor(poly.as_expr()))}"
        )

    lines.extend(["", "Nonnegative rational roots", "--------------------------"])
    for q in range(max_table_q + 1):
        indices = half_grid_root_indices(q)
        roots = [sp.Rational(m, 2) for m in indices]
        lines.append(f"q={q:2d}: m={indices}; x={roots}")

    report = "\n".join(lines) + "\n"
    (output_dir / "verification_report.txt").write_text(report, encoding="utf-8")
    return report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent / "generated",
        help="directory for CSV tables, report, and figures",
    )
    parser.add_argument(
        "--max-table-q",
        type=int,
        default=20,
        help="largest q printed and written to the CSV tables",
    )
    parser.add_argument(
        "--article-figure-dir",
        type=Path,
        default=Path(__file__).resolve().parent / "figures",
        help=(
            "directory receiving synchronized copies of the generated figure "
            "for LaTeX inclusion (default: the article's figures directory)"
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    output_dir: Path = args.output_dir
    output_dir.mkdir(parents=True, exist_ok=True)

    summary = VerificationSummary(
        max_n=5,
        max_k=70,
        max_q=30,
        max_half_index=30,
        denominator_max_q=24,
    )
    report = build_report(output_dir, summary, args.max_table_q)
    write_polynomial_csv(output_dir / "diagonal_polynomials.csv", args.max_table_q)
    write_root_csv(output_dir / "half_grid_roots.csv", args.max_table_q)
    generated_figure_pdf = output_dir / "normalized_row_pulses.pdf"
    generated_figure_png = output_dir / "normalized_row_pulses.png"
    plot_normalized_pulses(generated_figure_pdf, generated_figure_png)

    # Keep the article's figure directory synchronized automatically so that
    # the one-command experiment run can be followed immediately by latexmk.
    article_figure_dir: Path = args.article_figure_dir
    article_figure_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy2(generated_figure_pdf, article_figure_dir / generated_figure_pdf.name)
    shutil.copy2(generated_figure_png, article_figure_dir / generated_figure_png.name)

    print(report, end="")
    print(f"Generated artifacts in: {output_dir}")
    print(f"Synchronized article figures in: {article_figure_dir}")


if __name__ == "__main__":
    main()
