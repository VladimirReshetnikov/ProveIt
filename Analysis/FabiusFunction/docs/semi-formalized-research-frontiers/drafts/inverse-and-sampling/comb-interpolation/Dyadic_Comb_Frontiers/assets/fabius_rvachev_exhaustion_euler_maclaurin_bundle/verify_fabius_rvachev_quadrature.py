#!/usr/bin/env python3
"""Exact experiments for Fabius/Rvachev Euler--Maclaurin quadrature.

This script accompanies the report
    Exhaustion, Euler--Maclaurin, and Spectral Exactness for
    Fabius--Rvachev Monomial Integrals.

It uses only the Python standard library.  Every displayed value is computed
with fractions.Fraction, so a row marked PASS is an exact identity rather than
a floating-point comparison.

The normalization is
    up(x) = F(1-|x|) on |x| <= 1,
    F'(x) = 2 up(2x-1), 0 <= x <= 1.
The even moments are
    c_j = integral_{-1}^1 x^(2j) up(x) dx,
and
    d_n = E[X^n] = 2^(-n) sum_j binom(n,2j)c_j,
where X has distribution function F.

Outputs (written next to this script unless --output-dir is supplied):
  * verification_summary.csv
  * first_defect.csv
  * exact_moments.csv

Usage:
    python verify_fabius_rvachev_quadrature.py
    python verify_fabius_rvachev_quadrature.py --max-degree 7 --output-dir out
"""

from __future__ import annotations

import argparse
import csv
from functools import lru_cache
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
from typing import Iterable


def falling(n: int, k: int) -> int:
    """Return the falling factorial n(n-1)...(n-k+1)."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    if k > n:
        return 0
    result = 1
    for j in range(k):
        result *= n - j
    return result


@lru_cache(maxsize=None)
def bernoulli_numbers(max_n: int) -> tuple[Fraction, ...]:
    """Bernoulli numbers B_0,...,B_max_n with B_1=-1/2.

    The recurrence follows from
        sum_{k=0}^m binom(m+1,k) B_k = 0,  m >= 1.
    """
    if max_n < 0:
        return tuple()
    values = [Fraction(1)]
    for m in range(1, max_n + 1):
        subtotal = sum(
            Fraction(comb(m + 1, k)) * values[k] for k in range(m)
        )
        values.append(-subtotal / Fraction(m + 1))
    return tuple(values)


def bernoulli_number(n: int) -> Fraction:
    return bernoulli_numbers(n)[n]


def bernoulli_polynomial(n: int, x: Fraction) -> Fraction:
    """Evaluate B_n(x) exactly."""
    numbers = bernoulli_numbers(n)
    return sum(
        Fraction(comb(n, k)) * numbers[k] * x ** (n - k)
        for k in range(n + 1)
    )


@lru_cache(maxsize=None)
def even_up_moments(max_j: int) -> tuple[Fraction, ...]:
    """Return c_0,...,c_max_j, the even moments of Rvachev's up."""
    if max_j < 0:
        return tuple()
    c = [Fraction(1)]
    for n in range(1, max_j + 1):
        numerator = sum(
            Fraction(comb(2 * n + 1, 2 * k)) * c[k] for k in range(n)
        )
        denominator = Fraction((2 * n + 1) * (2 ** (2 * n) - 1))
        c.append(numerator / denominator)
    return tuple(c)


def c_moment(j: int) -> Fraction:
    return even_up_moments(j)[j]


def d_moment(n: int) -> Fraction:
    """Return d_n=E[X^n], where X has CDF F."""
    c = even_up_moments(n // 2)
    return sum(
        Fraction(comb(n, 2 * k)) * c[k]
        for k in range(n // 2 + 1)
    ) / Fraction(2**n)


def fabius_monomial_integral(n: int) -> Fraction:
    """I_n = integral_0^1 x^n F(x) dx."""
    return (Fraction(1) - d_moment(n + 1)) / Fraction(n + 1)


def half_up_monomial_integral(n: int) -> Fraction:
    """J_n = integral_0^1 x^n up(x) dx."""
    return d_moment(n + 1) / Fraction(n + 1)


@lru_cache(maxsize=None)
def fabius_dyadic(a: int, level: int) -> Fraction:
    """Exact F(a/2^level) from the finite Thue--Morse/moment formula.

    The implementation accepts 0 <= a <= 2^level.  Symmetry is used for
    a > 2^(level-1), reducing the summation cost and providing an independent
    check of F(1-x)=1-F(x).
    """
    if level < 0:
        raise ValueError("level must be nonnegative")
    denominator = 2**level
    if not 0 <= a <= denominator:
        raise ValueError("a must satisfy 0 <= a <= 2^level")
    if a == 0:
        return Fraction(0)
    if a == denominator:
        return Fraction(1)
    if 2 * a > denominator:
        return Fraction(1) - fabius_dyadic(denominator - a, level)

    c = even_up_moments(level // 2)
    total = Fraction(0)
    for h in range(a):
        thue_morse_sign = -1 if h.bit_count() % 2 else 1
        inner = Fraction(0)
        odd_distance = 2 * a - 2 * h - 1
        for k in range(level // 2 + 1):
            inner += (
                Fraction(comb(level, 2 * k))
                * c[k]
                * odd_distance ** (level - 2 * k)
            )
        total += thue_morse_sign * inner

    scale = Fraction(1, factorial(level) * 2 ** comb(level + 1, 2))
    return scale * total


def up_dyadic_nonnegative(a: int, level: int) -> Fraction:
    """Exact up(a/2^level) for 0 <= a <= 2^level."""
    return fabius_dyadic(2**level - a, level)


def fabius_lower_sum(n: int, level: int) -> Fraction:
    """Q_{2^level,0}(x^n F(x)); F(0)=0, so this is the open sum."""
    m = 2**level
    return sum(
        Fraction(a**n, m ** (n + 1)) * fabius_dyadic(a, level)
        for a in range(m)
    )


def fabius_midpoint_sum(n: int, level: int) -> Fraction:
    """Q_{2^level,1/2}(x^n F(x)), evaluated on denominator 2^(level+1)."""
    m = 2**level
    denom = 2 * m
    return sum(
        Fraction((2 * a + 1) ** n, m * denom**n)
        * fabius_dyadic(2 * a + 1, level + 1)
        for a in range(m)
    )


def half_up_lower_open_sum(n: int, level: int) -> Fraction:
    """Open dyadic sum for x^n up(x) on [0,1]."""
    m = 2**level
    return sum(
        Fraction(a**n, m ** (n + 1)) * up_dyadic_nonnegative(a, level)
        for a in range(1, m)
    )


def fabius_boundary_correction(n: int, m: int, theta: Fraction) -> Fraction:
    """C such that integral = shifted_sum - C after dyadic annihilation."""
    return sum(
        bernoulli_polynomial(r, theta)
        * Fraction(falling(n, r - 1), factorial(r) * m**r)
        for r in range(1, n + 2)
    )


def lower_tail_formula(n: int, level: int) -> Fraction:
    """Exact I_n-Q_N once the spectral threshold is reached."""
    m = 2**level
    correction = Fraction(1, 2 * m)
    for j in range(1, (n + 1) // 2 + 1):
        correction -= (
            bernoulli_number(2 * j)
            * Fraction(falling(n, 2 * j - 1), factorial(2 * j) * m ** (2 * j))
        )
    return correction


def half_up_tail_formula(n: int, level: int) -> Fraction:
    """Exact J_n-open_sum once the spectral threshold is reached."""
    m = 2**level
    if n == 0:
        return Fraction(1, 2 * m)
    return bernoulli_number(n + 1) / Fraction((n + 1) * m ** (n + 1))


def expected_bernoulli_of_x(order: int) -> Fraction:
    """E[B_order(X)] from exact Fabius moments d_j."""
    numbers = bernoulli_numbers(order)
    return sum(
        Fraction(comb(order, k)) * numbers[k] * d_moment(order - k)
        for k in range(order + 1)
    )


def first_defect_prediction(degree: int) -> Fraction:
    """Corrected lower-grid residual at M=2^degree.

    For degree >= 1, the theorem predicts
      (-1)^(degree+1) E[B_{degree+1}(X)]
      / ((degree+1) M^(degree+1)).
    """
    if degree < 1:
        raise ValueError("degree must be at least 1")
    m = 2**degree
    return (
        Fraction((-1) ** (degree + 1))
        * expected_bernoulli_of_x(degree + 1)
        / Fraction((degree + 1) * m ** (degree + 1))
    )


def exact_fraction_text(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def write_csv(path: Path, fieldnames: Iterable[str], rows: list[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(fieldnames))
        writer.writeheader()
        writer.writerows(rows)


def run(max_degree: int, output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)

    moment_rows: list[dict[str, object]] = []
    for n in range(max_degree + 2):
        c_text = exact_fraction_text(c_moment(n // 2)) if n % 2 == 0 else "(odd moment 0)"
        moment_rows.append(
            {
                "n": n,
                "c_n_over_2_when_even": c_text,
                "d_n": exact_fraction_text(d_moment(n)),
                "I_n_int_xn_F": exact_fraction_text(fabius_monomial_integral(n)),
                "J_n_int_xn_up_half": exact_fraction_text(half_up_monomial_integral(n)),
            }
        )
    write_csv(
        output_dir / "exact_moments.csv",
        ["n", "c_n_over_2_when_even", "d_n", "I_n_int_xn_F", "J_n_int_xn_up_half"],
        moment_rows,
    )

    verification_rows: list[dict[str, object]] = []
    for n in range(max_degree + 1):
        # Safe dyadic level: nu_2(M)=level > degree.
        level = n + 1
        m = 2**level
        exact_i = fabius_monomial_integral(n)

        lower_q = fabius_lower_sum(n, level)
        lower_recovered = lower_q - fabius_boundary_correction(n, m, Fraction(0))
        verification_rows.append(
            {
                "family": "Fabius lower + finite EM",
                "degree": n,
                "level": level,
                "computed": exact_fraction_text(lower_recovered),
                "target": exact_fraction_text(exact_i),
                "residual": exact_fraction_text(lower_recovered - exact_i),
                "status": "PASS" if lower_recovered == exact_i else "FAIL",
            }
        )

        midpoint_q = fabius_midpoint_sum(n, level)
        midpoint_recovered = midpoint_q - fabius_boundary_correction(
            n, m, Fraction(1, 2)
        )
        verification_rows.append(
            {
                "family": "Fabius midpoint + finite EM",
                "degree": n,
                "level": level,
                "computed": exact_fraction_text(midpoint_recovered),
                "target": exact_fraction_text(exact_i),
                "residual": exact_fraction_text(midpoint_recovered - exact_i),
                "status": "PASS" if midpoint_recovered == exact_i else "FAIL",
            }
        )

        exact_j = half_up_monomial_integral(n)
        up_q = half_up_lower_open_sum(n, level)
        up_recovered = up_q + half_up_tail_formula(n, level)
        verification_rows.append(
            {
                "family": "half-up lower + one correction",
                "degree": n,
                "level": level,
                "computed": exact_fraction_text(up_recovered),
                "target": exact_fraction_text(exact_j),
                "residual": exact_fraction_text(up_recovered - exact_j),
                "status": "PASS" if up_recovered == exact_j else "FAIL",
            }
        )

        # Verify the closed form of one stabilized Ruffa detail.
        ell = n + 2
        if n % 2 == 0 and n >= 2:
            # Parity superconvergence permits one earlier level.
            ell = n + 1
        if n == 0:
            ell = 1
        detail_direct = fabius_lower_sum(n, ell) - (
            fabius_lower_sum(n, ell - 1) if ell > 0 else Fraction(0)
        )
        detail_formula = lower_tail_formula(n, ell - 1) - lower_tail_formula(n, ell)
        verification_rows.append(
            {
                "family": "Fabius stabilized exhaustion detail",
                "degree": n,
                "level": ell,
                "computed": exact_fraction_text(detail_direct),
                "target": exact_fraction_text(detail_formula),
                "residual": exact_fraction_text(detail_direct - detail_formula),
                "status": "PASS" if detail_direct == detail_formula else "FAIL",
            }
        )

    write_csv(
        output_dir / "verification_summary.csv",
        ["family", "degree", "level", "computed", "target", "residual", "status"],
        verification_rows,
    )

    defect_rows: list[dict[str, object]] = []
    for degree in range(1, max_degree + 1):
        level = degree
        m = 2**level
        q = fabius_lower_sum(degree, level)
        exact_i = fabius_monomial_integral(degree)
        boundary = fabius_boundary_correction(degree, m, Fraction(0))
        observed = q - exact_i - boundary
        predicted = first_defect_prediction(degree)
        defect_rows.append(
            {
                "degree": degree,
                "M": m,
                "E_B_degree_plus_1_X": exact_fraction_text(
                    expected_bernoulli_of_x(degree + 1)
                ),
                "observed_corrected_residual": exact_fraction_text(observed),
                "predicted_corrected_residual": exact_fraction_text(predicted),
                "status": "PASS" if observed == predicted else "FAIL",
            }
        )
    write_csv(
        output_dir / "first_defect.csv",
        [
            "degree",
            "M",
            "E_B_degree_plus_1_X",
            "observed_corrected_residual",
            "predicted_corrected_residual",
            "status",
        ],
        defect_rows,
    )

    failures = [row for row in verification_rows + defect_rows if row["status"] != "PASS"]
    print(f"Wrote exact_moments.csv, verification_summary.csv, and first_defect.csv to {output_dir}")
    print(f"Checked {len(verification_rows) + len(defect_rows)} exact identities.")
    if failures:
        for row in failures:
            print("FAIL:", row)
        raise SystemExit(1)
    print("All exact rational checks passed.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-degree",
        type=int,
        default=7,
        help="largest monomial degree to verify (default: 7)",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory for CSV output (default: script directory)",
    )
    args = parser.parse_args()
    if args.max_degree < 0:
        parser.error("--max-degree must be nonnegative")
    run(args.max_degree, args.output_dir)
