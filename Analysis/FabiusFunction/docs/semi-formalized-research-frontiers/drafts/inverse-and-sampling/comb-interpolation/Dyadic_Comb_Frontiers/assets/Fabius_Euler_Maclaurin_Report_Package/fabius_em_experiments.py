#!/usr/bin/env python3
"""Exact and numerical experiments for Fabius--Euler--Maclaurin quadrature.

This script accompanies the report

    Euler--Maclaurin and Exhaustion Quadratures for Fabius and Rvachev Moments.

It deliberately uses exact rational arithmetic whenever a theorem predicts an
exact identity.  Floating-point arithmetic is restricted to independent checks
of the sinc-product spectral series and to plotting.

Main capabilities
-----------------
1. Compute the even moments c_k = integral x^(2k) up(x) dx recursively.
2. Evaluate F(a/2^N) exactly from the finite Thue--Morse/moment formula.
3. Compute J_n = integral_0^1 x^n F(x) dx exactly.
4. Evaluate the Bernoulli-corrected composite rule and verify finite
   termination at the predicted dyadic levels.
5. Verify the closed form of the Ruffa/exhaustion increments after the
   termination threshold.
6. Verify the derivative-free rational Richardson extrapolation.
7. Compare exact first-obstruction constants with the Fourier sinc-product
   Dirichlet series.

The code has no nonstandard dependency except matplotlib, which is used only
for the optional PDF/PNG figure.  All mathematical tables are generated even
when matplotlib is absent.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence


# ---------------------------------------------------------------------------
# Exact special-number utilities
# ---------------------------------------------------------------------------


def bernoulli_numbers(max_index: int) -> list[Fraction]:
    """Return B_0,...,B_max_index with the convention B_1=-1/2.

    The defining recurrence is

        sum_{k=0}^m binom(m+1,k) B_k = 0,  m >= 1.

    Fractions make the result exact and avoid convention ambiguities.
    """
    if max_index < 0:
        raise ValueError("max_index must be nonnegative")
    values = [Fraction(1)]
    for m in range(1, max_index + 1):
        subtotal = sum(
            Fraction(math.comb(m + 1, k)) * values[k] for k in range(m)
        )
        values.append(-subtotal / Fraction(m + 1))
    return values


def up_even_moments(max_index: int) -> list[Fraction]:
    """Return c_k = integral_{-1}^1 x^(2k) up(x) dx for 0 <= k <= max_index.

    The exact recurrence is

      (2k+1)(2^(2k)-1)c_k = sum_{j=0}^{k-1} binom(2k+1,2j)c_j,
      c_0=1.
    """
    if max_index < 0:
        raise ValueError("max_index must be nonnegative")
    c = [Fraction(1)]
    for k in range(1, max_index + 1):
        numerator = sum(
            Fraction(math.comb(2 * k + 1, 2 * j)) * c[j] for j in range(k)
        )
        denominator = Fraction((2 * k + 1) * (2 ** (2 * k) - 1))
        c.append(numerator / denominator)
    return c


def thue_morse_sign(index: int) -> int:
    """Return epsilon_index=(-1)^(binary digit sum of index)."""
    if index < 0:
        raise ValueError("index must be nonnegative")
    return -1 if index.bit_count() % 2 else 1


# ---------------------------------------------------------------------------
# Exact Fabius values and moments
# ---------------------------------------------------------------------------


def fabius_dyadic_grid(level: int) -> list[Fraction]:
    r"""Return all exact values F(a/2^level), 0 <= a <= 2^level.

    The implementation is the finite formula

      F(a/2^N) = 2^{-N(N+1)/2}/N! *
        sum_{h=0}^{a-1} epsilon_h
        sum_{k=0}^{floor(N/2)} binom(N,2k)c_k(2a-2h-1)^{N-2k}.

    For all a at a fixed level this is evaluated as a finite convolution.  The
    intended experiment range is N <= 10 or 12; exact fractions grow quickly.
    """
    if level < 0:
        raise ValueError("level must be nonnegative")
    mesh = 1 << level
    c = up_even_moments(level // 2)

    # K(j) is the inner moment polynomial at the odd argument 2j-1.
    kernel: list[Fraction] = []
    for j in range(1, mesh + 1):
        odd_argument = 2 * j - 1
        value = sum(
            Fraction(math.comb(level, 2 * k))
            * c[k]
            * odd_argument ** (level - 2 * k)
            for k in range(level // 2 + 1)
        )
        kernel.append(value)

    epsilon = [thue_morse_sign(h) for h in range(mesh)]
    scale = Fraction(
        1,
        (1 << (level * (level + 1) // 2)) * math.factorial(level),
    )

    values = [Fraction(0)] * (mesh + 1)
    for a in range(1, mesh + 1):
        convolution = sum(epsilon[a - j] * kernel[j - 1] for j in range(1, a + 1))
        values[a] = scale * convolution

    # Cheap internal consistency checks.
    assert values[0] == 0 and values[-1] == 1
    for a in range(mesh + 1):
        assert values[a] + values[mesh - a] == 1
    return values


def fabius_moment(power: int) -> Fraction:
    r"""Return J_power = integral_0^1 x^power F(x) dx exactly.

    Let X have density up on [-1,1] and Y=(1+X)/2, so F is the CDF of Y and
    F'=density(Y).  Integration by parts gives

      J_n = (1 - E[Y^(n+1)])/(n+1).

    Only the even moments of X survive in E[Y^(n+1)].
    """
    if power < 0:
        raise ValueError("power must be nonnegative")
    k = power + 1
    c = up_even_moments(k // 2)
    y_moment = sum(
        Fraction(math.comb(k, 2 * j)) * c[j]
        for j in range(k // 2 + 1)
    ) / Fraction(2**k)
    return (Fraction(1) - y_moment) / Fraction(k)


# ---------------------------------------------------------------------------
# Endpoint Euler--Maclaurin correction and Ruffa increments
# ---------------------------------------------------------------------------


def endpoint_raw_sum(power: int, level: int, grid: Sequence[Fraction]) -> Fraction:
    """Return Q_N = 2^{-N} sum_{a=1}^{2^N-1}(a/2^N)^power F(a/2^N)."""
    mesh = 1 << level
    if len(grid) != mesh + 1:
        raise ValueError("grid length does not match level")
    return sum(
        Fraction(a, mesh) ** power * grid[a] for a in range(1, mesh)
    ) / Fraction(mesh)


def monomial_correction_coefficients(power: int) -> list[Fraction]:
    r"""Return c_r(P)=B_{2r}P^(2r-1)(1)/(2r)! for P(x)=x^power.

    These are precisely the nontrivial endpoint Euler--Maclaurin coefficients.
    """
    if power < 0:
        raise ValueError("power must be nonnegative")
    max_r = (power + 1) // 2
    bernoulli = bernoulli_numbers(2 * max_r)
    coefficients: list[Fraction] = []
    for r in range(1, max_r + 1):
        derivative_at_one = Fraction(
            math.factorial(power), math.factorial(power - 2 * r + 1)
        )
        coefficients.append(
            bernoulli[2 * r]
            * derivative_at_one
            / Fraction(math.factorial(2 * r))
        )
    return coefficients


def corrected_endpoint_rule(power: int, level: int, grid: Sequence[Fraction]) -> Fraction:
    r"""Return the Bernoulli-corrected endpoint rule A_{2^level}(x^power)."""
    mesh = 1 << level
    raw = endpoint_raw_sum(power, level, grid)
    correction = Fraction(1, 2 * mesh)  # P(1)=1 for every monomial.
    for r, coefficient in enumerate(monomial_correction_coefficients(power), start=1):
        correction -= coefficient / Fraction(mesh ** (2 * r))
    return raw + correction


def predicted_endpoint_threshold(power: int) -> int:
    """Sharp dyadic onset threshold N0 for endpoint-corrected x^power F(x)."""
    if power == 0:
        return 0
    return 2 * ((power + 1) // 2)  # 2*ceil(power/2)


def ruffa_increment_from_raw_sums(
    power: int,
    level: int,
    fine_grid: Sequence[Fraction],
    coarse_grid: Sequence[Fraction],
) -> Fraction:
    """Return L_level=Q_level-Q_{level-1}; level must be at least 1."""
    if level < 1:
        raise ValueError("level must be at least 1")
    return endpoint_raw_sum(power, level, fine_grid) - endpoint_raw_sum(
        power, level - 1, coarse_grid
    )


def ruffa_increment_closed(power: int, level: int) -> Fraction:
    r"""Closed post-threshold Ruffa increment for x^power F(x).

      L_j = 2^{-j-1} - sum_r c_r (2^(2r)-1)2^{-2rj}.
    """
    if level < 1:
        raise ValueError("level must be at least 1")
    value = Fraction(1, 2 ** (level + 1))
    for r, coefficient in enumerate(monomial_correction_coefficients(power), start=1):
        value -= coefficient * Fraction(2 ** (2 * r) - 1, 2 ** (2 * r * level))
    return value


# ---------------------------------------------------------------------------
# Exact rational Richardson extrapolation
# ---------------------------------------------------------------------------


def polynomial_multiply(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    """Multiply two coefficient lists in ascending powers."""
    result = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            result[i + j] += ai * bj
    return result


def richardson_characteristic(power: int) -> list[Fraction]:
    r"""Return chi(z)=prod_{lambda in Lambda}(z-lambda), ascending coefficients.

    Lambda={1/2, 2^{-2},2^{-4},...,2^{-2R}}, R=floor((power+1)/2).
    """
    roots = [Fraction(1, 2)]
    roots.extend(
        Fraction(1, 2 ** (2 * r))
        for r in range(1, (power + 1) // 2 + 1)
    )
    polynomial = [Fraction(1)]
    for root in roots:
        polynomial = polynomial_multiply(polynomial, [-root, Fraction(1)])
    return polynomial


def richardson_weights(power: int) -> list[Fraction]:
    r"""Return rational weights w_s=a_s/chi(1) extracting the constant limit."""
    characteristic = richardson_characteristic(power)
    chi_at_one = sum(characteristic)
    if chi_at_one == 0:
        raise ZeroDivisionError("unexpected characteristic root at one")
    return [coefficient / chi_at_one for coefficient in characteristic]


def richardson_extrapolate(raw_sums: Sequence[Fraction], power: int) -> Fraction:
    """Extract the exact moment from consecutive post-threshold raw sums."""
    weights = richardson_weights(power)
    if len(raw_sums) != len(weights):
        raise ValueError("wrong number of raw sums for extrapolation")
    return sum(w * q for w, q in zip(weights, raw_sums))


# ---------------------------------------------------------------------------
# Floating-point spectral checks
# ---------------------------------------------------------------------------


def sinc_pi(x: float) -> float:
    """Return sin(pi*x)/(pi*x), with the removable value at zero."""
    if x == 0.0:
        return 1.0
    return math.sin(math.pi * x) / (math.pi * x)


def phi_sinc_product(x: float, factors: int = 90) -> float:
    r"""Approximate Phi(x)=prod_{j>=0}sinc(pi*x/2^j) in repository notation.

    The helper sinc_pi(y) equals sin(pi*y)/(pi*y), hence the jth factor is
    sinc_pi(x/2^j).  Ninety factors are ample for double precision at the
    arguments used here.
    """
    product = 1.0
    scale = 1.0
    for _ in range(factors):
        product *= sinc_pi(x / scale)
        scale *= 2.0
    return product


def odd_spectral_series(order: int, max_odd: int = 20001) -> float:
    r"""Approximate sum_{m>=1,m odd} Phi(m/2)/m^order.

    The sinc product has rapid dyadic decay; the elementary truncation is more
    than sufficient for the low-order consistency checks in the report.
    """
    if order < 2:
        raise ValueError("order must be at least 2")
    total = 0.0
    for m in range(1, max_odd + 1, 2):
        total += phi_sinc_product(m / 2.0) / (m**order)
    return total


def first_obstruction_coefficient(power: int, exact_error: Fraction) -> Fraction:
    r"""Return the rational C with S_{d+1}=C*pi^(d+1) for odd d=power.

    For P=x^d, d odd, at level N=d,

      A-I = 2(-1)^((d+1)/2)d! S_{d+1}/(2*pi*2^d)^(d+1).
    """
    d = power
    if d < 1 or d % 2 == 0:
        raise ValueError("power must be a positive odd integer")
    sign = -1 if ((d + 1) // 2) % 2 else 1
    numerator_scale = (2 * (2**d)) ** (d + 1)
    return exact_error * Fraction(
        numerator_scale,
        2 * sign * math.factorial(d),
    )


# ---------------------------------------------------------------------------
# Report-output generation
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ThresholdRecord:
    power: int
    predicted: int
    error_before: Fraction | None
    error_at: Fraction


def factor_integer(value: int) -> list[tuple[int, int]]:
    """Return the prime factorization of a positive integer.

    The denominators arising in this experiment are smooth, so elementary
    trial division is both transparent and fast.  This routine is used only
    to typeset very large exact rational numbers compactly in the report.
    """
    if value < 1:
        raise ValueError("value must be positive")
    factors: list[tuple[int, int]] = []
    remaining = value
    divisor = 2
    while divisor * divisor <= remaining:
        exponent = 0
        while remaining % divisor == 0:
            remaining //= divisor
            exponent += 1
        if exponent:
            factors.append((divisor, exponent))
        divisor = 3 if divisor == 2 else divisor + 2
    if remaining > 1:
        factors.append((remaining, 1))
    return factors


def factored_integer_tex(value: int) -> str:
    """Format a positive integer as a product of prime powers in LaTeX."""
    pieces = [
        str(prime) if exponent == 1 else f"{prime}^{{{exponent}}}"
        for prime, exponent in factor_integer(value)
    ]
    return r"\,".join(pieces)


def fraction_tex(value: Fraction, *, factor_large_denominator: bool = False) -> str:
    """Format a Fraction as compact LaTeX.

    When ``factor_large_denominator`` is true, denominators of ten or more
    digits are printed as products of prime powers.  This keeps exact tables
    legible without replacing any rational value by a decimal approximation.
    """
    if value.denominator == 1:
        return str(value.numerator)
    sign = "-" if value < 0 else ""
    v = abs(value)
    denominator = (
        factored_integer_tex(v.denominator)
        if factor_large_denominator and v.denominator >= 10**9
        else str(v.denominator)
    )
    return f"{sign}\\frac{{{v.numerator}}}{{{denominator}}}"


def write_csv(path: Path, header: Sequence[str], rows: Iterable[Sequence[object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(header)
        writer.writerows(rows)


def generate_outputs(output_dir: Path, max_power: int, max_level: int) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)

    # Cache exact grids because they are the most expensive objects.
    grids: dict[int, list[Fraction]] = {
        level: fabius_dyadic_grid(level) for level in range(max_level + 1)
    }

    moments = [(n, fabius_moment(n)) for n in range(max_power + 1)]
    write_csv(
        output_dir / "moments.csv",
        ["n", "J_n_exact", "J_n_decimal"],
        [(n, str(value), f"{float(value):.16g}") for n, value in moments],
    )

    thresholds: list[ThresholdRecord] = []
    error_rows: list[tuple[int, int, Fraction]] = []
    for n, moment in moments:
        threshold = predicted_endpoint_threshold(n)
        if threshold > max_level:
            continue
        at_value = corrected_endpoint_rule(n, threshold, grids[threshold])
        error_at = at_value - moment
        assert error_at == 0
        before_error: Fraction | None = None
        if threshold >= 1:
            before_value = corrected_endpoint_rule(n, threshold - 1, grids[threshold - 1])
            before_error = before_value - moment
            if n > 0:
                assert before_error != 0
        thresholds.append(ThresholdRecord(n, threshold, before_error, error_at))

        for level in range(max_level + 1):
            error = corrected_endpoint_rule(n, level, grids[level]) - moment
            error_rows.append((n, level, error))

    write_csv(
        output_dir / "thresholds.csv",
        ["n", "predicted_N0", "error_at_N0_minus_1", "error_at_N0"],
        [
            (
                record.power,
                record.predicted,
                "" if record.error_before is None else str(record.error_before),
                str(record.error_at),
            )
            for record in thresholds
        ],
    )
    write_csv(
        output_dir / "corrected_errors.csv",
        ["n", "N", "A_N_minus_J_n"],
        [(n, level, str(error)) for n, level, error in error_rows],
    )

    # Ruffa closure for n=3, a compact representative example.
    ruffa_rows: list[tuple[int, Fraction, Fraction, Fraction]] = []
    power = 3
    for level in range(1, max_level + 1):
        actual = ruffa_increment_from_raw_sums(
            power, level, grids[level], grids[level - 1]
        )
        closed = ruffa_increment_closed(power, level)
        difference = actual - closed
        if level - 1 >= predicted_endpoint_threshold(power):
            assert difference == 0
        ruffa_rows.append((level, actual, closed, difference))
    write_csv(
        output_dir / "ruffa_n3.csv",
        ["j", "L_j_exact", "closed_form", "difference"],
        [(j, str(a), str(c), str(d)) for j, a, c, d in ruffa_rows],
    )

    # Richardson checks for every power whose required levels fit the cache.
    richardson_rows: list[tuple[int, int, list[Fraction], Fraction, Fraction]] = []
    for n, moment in moments:
        base = predicted_endpoint_threshold(n)
        weights = richardson_weights(n)
        if base + len(weights) - 1 > max_level:
            continue
        raw = [endpoint_raw_sum(n, base + s, grids[base + s]) for s in range(len(weights))]
        extrapolated = richardson_extrapolate(raw, n)
        assert extrapolated == moment
        richardson_rows.append((n, base, weights, extrapolated, moment))
    write_csv(
        output_dir / "richardson.csv",
        ["n", "base_N", "weights", "extrapolated", "exact_moment"],
        [
            (
                n,
                base,
                "; ".join(str(w) for w in weights),
                str(extrapolated),
                str(moment),
            )
            for n, base, weights, extrapolated, moment in richardson_rows
        ],
    )

    # First-obstruction spectral constants for odd degrees available in cache.
    spectral_rows: list[tuple[int, Fraction, float, float]] = []
    for d in range(1, min(max_power, max_level) + 1, 2):
        moment = fabius_moment(d)
        exact_error = corrected_endpoint_rule(d, d, grids[d]) - moment
        rational_coefficient = first_obstruction_coefficient(d, exact_error)
        numerical_series = odd_spectral_series(d + 1)
        predicted_series = float(rational_coefficient) * math.pi ** (d + 1)
        spectral_rows.append(
            (d + 1, rational_coefficient, numerical_series, numerical_series - predicted_series)
        )
    write_csv(
        output_dir / "spectral_series.csv",
        ["order", "S_order_over_pi_power", "direct_numeric", "numeric_minus_exact"],
        [
            (order, str(coeff), f"{numeric:.17g}", f"{difference:.3e}")
            for order, coeff, numeric, difference in spectral_rows
        ],
    )

    # Human-readable log.
    log_lines = [
        "Fabius--Euler--Maclaurin exact experiment log",
        "=" * 52,
        "",
        "Exact moments J_n = integral_0^1 x^n F(x) dx:",
    ]
    log_lines.extend(f"  J_{n} = {value}" for n, value in moments)
    log_lines.extend(["", "Sharp dyadic onset checks:"])
    for record in thresholds:
        log_lines.append(
            f"  n={record.power:2d}: N0={record.predicted:2d}, "
            f"error at N0-1={record.error_before}, error at N0={record.error_at}"
        )
    log_lines.extend(["", "First-obstruction spectral evaluations:"])
    for order, coeff, numeric, difference in spectral_rows:
        log_lines.append(
            f"  S_{order}/pi^{order} = {coeff}; direct series={numeric:.17g}; "
            f"difference={difference:.3e}"
        )
    log_lines.extend(["", "Richardson extrapolation checks:"])
    for n, base, weights, extrapolated, _ in richardson_rows:
        log_lines.append(
            f"  n={n:2d}, base N={base:2d}, weights={weights}, value={extrapolated}"
        )
    (output_dir / "numerical_results.txt").write_text(
        "\n".join(log_lines) + "\n", encoding="utf-8"
    )

    # LaTeX tables included by the report.
    moment_lines = [
        r"\begin{tabular}{rll}",
        r"\toprule",
        r"$n$ & exact $J_n$ & decimal \\",
        r"\midrule",
    ]
    for n, value in moments:
        moment_lines.append(
            f"{n} & ${fraction_tex(value)}$ & ${float(value):.12f}$ \\\\"
        )
    moment_lines.extend([r"\bottomrule", r"\end{tabular}"])
    (output_dir / "moment_table.tex").write_text(
        "\n".join(moment_lines) + "\n", encoding="utf-8"
    )

    threshold_lines = [
        r"\begin{tabular}{rrlr}",
        r"\toprule",
        r"$n$ & predicted $N_0$ & $A_{N_0-1}-J_n$ & $A_{N_0}-J_n$ \\",
        r"\midrule",
    ]
    for record in thresholds:
        before = "--" if record.error_before is None else f"${fraction_tex(record.error_before, factor_large_denominator=True)}$"
        threshold_lines.append(
            f"{record.power} & {record.predicted} & {before} & $0$ \\\\"
        )
    threshold_lines.extend([r"\bottomrule", r"\end{tabular}"])
    (output_dir / "threshold_table.tex").write_text(
        "\n".join(threshold_lines) + "\n", encoding="utf-8"
    )

    spectral_lines = [
        r"\begin{tabular}{rll}",
        r"\toprule",
        r"$s$ & exact $S_s/\pi^s$ & direct numerical check \\",
        r"\midrule",
    ]
    for order, coeff, numeric, _ in spectral_rows:
        spectral_lines.append(
            f"{order} & ${fraction_tex(coeff)}$ & ${numeric:.14g}$ \\\\"
        )
    spectral_lines.extend([r"\bottomrule", r"\end{tabular}"])
    (output_dir / "spectral_table.tex").write_text(
        "\n".join(spectral_lines) + "\n", encoding="utf-8"
    )

    # Optional exact-error plot.  Zeros are displayed below the smallest
    # nonzero error solely to make termination visible.
    try:
        import matplotlib.pyplot as plt  # type: ignore

        selected_powers = list(range(1, min(max_power, 8) + 1))
        nonzero_logs = [
            math.log10(abs(float(error)))
            for n, _level, error in error_rows
            if n in selected_powers and error != 0
        ]
        floor = min(nonzero_logs) - 2.0 if nonzero_logs else -20.0
        fig, ax = plt.subplots(figsize=(8.1, 4.8))
        for n in selected_powers:
            ys: list[float] = []
            xs: list[int] = []
            for nn, level, error in error_rows:
                if nn != n:
                    continue
                xs.append(level)
                ys.append(floor if error == 0 else math.log10(abs(float(error))))
            ax.plot(xs, ys, marker="o", linewidth=1.2, label=f"n={n}")
        ax.set_xlabel("dyadic level N")
        ax.set_ylabel(r"$\log_{10}|A_{2^N}(x^n)-J_n|$")
        ax.set_title("Finite termination of Bernoulli-corrected Fabius moments")
        ax.grid(True, linewidth=0.35)
        ax.legend(ncol=4, fontsize=8)
        fig.tight_layout()
        fig.savefig(output_dir / "termination_errors.pdf")
        fig.savefig(output_dir / "termination_errors.png", dpi=180)
        plt.close(fig)
    except Exception as exc:  # pragma: no cover - plotting is optional
        (output_dir / "plot_warning.txt").write_text(
            f"The optional plot was not generated: {exc}\n", encoding="utf-8"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("data"),
        help="directory for CSV, TeX, log, and figure outputs",
    )
    parser.add_argument(
        "--max-power",
        type=int,
        default=10,
        help="largest monomial power to test (default: 10)",
    )
    parser.add_argument(
        "--max-level",
        type=int,
        default=10,
        help="largest exact dyadic grid level to build (default: 10)",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.max_power < 0 or args.max_level < 0:
        raise SystemExit("max-power and max-level must be nonnegative")
    generate_outputs(args.output_dir, args.max_power, args.max_level)
    print(f"Wrote exact experiment outputs to {args.output_dir.resolve()}")


if __name__ == "__main__":
    main()
