#!/usr/bin/env python3
"""Reproduce the article's finite checks and floating-point diagnostics.

Run from the package root:
    python verification/verify.py
    python verification/verify.py --output data --figures figures

The default destination is build/verification, so a normal replay does not
overwrite delivered data. Symbolic checks are finite exact calculations.
Numerical results are high-precision floating-point diagnostics, not proofs
or interval enclosures. Moderate-size defining-series comparisons validate
the cancelled evaluator used for small inverse arguments.
"""

from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
from functools import lru_cache
import json
from math import comb
from pathlib import Path
import platform

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
import sympy as sp

PACKAGE = Path(__file__).resolve().parents[1]
EXPECTED = {
    "mpmath": "1.3.0",
    "sympy": "1.14.0",
    "numpy": "2.3.5",
    "matplotlib": "3.10.8",
}


def number(value, digits=40):
    """Store arbitrary-precision values as decimal strings, never binary JSON floats."""
    return mp.nstr(value, digits)


def complete_bell(arguments, arithmetic):
    values = [arithmetic(1)]
    for n in range(1, len(arguments) + 1):
        values.append(
            sum(comb(n - 1, j - 1) * arguments[j - 1] * values[n - j]
                for j in range(1, n + 1))
        )
    return values[-1]


def exact_resonance_checks():
    epsilon, logarithm = sp.symbols("epsilon logarithm")
    records = []
    for n in range(4):
        # Independent CAS Laurent expansion of the Gamma factor.
        gamma_series = sp.series(
            (-1) ** n * sp.factorial(n) * sp.gamma(-n - epsilon)
            * sp.exp(epsilon * logarithm), epsilon, 0, 4
        ).removeO().expand()
        for derivative in range(4):
            actual = (sp.factorial(derivative) * gamma_series.coeff(epsilon, derivative)
                      + (-1) ** derivative * sp.stieltjes(derivative))
            arguments = [logarithm + sp.EulerGamma - sp.harmonic(n)]
            arguments += [sp.factorial(j - 1)
                          * (sp.zeta(j) + (-1) ** j * sp.harmonic(n, j))
                          for j in range(2, derivative + 2)]
            predicted = ((-1) ** derivative * sp.stieltjes(derivative)
                         - complete_bell(arguments, sp.Integer) / (derivative + 1))
            assert sp.simplify(sp.expand(actual - predicted)) == 0
            assert sp.expand(gamma_series).coeff(epsilon, -1) == -1
            records.append({"order": n + 1, "derivative": derivative,
                            "status": "exact symbolic equality"})
    return records


def polynomial_product(left, right, degree):
    result = [sp.S.Zero] * (degree + 1)
    for i, first in enumerate(left):
        if first == 0:
            continue
        for j, second in enumerate(right[: degree + 1 - i]):
            if second != 0:
                result[i + j] += first * second
    return [sp.expand(term) for term in result]


def polynomial_power(poly, exponent, degree):
    result = [sp.S.One] + [sp.S.Zero] * degree
    for _ in range(exponent):
        result = polynomial_product(result, poly, degree)
    return result


def exact_edge_check(m, d, max_q):
    """Revert a generic germ, with all lower coefficients deliberately present."""
    logarithm = sp.symbols("logarithm")
    r, order = m - 1, (m - 1) * max_q
    a = sp.Rational(2)
    b = sp.Rational((-1) ** (m + d - 1), m * (d + 1))
    inverse = [sp.S.One] + [sp.S.Zero] * order
    p_coefficients = [sp.Rational(j + 1, j + 2) for j in range(d)] + [b]
    for n in range(1, order + 1):
        v = inverse[: n + 1]
        residual = [sp.S.Zero] * (n + 1)
        for j in range(n + 1):
            a_j = a if j == 0 else sp.Rational((-1) ** j, j + 1)
            for z, coefficient in enumerate(polynomial_power(v, j + 1, n - j)):
                residual[j + z] += a_j * coefficient / a ** (j + 1)
        if n >= r:
            degree = n - r
            w = [sp.S.Zero] + v[1 : degree + 1]
            log_v = [logarithm] + [sp.S.Zero] * degree
            for j in range(1, degree + 1):
                for z, coefficient in enumerate(polynomial_power(w, j, degree)):
                    log_v[z] += sp.Rational((-1) ** (j + 1), j) * coefficient
            p_at_log_v = [sp.S.Zero] * (degree + 1)
            for j, coefficient in enumerate(p_coefficients):
                for z, term in enumerate(polynomial_power(log_v, j, degree)):
                    p_at_log_v[z] += coefficient * term
            convolution = polynomial_product(
                polynomial_power(v[: degree + 1], m, degree), p_at_log_v, degree
            )
            for z, coefficient in enumerate(convolution):
                residual[r + z] += coefficient / a**m
        inverse[n] = sp.expand(-residual[n])
    for n in range(order + 1):
        assert sp.degree(inverse[n], logarithm) <= d * (n // r)
    for q in range(max_q + 1):
        # Here logarithm = log(y/a); its constant shift does not affect the top degree.
        actual = sp.expand(inverse[r * q] / a).coeff(logarithm, d * q)
        predicted = ((-b) ** q / a ** (m * q + 1)
                     * sp.Rational(comb(m * q, q), r * q + 1))
        assert sp.simplify(actual - predicted) == 0
    return {"m": m, "log_degree": d, "max_q": max_q,
            "status": "exact reversion, degree bound, and highest-log coefficients"}


def exact_lambert_check():
    x, h = sp.symbols("x h")
    c2 = -1 / (4 * (h - 1))
    c3 = 1 / (72 * (h - 1)) + 1 / (8 * (h - 1)**2) + 1 / (32 * (h - 1)**3)
    combined = (4 * h**2 + 28 * h - 23) / (288 * (h - 1)**3)
    assert sp.simplify(c3 - combined) == 0
    t = x + c2 * x**2 + c3 * x**3
    residual = sp.series(t * (h - sp.log(t / x)) + t**2 / 4 - t**3 / 72
                         - h * x, x, 0, 4).removeO().expand()
    assert all(sp.simplify(residual.coeff(x, j)) == 0 for j in range(4))
    return {"status": "exact cancellation through degree three",
            "quadratic_coefficient": str(c2), "cubic_coefficient": str(combined)}


@lru_cache(maxsize=None)
def zeta_derivative(argument, derivative):
    return mp.zeta(argument, derivative=derivative)


@lru_cache(maxsize=None)
def stieltjes(index):
    return mp.stieltjes(index)


def polylog_jet_expansion(order, derivative, t, terms=90):
    n, logarithm = order - 1, mp.log(t)
    harmonic = lambda j: mp.fsum(mp.mpf(v) ** (-j) for v in range(1, n + 1))
    arguments = [logarithm + mp.euler - harmonic(1)]
    arguments += [mp.factorial(j - 1) * (mp.zeta(j) + (-1) ** j * harmonic(j))
                  for j in range(2, derivative + 2)]
    polynomial = ((-1) ** derivative * stieltjes(derivative)
                  - complete_bell(arguments, mp.mpf) / (derivative + 1))
    value = (-t)**n / mp.factorial(n) * polynomial
    value += mp.fsum(zeta_derivative(mp.mpf(order - j), derivative)
                     * (-t)**j / mp.factorial(j)
                     for j in range(terms + 1) if j != n)
    return value


def defining_polylog_sum(order, derivative, t):
    """Exponential series oracle at moderate positive t, with a simple tail bound.

All calls use order >= 1 and derivative <= 2. Then
    (log n)^derivative / n^order <= 1,
so the absolute uncomputed tail is bounded by the geometric tail.
The bound is analytic; the returned floating value is not an interval.
"""
    count = int(mp.ceil((mp.mp.dps + 12) * mp.log(10) / t))
    result = mp.fsum(((-mp.log(n))**derivative if derivative else 1)
                     * mp.exp(-n * t) / mp.mpf(n)**order
                     for n in range(1, count + 1))
    tail = mp.exp(-(count + 1) * t) / (-mp.expm1(-t))
    return result, count, tail


def numerical_jet_checks(tolerance):
    records = []
    for order in range(1, 5):
        for derivative in range(3):
            for t_string in ("0.25", "0.75"):
                t = mp.mpf(t_string)
                predicted = polylog_jet_expansion(order, derivative, t)
                direct, count, tail = defining_polylog_sum(order, derivative, t)
                error = abs(predicted - direct)
                assert error < tolerance
                records.append({"order": order, "derivative": derivative, "t": t_string,
                                "normal_form_terms": 90, "oracle_terms": count,
                                "absolute_error": number(error),
                                "defining_sum_tail_bound": number(tail),
                                "reference": number(direct)})
    return records


def crossover_h(weight, tau):
    return mp.hyp1f1(weight + 1, weight + 2, -tau) / (weight + 1)


@lru_cache(maxsize=None)
def regular_gamma_zero(max_order):
    # Gamma(1-e)/(1+e) = 1 + e G(e).
    logarithm = [mp.mpf(0), mp.euler - 1]
    logarithm += [(mp.zeta(j) + (-1)**j) / j for j in range(2, max_order + 2)]
    coefficients = [mp.mpf(1)]
    for n in range(1, max_order + 2):
        coefficients.append(mp.fsum(j * logarithm[j] * coefficients[n - j]
                                    for j in range(1, n + 1)) / n)
    return tuple(mp.factorial(j) * coefficients[j + 1] for j in range(max_order + 1))


@lru_cache(maxsize=None)
def critical_coefficients(epsilon, weight, terms):
    if epsilon == 0:
        z_jet = (-1)**weight * stieltjes(weight)
        g_jets = regular_gamma_zero(weight)
    else:
        z_jet = mp.diff(lambda e: mp.zeta(1 + e) - 1 / e, epsilon, weight)
        g_jets = tuple(mp.diff(lambda e: mp.gamma(-1 - e) - 1 / e, epsilon, j)
                       for j in range(weight + 1))
    r_coefficients = tuple((-1)**(j + 1 + weight)
                           * zeta_derivative(2 + epsilon - j, weight) / mp.factorial(j)
                           for j in range(2, terms + 1))
    return z_jet, g_jets, r_coefficients


def critical_over_t(t, epsilon, weight, terms=8):
    z_jet, g_jets, r_coefficients = critical_coefficients(epsilon, weight, terms)
    logarithm = -mp.log(t)
    regular = t * mp.polyval(list(reversed(r_coefficients)), t)
    return (logarithm**(weight + 1) * crossover_h(weight, epsilon * logarithm)
            + (-1)**weight * z_jet
            - mp.exp(-epsilon * logarithm)
            * mp.fsum(comb(weight, j) * (-1)**j * g_jets[j] * logarithm**(weight - j)
                       for j in range(weight + 1)) + regular)


def normal_form_checks(tolerance):
    records = []
    t = mp.mpf("0.5")
    for epsilon_string in ("-0.1", "0", "0.1"):
        epsilon = mp.mpf(epsilon_string)
        for weight in range(3):
            jet, count, tail = defining_polylog_sum(2 + epsilon, weight, t)
            direct = (-1)**weight * (zeta_derivative(2 + epsilon, weight) - jet)
            predicted = t * critical_over_t(t, epsilon, weight, terms=90)
            error = abs(predicted / direct - 1)
            assert error < tolerance
            records.append({"weight": weight, "epsilon": epsilon_string, "t": "0.5",
                            "normal_form_terms": 90, "oracle_terms": count,
                            "relative_error": number(error),
                            "defining_sum_tail_bound": number(tail),
                            "reference_deficit": number(direct)})
    return records


def inverse_case(weight, tau, T, tolerance):
    tau, T = mp.mpf(tau), mp.mpf(T)
    epsilon, y = tau / T, mp.exp(-T)
    h_value = crossover_h(weight, tau)
    p = y / T**(weight + 1)

    def equation(v):
        return v * critical_over_t(p * v, epsilon, weight) / T**(weight + 1) - 1

    # Solve in v, whose scale remains moderate even when y is exponentially tiny.
    v = mp.findroot(equation, (mp.mpf("0.8") / h_value, mp.mpf("1.1") / h_value))
    residual = abs(equation(v))
    assert v > 0 and residual < tolerance
    g = mp.exp(-tau) * (mp.log(h_value) - mp.euler + 1)
    if weight == 0:
        g += mp.euler
    leading = 1 / h_value
    corrected = (1 - ((weight + 1) * mp.exp(-tau) * mp.log(T) + g)
                 / (h_value * T)) / h_value
    leading_error, corrected_error = leading / v - 1, corrected / v - 1
    return {"weight": weight, "tau": number(tau), "T": int(T),
            "epsilon": number(epsilon), "y": number(y), "t_numeric": number(p * v),
            "v_numeric": number(v), "v_leading": number(leading),
            "v_first_correction": number(corrected),
            "leading_relative_error": number(leading_error),
            "first_relative_error": number(corrected_error),
            "first_correction_positive": bool(corrected > 0),
            "first_correction_reduces_absolute_error": bool(abs(corrected_error) < abs(leading_error)),
            "normalized_equation_residual": number(residual), "normal_form_terms": 8}


def lambert_diagnostics(tolerance):
    records = []
    for h_integer in (6, 10, 16, 24):
        h = mp.mpf(h_integer)
        x, y = mp.exp(1 - h), h * mp.exp(1 - h)
        c2 = -1 / (4 * (h - 1))
        c3 = (4 * h**2 + 28 * h - 23) / (288 * (h - 1)**3)

        def equation(v):
            return v * critical_over_t(x * v, mp.mpf(0), 0, terms=40) / h - 1

        v = mp.findroot(equation, (mp.mpf("0.99"), mp.mpf(1)))
        t = x * v
        residual = abs(equation(v))
        assert t > 0 and residual < tolerance
        approximations = (x, x + c2 * x**2, x + c2 * x**2 + c3 * x**3)
        errors = [abs(approximation / t - 1) for approximation in approximations]
        assert errors[2] < errors[1] < errors[0]
        records.append({"H": h_integer, "T0": number(x), "y": number(y),
                        "t_numeric": number(t), "leading_relative_error": number(errors[0]),
                        "quadratic_relative_error": number(errors[1]),
                        "cubic_relative_error": number(errors[2]),
                        "cubic_error_scaled_by_T0_fourth_over_H": number(abs(approximations[2] - t) * h / x**4),
                        "normalized_equation_residual": number(residual), "normal_form_terms": 40})
    return records


def write_csv(path, records):
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(records[0]))
        writer.writeheader()
        writer.writerows(records)


def latex_scientific(value, digits=3, signed=False):
    value = mp.mpf(value)
    if value == 0:
        return "0"
    rendered = mp.nstr(value, digits, min_fixed=0, max_fixed=0)
    if "e" in rendered:
        mantissa, exponent = rendered.split("e")
        rendered = mantissa + r"\times10^{" + str(int(exponent)) + "}"
    if signed and value > 0:
        rendered = "+" + rendered
    return rendered


def write_latex_tables(report, destination):
    """Derive article tables from the same stored records as the JSON and CSV."""
    summary = report["summary"]
    inverse_count = (summary["critical_inverse_cases"] + summary["plot_inverse_cases"]
                     + summary["lambert_cases"])
    jet_error = latex_scientific(summary["max_absolute_jet_error"])
    normal_error = latex_scientific(summary["max_relative_normal_form_error"])
    residual = latex_scientific(summary["max_normalized_inverse_residual"])
    rows = [
        ("Gamma--Bell resonance jets", str(summary["exact_resonance_cases"]), "Exact equality"),
        ("Generic logarithmic reversion", str(summary["exact_generic_edge_families"]) + " families",
         "Exact degree and corner checks"),
        ("Lambert inverse coefficients", "1 formula", "Exact through cubic order"),
        ("Resonant jets versus defining sums", str(summary["numerical_jet_cases"]),
         r"Max.\ absolute error $" + jet_error + "$"),
        ("Critical normal form versus defining sums", str(summary["normal_form_comparisons"]),
         r"Max.\ relative error $" + normal_error + "$"),
        ("Positive numerical inverse roots", str(inverse_count),
         r"Max.\ normalized residual $" + residual + "$"),
    ]
    text = [
        "% Generated from data/verification.json by verification/verify.py.",
        r"\begin{center}", r"\small",
        r"\begin{tabular}{@{}p{.43\textwidth}p{.15\textwidth}p{.33\textwidth}@{}}",
        r"\toprule", r"Calculation & Coverage & Recorded result\\", r"\midrule",
    ]
    text += [" & ".join(row) + r"\\[3pt]" for row in rows]
    text += [r"\bottomrule", r"\end{tabular}", r"\end{center}",
             r"{\footnotesize The inverse solves comprise "
             + str(summary["critical_inverse_cases"]) + " selected crossover cases, "
             + str(summary["plot_inverse_cases"]) + " points in the crossover figure, and "
             + str(summary["lambert_cases"]) + " Lambert cases. Numerical values use "
             + str(report["metadata"]["decimal_precision"])
             + r" decimal digits. Residuals refer to the computed normal-form equation; "
             + r"the reported errors are floating-point diagnostics, not interval bounds.\par}"]
    (destination / "verification_table.tex").write_text("\n".join(text) + "\n", encoding="utf-8")

    selected = {(row["weight"], int(mp.mpf(row["tau"])), row["T"]): row
                for row in report["critical_inverse_cases"]}
    text = [
        "% Signed relative errors, generated from the recorded numerical roots.",
        r"\begin{center}", r"\small",
        r"\begin{tabular}{@{}rrrrrr@{}}", r"\toprule",
        r"& & \multicolumn{2}{c}{$T=60$} & \multicolumn{2}{c}{$T=120$}\\",
        r"\cmidrule(lr){3-4}\cmidrule(lr){5-6}",
        r"$k$ & $\tau$ & Leading & First correction & Leading & First correction\\",
        r"\midrule",
    ]
    for weight in range(3):
        for tau in (-2, 0, 2):
            cells = [str(weight), str(tau)]
            for T in (60, 120):
                row = selected[weight, tau, T]
                cells += ["$" + latex_scientific(row[key], signed=True) + "$"
                          for key in ("leading_relative_error", "first_relative_error")]
            text.append(" & ".join(cells) + r"\\")
        if weight != 2:
            text.append(r"\addlinespace[3pt]")
    text += [r"\bottomrule", r"\end{tabular}", r"\end{center}",
             r"{\footnotesize Entries are signed relative errors "
             r"$(t_{\rm approximation}/t_{\rm numerical})-1$. "
             r"An error below $-1$ means that the truncated approximation is negative, "
             r"although the numerical inverse is positive.\par}"]
    (destination / "crossover_table.tex").write_text("\n".join(text) + "\n", encoding="utf-8")


def make_plot(records, destination, T):
    destination.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "axes.labelcolor": "#283444", "text.color": "#283444",
                         "axes.edgecolor": "#64748b", "savefig.facecolor": "white"})
    figure, axes = plt.subplots(1, 3, figsize=(9, 3.0), sharex=True, sharey=True)
    for weight, axis in enumerate(axes):
        rows = [row for row in records if row["weight"] == weight]
        tau = np.array([float(row["tau"]) for row in rows])
        leading = np.abs([float(row["leading_relative_error"]) for row in rows])
        corrected = np.abs([float(row["first_relative_error"]) for row in rows])
        axis.semilogy(tau, leading, "--", color="#315a88", lw=1.65, label="Leading term")
        axis.semilogy(tau, corrected, color="#b44922", lw=1.8, label="First correction")
        axis.set_title(f"Logarithmic weight k = {weight}", fontsize=10)
        axis.set_xlabel(r"Crossover parameter $\tau$")
        axis.grid(True, axis="y", which="major", alpha=0.2)
        axis.set_xlim(-3, 3)
        axis.set_xticks([-3, -1, 1, 3])
    axes[0].set_ylabel("Absolute relative error")
    axes[0].legend(frameon=False, loc="upper right", fontsize=8)
    figure.suptitle(f"Critical inverse approximations at T = {T}", fontsize=12, y=1.01)
    figure.tight_layout(pad=1.0)
    figure.savefig(destination / "critical_crossover_errors.pdf", bbox_inches="tight")
    figure.savefig(destination / "critical_crossover_errors.png", dpi=220, bbox_inches="tight")
    plt.close(figure)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=PACKAGE / "build" / "verification")
    parser.add_argument("--figures", type=Path, default=None)
    parser.add_argument("--dps", type=int, default=85)
    parser.add_argument("--plot-T", type=int, default=240)
    parser.add_argument("--no-plots", action="store_true")
    args = parser.parse_args()
    if args.dps < 70:
        parser.error("Use at least 70 decimal digits for the shipped diagnostic thresholds.")
    mp.mp.dps = args.dps
    tolerance = mp.mpf("1e-60")
    args.output.mkdir(parents=True, exist_ok=True)
    figures = args.figures or args.output / "figures"
    versions = {"mpmath": mp.__version__, "sympy": sp.__version__,
                "numpy": np.__version__, "matplotlib": matplotlib.__version__}
    print("Finite exact symbolic checks...", flush=True)
    exact = {
        "resonant_jets": exact_resonance_checks(),
        "generic_edge_law": [exact_edge_check(*parameters) for parameters in
                             [(2, 1, 5), (2, 2, 4), (2, 3, 3), (3, 1, 3), (3, 2, 3), (4, 1, 2)]],
        "lambert_coefficients": exact_lambert_check(),
    }
    print("Moderate-argument comparisons with independent exponential sums...", flush=True)
    jets = numerical_jet_checks(tolerance)
    normal_forms = normal_form_checks(tolerance)
    print("Weighted critical inverse diagnostics...", flush=True)
    inverses = [inverse_case(weight, tau, T, tolerance) for weight in range(3)
                for tau in (-2, 0, 2) for T in (30, 60, 120)]
    lambert = lambert_diagnostics(tolerance)
    print(f"Computing the crossover error curve at T={args.plot_T}...", flush=True)
    grid = [inverse_case(weight, mp.mpf(j) / 10, args.plot_T, tolerance)
            for weight in range(3) for j in range(-30, 31)]
    summary = {
        "exact_resonance_cases": len(exact["resonant_jets"]),
        "exact_generic_edge_families": len(exact["generic_edge_law"]),
        "numerical_jet_cases": len(jets), "normal_form_comparisons": len(normal_forms),
        "critical_inverse_cases": len(inverses), "plot_inverse_cases": len(grid),
        "lambert_cases": len(lambert),
        "max_absolute_jet_error": number(max(mp.mpf(row["absolute_error"]) for row in jets)),
        "max_relative_normal_form_error": number(max(mp.mpf(row["relative_error"]) for row in normal_forms)),
        "max_normalized_inverse_residual": number(max(mp.mpf(row["normalized_equation_residual"])
                                                     for row in inverses + grid + lambert)),
        "first_correction_reduces_error_cases": sum(row["first_correction_reduces_absolute_error"]
                                                   for row in inverses),
        "nonpositive_first_corrections": [{"weight": row["weight"], "tau": row["tau"], "T": row["T"]}
                                          for row in inverses if not row["first_correction_positive"]],
    }
    report = {
        "metadata": {"generated_utc": datetime.now(timezone.utc).isoformat(),
                     "python": platform.python_version(), "versions": versions,
                     "expected_versions": EXPECTED, "decimal_precision": args.dps,
                     "numeric_comparison_threshold": number(tolerance),
                     "scope": "Finite exact checks and floating-point diagnostics; not an all-order proof or interval certification.",
                     "inverse_reference": "Numerical inversion of the pole-cancelled Jonquiere normal form. Its power series is truncated at the recorded order; moderate-argument comparisons use independent defining exponential sums.",
                     "plot_T": args.plot_T},
        "summary": summary, "exact_checks": exact, "numerical_jet_checks": jets,
        "normal_form_checks": normal_forms, "critical_inverse_cases": inverses,
        "lambert_cases": lambert, "crossover_plot_grid": grid,
    }
    (args.output / "verification.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    for name, records in [("resonant_jets", jets), ("normal_form", normal_forms),
                          ("critical_inverse", inverses), ("lambert_chart", lambert),
                          ("crossover_grid", grid)]:
        write_csv(args.output / f"{name}.csv", records)
    write_latex_tables(report, args.output)
    if not args.no_plots:
        make_plot(grid, figures, args.plot_T)
    (args.output / "summary.txt").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))
    print(f"Saved diagnostics to {args.output}")


if __name__ == "__main__":
    main()
