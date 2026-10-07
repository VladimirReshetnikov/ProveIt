#!/usr/bin/env python3
"""Reproduce finite checks, numerical tables, and the article's two figures.

Run from any directory with ``python code/reproduce.py``.  Exact checks use
Fraction arithmetic and an independent state-space walk enumeration.  Saddle
diagnostics use 60 decimal digits; they are not interval arithmetic.  Large
dimension transition rows are saddle evaluations, not exact enumerations.
"""

from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
from math import comb, factorial, isqrt
from pathlib import Path
from io import BytesIO
import json
import platform
import sys

import mpmath as mp

import walks


ROOT = Path(__file__).resolve().parents[1]
mp.mp.dps = 60


def require(condition, message):
    """Keep all mathematical checks active under python -O."""
    if not condition:
        raise RuntimeError(message)


def number(value):
    if isinstance(value, Fraction):
        return mp.mpf(value.numerator) / value.denominator
    return mp.mpf(value)


def decimal(value, digits=35):
    return mp.nstr(value, digits)


def independent_convolution(left, right, order):
    # Intentionally independent of walks.coefficient_convolution.
    return [sum((left[j] * right[k-j]
                 for j in range(k+1)
                 if j < len(left) and k-j < len(right)), Fraction(0))
            for k in range(order+1)]


def brute_counts(directions, idle, maximum_length):
    """Weighted dynamic enumeration of positions at every small length."""
    dimension = len(directions)
    origin = (0,) * dimension
    increments = [(origin, Fraction(idle))]
    for axis, (positive, negative) in enumerate(directions):
        for sign, weight in [(1, positive), (-1, negative)]:
            step = tuple(sign if j == axis else 0 for j in range(dimension))
            increments.append((step, Fraction(weight)))
    states = {origin: Fraction(1)}
    answer = [Fraction(1)]
    for _ in range(maximum_length):
        following = defaultdict(Fraction)
        for point, mass in states.items():
            for increment, weight in increments:
                if weight:
                    destination = tuple(x+y for x, y in zip(point, increment))
                    following[destination] += mass * weight
        states = following
        answer.append(states.get(origin, Fraction(0)))
    return answer


def exact_checks():
    count = defaultdict(int)
    evidence = []
    order = 12
    factor = [Fraction(1, factorial(k)**2) for k in range(order+1)]
    power = [Fraction(1)] + [Fraction(0)] * order
    for dimension in range(7):
        recurrence = walks.axis_coefficients(dimension, order)
        for k in range(order+1):
            require(recurrence[k] == power[k] * factorial(k)**2,
                    f"Miller/convolution disagreement at D={dimension}, k={k}")
            count["miller_vs_independent_fraction_coefficients"] += 1
            evidence.append(str(recurrence[k]))
        power = independent_convolution(power, factor, order)

    for dimension in range(4):
        for idle in [Fraction(0), Fraction(1), Fraction(3, 2)]:
            brute = brute_counts([(1, 1)] * dimension, idle, 8)
            for length, result in enumerate(brute):
                require(result == walks.exact_count(length, dimension, idle),
                        f"Brute isotropic mismatch: N={length}, D={dimension}")
                count["brute_isotropic_return_counts"] += 1
                evidence.append(str(result))

    for dimension in range(6):
        for idle in [Fraction(0), Fraction(1), Fraction(3, 2)]:
            for length in range(11):
                left = walks.exact_count(length, dimension, idle)
                right = walks.exact_anisotropic(length, [1] * dimension, idle)
                require(left == right, "Isotropic/parity convolution disagreement")
                count["isotropic_vs_parity_convolution"] += 1

    asymmetric = [
        ([(Fraction(1, 2), Fraction(3, 2))], Fraction(2, 3)),
        ([(Fraction(1, 2), Fraction(3, 2)),
          (Fraction(2), Fraction(3, 4))], Fraction(1, 3)),
        ([(Fraction(0), Fraction(2)),
          (Fraction(2, 3), Fraction(3, 2)),
          (Fraction(5, 4), Fraction(4, 5))], Fraction(0)),
        ([], Fraction(3, 2)),
    ]
    for directions, idle in asymmetric:
        pair_weights = [a*b for a, b in directions]
        for length, result in enumerate(brute_counts(directions, idle, 8)):
            require(result == walks.exact_anisotropic(length, pair_weights, idle),
                    f"Asymmetric rational mismatch: {directions}, N={length}")
            count["brute_asymmetric_rational_return_counts"] += 1
            evidence.append(str(result))

    # The zero pair cannot be used in a returning path, despite its nonzero
    # one-way directional activity in the third asymmetric example.
    for length in range(11):
        require(walks.exact_anisotropic(length, [0, 1, 1], 0)
                == walks.exact_count(length, 2, 0), "Inactive-axis mismatch")
        count["inactive_axis_identities"] += 1
    return {
        "case_counts": dict(count),
        "all_passed": True,
        "integer_rational_evidence_sha256": sha256(
            "\n".join(evidence).encode("ascii")).hexdigest(),
        "largest_brute_length": 8,
        "largest_brute_dimension": 3,
        "miller_coefficient_order": order,
        "description": "Exact arithmetic; no floating-point decisions.",
    }


def nonlazy_counterexample():
    """Two independent exact counts and the requested rational pi certificate."""
    dimension, length, order = 16, 26, 13
    coefficient = [Fraction(1)] + [Fraction(0)] * order
    factor = [Fraction(1, factorial(k)**2) for k in range(order+1)]
    for _ in range(dimension):
        coefficient = independent_convolution(coefficient, factor, order)
    independent = factorial(length) * coefficient[order]
    miller = walks.exact_count(length, dimension, 0)
    expected = 23062502564288544059408295833600
    require(independent == miller == expected, "Nonlazy counterexample count mismatch")
    left = expected * 333**8 * 13**8
    right = 2 * 4**8 * 32**26 * 106**8
    difference = left-right
    require(difference > 0, "Nonlazy counterexample integer certificate failed")
    lower_ratio = Fraction(left, right)
    actual_ratio = (mp.mpf(expected)/mp.mpf(32)**26
                    /(2*(mp.mpf(4)/(13*mp.pi))**8))
    return {
        "dimension": dimension, "length": length, "idle": 0,
        "exact_count": str(expected),
        "independent_fraction_convolution_count": str(independent),
        "miller_recurrence_count": str(miller),
        "pi_bound_used": "333/106 < pi; this analytic bound is supplied in the article.",
        "comparison": "C*333^8*13^8 > 2*4^8*32^26*106^8",
        "strict_integer_difference": str(difference),
        "reduced_ratio_lower_numerator": str(lower_ratio.numerator),
        "reduced_ratio_lower_denominator": str(lower_ratio.denominator),
        "ratio_lower_decimal": decimal(number(lower_ratio)),
        "ratio_using_numerical_pi": decimal(actual_ratio),
        "conjectured_bound": "2*(D/(2*pi*N))^(D/2), compared with C/(2D)^N",
        "scope": "One exact counterexample. No minimality or first-violation claim.",
        "all_integer_checks_passed": True,
    }


def explicit_terms(cumulants):
    b = cumulants[2]
    k3, k4, k5, k6 = cumulants[3:7]
    first = k4/(8*b**2) - 5*k3**2/(24*b**3)
    second = (-k6/(48*b**3) + 7*k3*k5/(48*b**4)
              + 35*k4**2/(384*b**4) - 35*k3**2*k4/(64*b**5)
              + 385*k3**4/(1152*b**6))
    return first, second


def numerical_case(length, dimension=None, idle=1, pair_weights=None, regime=""):
    idle = Fraction(idle)
    if pair_weights is None:
        exact = walks.exact_count(length, dimension, idle)
        result = walks.saddle(length, dimension=dimension, idle=number(idle))
    else:
        pair_weights = list(map(Fraction, pair_weights))
        exact = walks.exact_anisotropic(length, pair_weights, idle)
        result = walks.saddle(length, idle=number(idle),
                              pair_weights=list(map(number, pair_weights)))
    row = {
        "length": length, "m": length//2, "parity": length % 2,
        "dimension": dimension if pair_weights is None else len(pair_weights),
        "idle": str(idle), "regime": regime,
        "pair_weights": None if pair_weights is None else list(map(str, pair_weights)),
        "exact_zero": exact == 0,
        "reference": "Exact integer/rational finite formula, evaluated at 60 digits.",
    }
    if exact == 0:
        require(result["zero"], "Saddle failed to preserve an exact zero boundary")
        return row
    require(not result["zero"], "Nonzero count incorrectly classified as zero")
    m = length//2
    b = result["variance"]
    tolerance = mp.mpf("1e-48")
    require(abs(result["mean"]-m) < tolerance * max(1, m), "Saddle mean residual")
    require(b >= m/2-tolerance*m and b <= m+tolerance*m, "Variance sandwich")
    c1, c2 = explicit_terms(result["cumulants"])
    require(abs(c1-result["terms"][1]) < tolerance, "First correction disagreement")
    require(abs(c2-result["terms"][2]) < tolerance, "Second correction disagreement")
    log_exact = mp.log(number(exact))
    ratios, errors = [], []
    for order in range(3):
        correction = mp.fsum(result["terms"][:order+1])
        require(correction > 0, "Nonpositive correction in finite diagnostic grid")
        log_difference = result["log_leading"] + mp.log(correction) - log_exact
        errors.append(mp.expm1(log_difference))
        ratios.append(mp.exp(log_difference))
    # The proved statement bounds exact/leading-1, whereas the displayed
    # approximation errors below use approximation/exact-1. Test the theorem
    # in its stated orientation to avoid silently exchanging denominators.
    exact_over_leading_error = mp.expm1(log_exact-result["log_leading"])
    require(abs(exact_over_leading_error) <= 12/b + tolerance,
            "Explicit leading-error bound violated")
    row.update({
        "saddle_t": decimal(result["t"]),
        "variance": decimal(b), "variance_over_m": decimal(b/m),
        "mean_residual": decimal(result["mean"]-m),
        "cumulants_2_through_6": [decimal(v) for v in result["cumulants"][2:7]],
        "E1": decimal(c1), "E2": decimal(c2),
        "log_exact_count": decimal(log_exact),
        "approximation_over_exact_errors": [decimal(v) for v in errors],
        "exact_over_leading_error": decimal(exact_over_leading_error),
        "proved_exact_over_leading_envelope": decimal(12/b),
        "bound_utilization": decimal(abs(exact_over_leading_error)*b/12),
    })
    return row


def numerical_checks():
    rows = []
    for base in [40, 80, 160]:
        m = base//2
        for epsilon in [0, 1]:
            for regime, dimension in [("sparse", m*m), ("balanced", m),
                                      ("dense", max(1, m//10))]:
                for idle in [0, 1, 2*dimension+1]:
                    rows.append(numerical_case(base+epsilon, dimension, idle,
                                               regime=regime))
            for idle in [0, 1, 7]:
                rows.append(numerical_case(base+epsilon, 0, idle, regime="idle-only"))
            for pair_weights, idle in [
                ([Fraction(1, 7), Fraction(3, 2), Fraction(5)], Fraction(2, 3)),
                ([Fraction(0), Fraction(3, 4), Fraction(3, 2)], Fraction(0)),
            ]:
                rows.append(numerical_case(base+epsilon, idle=idle,
                                           pair_weights=pair_weights,
                                           regime="anisotropic rational"))
    nonzero = [row for row in rows if not row["exact_zero"]]
    summary = []
    for m in [20, 40, 80]:
        selected = [row for row in nonzero if row["m"] == m]
        summary.append({
            "m": m, "nonzero_cases": len(selected),
            "max_abs_approximation_over_exact_error": [
                decimal(max(abs(mp.mpf(row["approximation_over_exact_errors"][j]))
                            for row in selected)) for j in range(3)],
            "max_abs_exact_over_approximation_error": [
                decimal(max(abs(mp.expm1(-mp.log1p(mp.mpf(
                    row["approximation_over_exact_errors"][j]))))
                            for row in selected)) for j in range(3)],
            "max_abs_exact_over_leading_error": decimal(max(
                abs(mp.mpf(row["exact_over_leading_error"])) for row in selected)),
            "universal_exact_over_leading_envelope_24_over_m": decimal(mp.mpf(24)/m),
        })
    return rows, summary


def dense_transition():
    rows = []
    for dimension in [100, 1600, 25600, 409600]:
        root = isqrt(dimension)
        require(root*root == dimension, "Dense grid expects square dimensions")
        for c in [Fraction(1, 2), Fraction(1), Fraction(2)]:
            base = int(c * dimension * root)
            base -= base % 2
            for epsilon in [0, 1]:
                length = base+epsilon
                result = walks.saddle(length, dimension=dimension, idle=1, order=2)
                log_gaussian = dimension/2 * mp.log(
                    mp.mpf(2*dimension+1)/(4*mp.pi*length))
                normalization = length*mp.log(2*dimension+1) + log_gaussian
                lead = mp.exp(result["log_leading"]-normalization)
                corrected = mp.exp(result["log_count"]-normalization)
                limit = mp.exp(1/(48*number(c)**2))
                rows.append({
                    "dimension": dimension, "length": length,
                    "parity": epsilon, "nominal_s": str(c),
                    "N_over_D_to_three_halves": decimal(
                        mp.mpf(length)/(dimension*root)),
                    "leading_saddle_return_over_gaussian": decimal(lead),
                    "E2_saddle_return_over_gaussian": decimal(corrected),
                    "limiting_ratio": decimal(limit),
                    "log_ratio_dense_two_term_prediction": decimal(
                        -mp.mpf(3)*dimension/(16*length)
                        +mp.mpf(dimension)**3/(48*length**2)),
                    "variance": decimal(result["variance"]),
                    "leading_analytic_relative_envelope": decimal(12/result["variance"]),
                    "reference": "Numerical parity saddle; no exact count computed.",
                })
    return rows


def sparse_transition():
    rows = []
    for m in [20, 40, 80, 160]:
        dimension = m*m
        q = walks.axis_coefficients(dimension, m)
        for epsilon in [0, 1]:
            length = 2*m+epsilon
            # theta=beta=1 implies lambda^2=m. After removing lambda^epsilon
            # every term is an integer; use that exact normalized count.
            exact_normalized = sum(comb(length, 2*k)*comb(2*k, k)*q[k]*m**(m-k)
                                   for k in range(m+1))
            def h(c):
                x = mp.sqrt(c)
                return mp.cosh(x) if epsilon == 0 else mp.sinh(x)/x
            value = h(mp.mpf(1))
            first = mp.diff(h, mp.mpf(1), 1)
            second = mp.diff(h, mp.mpf(1), 2)
            correction = mp.mpf(1)/4-mp.mpf(1)/72+first/(2*value)-second/(2*value)
            log_lead = (mp.loggamma(length+1)+m*mp.log(dimension)
                        -mp.loggamma(m+1)-mp.mpf(1)/4+mp.log(value))
            log_exact = mp.log(exact_normalized)
            error0 = mp.expm1(log_lead-log_exact)
            error1 = mp.expm1(log_lead+mp.log1p(correction/m)-log_exact)
            rows.append({
                "m": m, "length": length, "dimension": dimension,
                "parity": epsilon, "theta": "1", "beta": "1",
                "idle_squared": m, "first_correction_coefficient": decimal(correction),
                "leading_over_exact_error": decimal(error0),
                "corrected_over_exact_error": decimal(error1),
                "m_squared_times_corrected_error": decimal(m*m*error1),
                "reference": "Exact integer normalized count; lambda^parity removed.",
            })
    return rows


def tex_scientific(value):
    value = mp.mpf(value)
    if not value:
        return "$0$"
    exponent = int(mp.floor(mp.log10(abs(value))))
    mantissa = value/mp.power(10, exponent)
    return "$"+mp.nstr(mantissa, 4)+"\\times10^{"+str(exponent)+"}$"


def write_tables(summary, dense, sparse):
    row_end = chr(92) * 2
    out = [
        "% Generated by code/reproduce.py at 60 decimal digits.",
        "\\begin{table}[tbp]", "\\centering", "\\small",
        "\\begin{tabular}{rrrrr}", "\\toprule",
        "$m$ & Cases & Leading & Through $E_1$ & Through $E_2$ "+row_end,
        "\\midrule",
    ]
    for row in summary:
        errors = row["max_abs_approximation_over_exact_error"]
        out.append(f"{row['m']} & {row['nonzero_cases']} & "
                   +" & ".join(tex_scientific(x) for x in errors)+" "+row_end)
    out += ["\\bottomrule", "\\end{tabular}",
            "\\caption{Maximum observed absolute relative error, with the exact count "
            "in the denominator, over the nonzero finite verification cases at each "
            "$m$. The grid includes both parities, sparse, balanced, dense, idle-only, "
            "and rational anisotropic cases. Higher-order columns are numerical "
            "diagnostics, not finite error certificates.}",
            "\\label{tab:verification-errors}", "\\end{table}", "",
            "\\begin{table}[tbp]", "\\centering", "\\small",
            "\\begin{tabular}{rrrrr}", "\\toprule",
            "$D$ & $s$ & Even $N$ & Odd $N$ & $e^{1/(48s^2)}$ "+row_end,
            "\\midrule"]
    for dimension in [100, 1600, 25600, 409600]:
        for c in ["1/2", "1", "2"]:
            pair = [r for r in dense if r["dimension"] == dimension and r["nominal_s"] == c]
            pair.sort(key=lambda r: r["parity"])
            nums = [mp.nstr(mp.mpf(r["E2_saddle_return_over_gaussian"]), 9) for r in pair]
            limit = mp.nstr(mp.mpf(pair[0]["limiting_ratio"]), 9)
            out.append(f"{dimension} & ${c}$ & {nums[0]} & {nums[1]} & {limit} "+row_end)
    out += ["\\bottomrule", "\\end{tabular}",
            "\\caption{Dense transition: parity saddle approximations through $E_2$, "
            "divided by the Gaussian prediction, at even $N=sD^{3/2}$ and the next "
            "odd integer. These large-dimension entries are saddle evaluations, "
            "not exact walk counts.}",
            "\\label{tab:verification-dense}", "\\end{table}", "",
            "\\begin{table}[tbp]", "\\centering", "\\small",
            "\\begin{tabular}{rrrrr}", "\\toprule",
            "$m$ & Even, leading & Even, corrected & Odd, leading & Odd, corrected "+row_end,
            "\\midrule"]
    for m in [20, 40, 80, 160]:
        pair = sorted([r for r in sparse if r["m"] == m], key=lambda r: r["parity"])
        values = [pair[0]["leading_over_exact_error"], pair[0]["corrected_over_exact_error"],
                  pair[1]["leading_over_exact_error"], pair[1]["corrected_over_exact_error"]]
        out.append(str(m)+" & "+" & ".join(tex_scientific(x) for x in values)+" "+row_end)
    out += ["\\bottomrule", "\\end{tabular}",
            "\\caption{Sparse count formula at $\\theta=\\beta=1$: signed relative "
            "errors against exact normalized integer counts, before and after the "
            "$1/m$ correction. Here $D=m^2$ and $\\lambda^2=m$.}",
            "\\label{tab:verification-sparse}", "\\end{table}", ""]
    (ROOT/"data"/"numerical_tables.tex").write_text("\n".join(out), encoding="utf-8")


def make_figures(summary, dense):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import NullFormatter, NullLocator
    plt.rcParams.update({"font.size": 10, "axes.titlesize": 12,
                         "axes.labelsize": 11, "pdf.fonttype": 42,
                         "ps.fonttype": 42, "figure.dpi": 150,
                         "savefig.dpi": 180})
    colors = ["#1f77b4", "#d97706", "#16856d"]
    figure, axis = plt.subplots(figsize=(7.1, 4.5), layout="constrained")
    m_values = [r["m"] for r in summary]
    for order, label in enumerate(["Leading saddle", r"Through $E_1$", r"Through $E_2$"]):
        values = [float(mp.mpf(r["max_abs_exact_over_approximation_error"][order]))
                  for r in summary]
        axis.loglog(m_values, values, "o-", color=colors[order], label=label, linewidth=1.8)
    axis.loglog(m_values, [24/m for m in m_values], "--", color="#666666",
                label="Proved 24/m envelope for leading saddle", linewidth=1.3)
    axis.set_xticks(m_values, labels=[str(x) for x in m_values])
    axis.xaxis.set_minor_locator(NullLocator())
    axis.xaxis.set_minor_formatter(NullFormatter())
    axis.set_xlabel(r"Half-length $m$")
    axis.set_ylabel("Maximum |exact / approximation - 1|")
    axis.set_title("Finite-grid errors across weights, dimensions, and parities")
    axis.grid(True, which="major", alpha=0.2)
    axis.legend(loc="upper center", bbox_to_anchor=(0.5, -0.17), ncol=2, fontsize=9)
    save_figure(figure, "uniform_errors")
    plt.close(figure)

    figure, axis = plt.subplots(figsize=(7.1, 4.5), layout="constrained")
    for index, c in enumerate(["1/2", "1", "2"]):
        even = sorted([r for r in dense if r["nominal_s"] == c and r["parity"] == 0],
                      key=lambda r: r["dimension"])
        odd = sorted([r for r in dense if r["nominal_s"] == c and r["parity"] == 1],
                     key=lambda r: r["dimension"])
        dimensions = [r["dimension"] for r in even]
        axis.semilogx(dimensions, [float(mp.mpf(r["E2_saddle_return_over_gaussian"])) for r in even],
                      "o-", label=f"s = {c}, even", color=colors[index], linewidth=1.8)
        axis.semilogx(dimensions, [float(mp.mpf(r["E2_saddle_return_over_gaussian"])) for r in odd],
                      "s:", label=f"s = {c}, odd", color=colors[index],
                      markerfacecolor="none", linewidth=1)
        axis.axhline(float(mp.mpf(even[0]["limiting_ratio"])), color=colors[index],
                     linestyle="--", linewidth=0.8, alpha=0.65)
    axis.set_xlabel(r"Dimension $D$")
    axis.set_ylabel("Saddle return / Gaussian prediction")
    axis.set_title(r"Critical scale $N\simeq sD^{3/2}$")
    axis.grid(True, alpha=0.2)
    axis.legend(loc="upper center", bbox_to_anchor=(0.5, -0.17), ncol=3, fontsize=9)
    axis.text(0.03, 0.70, "Dashed lines: exp(1 / (48 s²))\nSaddle evaluations, not exact counts",
              transform=axis.transAxes, va="top", fontsize=9,
              bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.95})
    save_figure(figure, "dense_transition")
    plt.close(figure)


def save_figure(figure, stem):
    """Write complete encodings before exposing the destination path."""
    from PIL import Image
    for suffix in ["pdf", "png"]:
        buffer = BytesIO()
        options = {"metadata": {"CreationDate": None}} if suffix == "pdf" else {}
        figure.savefig(buffer, format=suffix, **options)
        if suffix == "png":
            buffer.seek(0)
            Image.open(buffer).verify()
        target = ROOT/"figures"/(stem+"."+suffix)
        temporary = target.with_suffix(target.suffix+".tmp")
        temporary.write_bytes(buffer.getvalue())
        temporary.replace(target)


def scale_invariance_checks():
    """Check the saddle across 240 orders of pair-activity scale."""
    length = 63
    weights = [mp.mpf(1), mp.mpf(3), mp.mpf(0)]
    baseline = walks.saddle(length, pair_weights=weights, idle=2, order=2)
    rows = []
    for exponent in [-120, 120]:
        scale = mp.power(10, exponent)
        current = walks.saddle(length, pair_weights=[c*scale**2 for c in weights],
                               idle=2*scale, order=2)
        log_residual = (current["log_count"]-baseline["log_count"]
                        - length*mp.log(scale))
        root_residual = current["t"]*scale**2/baseline["t"]-1
        variance_residual = current["variance"]/baseline["variance"]-1
        for value in [log_residual, root_residual, variance_residual]:
            require(abs(value) < mp.mpf("1e-40"),
                    "Extreme activity scaling failed")
        rows.append({"directional_scale_power_of_10": exponent,
                     "pair_scale_power_of_10": 2*exponent,
                     "log_count_residual": decimal(log_residual),
                     "relative_saddle_residual": decimal(root_residual),
                     "relative_variance_residual": decimal(variance_residual),
                     "passed": True})
    return rows


def main():
    (ROOT/"data").mkdir(exist_ok=True)
    (ROOT/"figures").mkdir(exist_ok=True)
    scaling = scale_invariance_checks()
    exact = exact_checks()
    print("Exact checks:", sum(exact["case_counts"].values()), "passed", flush=True)
    certificate = nonlazy_counterexample()
    print("Nonlazy D=16, N=26: independent exact count and strict integer certificate passed.",
          flush=True)
    numerical, summary = numerical_checks()
    zero_count = sum(r["exact_zero"] for r in numerical)
    print("Finite saddle cases:", len(numerical), "including", zero_count,
          "exact-zero boundaries", flush=True)
    dense = dense_transition()
    print("Large-dimension saddle transition cases:", len(dense), flush=True)
    sparse = sparse_transition()
    write_tables(summary, dense, sparse)
    make_figures(summary, dense)
    nonzero = [r for r in numerical if not r["exact_zero"]]
    result = {
        "description": "Reproducible supporting computation for Uniform Lattice Bridges.",
        "precision_decimal_digits": mp.mp.dps,
        "software": {"python": platform.python_version(), "mpmath": mp.__version__},
        "verification_conventions": {
            "exact_checks": "Fraction arithmetic and independent dynamic enumeration.",
            "numeric_checks": "60-digit evaluation, not interval arithmetic.",
            "higher_order_errors": "Observed residuals only; no finite universal constants asserted.",
            "explicit_bound_orientation": "The theorem bounds exact/leading-1, not leading/exact-1.",
            "dense_rows": "Computed from the parity saddle; exact counts are not evaluated.",
        },
        "exact_checks": exact,
        "extreme_scale_invariance_checks": scaling,
        "nonlazy_upper_bound_counterexample": certificate,
        "numerical_summary": {
            "total_cases": len(numerical), "nonzero_cases": len(nonzero),
            "exact_zero_cases": zero_count,
            "all_mean_variance_correction_and_envelope_checks_passed": True,
            "smallest_variance_over_m": min(
                (r["variance_over_m"] for r in nonzero), key=mp.mpf),
            "largest_variance_over_m": max(
                (r["variance_over_m"] for r in nonzero), key=mp.mpf),
            "maximum_proved_bound_utilization": max(
                (r["bound_utilization"] for r in nonzero), key=mp.mpf),
            "by_half_length": summary,
        },
        "numerical_cases": numerical,
        "dense_transition": dense,
        "sparse_transition": sparse,
    }
    (ROOT/"data"/"verification.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")
    print("Sparse normalized exact comparisons:", len(sparse), flush=True)
    print("Wrote data/verification.json, data/numerical_tables.tex, and four figure files.",
          flush=True)


if __name__ == "__main__":
    main()
