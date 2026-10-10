#!/usr/bin/env python3
"""Reproduce ordinary Hurwitz and log-Gamma correlation diagnostics and a figure.

Requirements: Python 3, mpmath, numpy, matplotlib.

    python check_gamma_correlations.py
    python check_gamma_correlations.py --quick

The default uses 48 decimal working digits.  --quick uses 32 digits and fewer
parameters/Cauchy samples.  Every numerical parameter is fixed; no random
sampling is used.  Results are written beside this script as results_gamma.json,
and a PDF/PNG figure is written to ../figures/loggamma_correlation.*.

The real-space integrals, convergent cusp series, reflected zeta identity, and
Cauchy order derivatives are evaluated independently where practical.  These
are numerical diagnostics, not interval-certified enclosures or proofs.

The public helper contour_derivatives can also be imported by other checks.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import platform
import time

import mpmath as mp


def contour_derivatives(func, center, max_order, nodes=64, radius=None):
    """Cauchy derivatives by a fixed half-offset trapezoidal circle.

    Returns derivatives of orders 0,...,max_order.  A half-step offset avoids
    evaluating precisely on the real axis.  The caller controls mp.mp.dps.
    This routine supplies no rigorous discretization/roundoff error bound.
    """
    radius = mp.mpf("0.125") if radius is None else mp.mpf(radius)
    center = mp.mpc(center)
    samples = []
    for j in range(nodes):
        angle = 2 * mp.pi * (mp.mpf(j) + mp.mpf("0.5")) / nodes
        phase = mp.exp(1j * angle)
        samples.append((phase, func(center + radius * phase)))
    return [
        mp.factorial(k)
        * mp.fsum(value / phase**k for phase, value in samples)
        / (nodes * radius**k)
        for k in range(max_order + 1)
    ]


def shifted_hurwitz_formula(s, t, a):
    phase = mp.exp(0.5j * mp.pi * (s - t))
    return (
        mp.gamma(1 - s)
        * mp.gamma(1 - t)
        * (2 * mp.pi) ** (s + t - 2)
        * (
            phase * mp.polylog(2 - s - t, mp.exp(-2j * mp.pi * a))
            + mp.polylog(2 - s - t, mp.exp(2j * mp.pi * a)) / phase
        )
    )


def shifted_hurwitz_integral(s, t, a):
    """Real integral after exact subtraction of both leading endpoint powers."""
    b = 1 - a

    def first(x):
        if x == 0:
            return mp.zeta(s) * mp.zeta(t, a)
        return (
            x ** (-s) * (mp.zeta(t, a + x) - mp.zeta(t, a))
            + mp.zeta(s, 1 + x) * mp.zeta(t, a + x)
        )

    def second(y):
        if y == 0:
            return mp.zeta(t) * mp.zeta(s, b)
        return (
            y ** (-t) * (mp.zeta(s, b + y) - mp.zeta(s, b))
            + mp.zeta(t, 1 + y) * mp.zeta(s, b + y)
        )

    return (
        mp.quad(first, [0, b / 2, b])
        + mp.quad(second, [0, a / 2, a])
        + mp.zeta(t, a) * b ** (1 - s) / (1 - s)
        + mp.zeta(s, b) * a ** (1 - t) / (1 - t)
    )


def gamma_correlation_integral(a):
    b = 1 - a
    return mp.quad(
        lambda x: mp.loggamma(x) * mp.loggamma(x + a), [0, b / 2, b]
    ) + mp.quad(
        lambda x: mp.loggamma(x + b) * mp.loggamma(x), [0, a / 2, a]
    )


def reflected_gamma_integral(a):
    """Integral logGamma(x) logGamma({a-x}); use symmetry in the first piece."""
    return 2 * mp.quad(
        lambda x: mp.loggamma(x) * mp.loggamma(a - x), [0, a / 4, a / 2]
    ) + mp.quad(
        lambda x: mp.loggamma(x) * mp.loggamma(1 + a - x),
        [a, (1 + a) / 2, 1],
    )


def reflected_gamma_formula(a):
    z = lambda s: mp.zeta(s, a)
    return (
        mp.log(2 * mp.pi) ** 2 / 4
        + mp.diff(z, -1, 2)
        + 2 * mp.diff(z, -1)
        + (2 - mp.zeta(2)) * z(-1)
    )


def gamma_correlation_zero():
    ell = mp.log(2 * mp.pi)
    cap_a = mp.euler + ell
    return ell**2 / 4 + (
        (cap_a**2 + mp.pi**2 / 4) * mp.zeta(2)
        - 2 * cap_a * mp.diff(mp.zeta, 2)
        + mp.diff(mp.zeta, 2, 2)
    ) / (2 * mp.pi**2)


def cusp_coefficients(count):
    return [
        mp.harmonic(2 * m) * mp.zeta(2 * m + 1)
        + mp.diff(mp.zeta, 2 * m + 1)
        for m in range(1, count + 1)
    ]


def gamma_correlation_series(a, r_zero, coefficients):
    a = min(a, 1 - a)
    if a == 0:
        return r_zero
    cusp = a / 2 * (mp.log(a) ** 2 - 2 * mp.log(a) + 2 + mp.pi**2 / 3)
    return r_zero - cusp + (mp.zeta(2) - mp.stieltjes(1)) * a**2 + mp.fsum(
        value * a ** (2 * m + 2) / ((m + 1) * (2 * m + 1))
        for m, value in enumerate(coefficients, start=1)
    )


def gamma_curvature_series(a, coefficients):
    a = min(a, 1 - a)
    return (
        -mp.log(a) / a
        + 2 * (mp.zeta(2) - mp.stieltjes(1))
        + 2 * mp.fsum(
            value * a ** (2 * m)
            for m, value in enumerate(coefficients, start=1)
        )
    )


def polylog_gamma_value(a, derivatives):
    cap_a = mp.euler + mp.log(2 * mp.pi)
    return mp.log(2 * mp.pi) ** 2 / 4 + (
        (cap_a**2 + mp.pi**2 / 4) * derivatives[0]
        - 2 * cap_a * derivatives[1]
        + derivatives[2]
    ) / (2 * mp.pi**2)


def make_figure(directory, r_zero, coefficients, r_min, curvature_min):
    """Vector PDF and high-resolution PNG; curve evaluation is a fast series."""
    import numpy as np
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import LogLocator, NullFormatter

    directory.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update(
        {
            "font.family": "serif",
            "font.serif": ["DejaVu Serif"],
            "mathtext.fontset": "stix",
            "font.size": 10,
            "axes.titlesize": 11,
            "axes.labelsize": 11,
            "xtick.labelsize": 9,
            "ytick.labelsize": 9,
            "axes.edgecolor": "#687584",
            "axes.linewidth": 0.65,
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
            "savefig.facecolor": "white",
        }
    )
    grid = np.unique(
        np.concatenate(
            [
                [0.0, 1.0],
                np.linspace(0.0001, 0.9999, 801),
                np.geomspace(1e-6, 0.03, 240),
                1 - np.geomspace(1e-6, 0.03, 240),
            ]
        )
    )
    reduced = np.minimum(grid, 1 - grid)
    positive = reduced > 0
    r = np.full_like(grid, float(r_zero))
    t = reduced[positive]
    log_t = np.log(t)
    zeta2 = float(mp.zeta(2))
    gamma1 = float(mp.stieltjes(1))
    r[positive] += (
        -t / 2 * (log_t**2 - 2 * log_t + 2 + math.pi**2 / 3)
        + (zeta2 - gamma1) * t**2
    )
    curv = -log_t / t + 2 * (zeta2 - gamma1)
    for m, value in enumerate(coefficients, start=1):
        value = float(value)
        power = t ** (2 * m)
        r[positive] += value * power * t**2 / ((m + 1) * (2 * m + 1))
        curv += 2 * value * power

    navy, teal = "#193D58", "#087E8B"
    fig, axes = plt.subplots(1, 2, figsize=(9.2, 3.65), layout="constrained")
    for ax in axes:
        ax.set_xlim(0, 1)
        ax.set_xlabel(r"Circular shift $a$")
        ax.set_xticks([0, 0.25, 0.5, 0.75, 1])
        ax.set_xticklabels(["0", "0.25", "0.50", "0.75", "1"])
        ax.spines[["top", "right"]].set_visible(False)
        ax.grid(axis="y", color="#D8E0E6", linewidth=0.55, alpha=0.85)
        ax.tick_params(length=3, width=0.65)

    axes[0].plot(grid, r, color=navy, linewidth=1.7)
    axes[0].scatter([0.5], [float(r_min)], color=teal, s=22, zorder=4)
    axes[0].set_title("(a) Log-Gamma correlation", loc="left", pad=10)
    axes[0].set_ylabel(r"$R(a)$")
    axes[0].set_ylim(0.43, float(r_zero) + 0.11)
    axes[0].annotate(
        r"$R(1/2)\approx %.6f$" % float(r_min),
        xy=(0.5, float(r_min)),
        xytext=(0.5, 0.72),
        ha="center",
        va="bottom",
        color=teal,
        fontsize=10,
        arrowprops={"arrowstyle": "-", "color": teal, "linewidth": 0.65},
    )
    axes[0].text(
        0.5, 0.95, r"$R(a)=R(1-a)$", transform=axes[0].transAxes,
        ha="center", va="top", fontsize=10, color="#465766"
    )

    axes[1].plot(grid[positive], curv, color=teal, linewidth=1.7)
    axes[1].set_yscale("log")
    axes[1].set_ylim(4.5, 1e5)
    axes[1].set_title("(b) Strictly positive curvature", loc="left", pad=10)
    axes[1].set_ylabel(r"$R''(a)$  (log scale)")
    axes[1].yaxis.set_major_locator(LogLocator(base=10, numticks=6))
    axes[1].yaxis.set_minor_formatter(NullFormatter())
    axes[1].scatter([0.5], [float(curvature_min)], color=navy, s=22, zorder=4)
    axes[1].annotate(
        r"$R''(1/2)\approx %.6f$" % float(curvature_min),
        xy=(0.5, float(curvature_min)),
        xytext=(0.5, 18),
        ha="center",
        color=navy,
        fontsize=10,
        arrowprops={"arrowstyle": "-", "color": navy, "linewidth": 0.65},
    )
    axes[1].text(
        0.5, 0.95, "Curvature diverges at both endpoints",
        transform=axes[1].transAxes, ha="center", va="top",
        fontsize=9, color="#465766"
    )

    paths = [directory / "loggamma_correlation.pdf", directory / "loggamma_correlation.png"]
    fig.savefig(paths[0], bbox_inches="tight", metadata={"Title": "Circular log-Gamma correlation and curvature"})
    fig.savefig(paths[1], dpi=240, bbox_inches="tight")
    plt.close(fig)
    return paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="32 digits and a smaller fixed test set")
    parser.add_argument("--dps", type=int, help="override working decimal precision")
    parser.add_argument("--results", type=Path, default=Path(__file__).with_name("results_gamma.json"))
    parser.add_argument("--figure-dir", type=Path, default=Path(__file__).resolve().parent.parent / "figures")
    parser.add_argument("--no-figure", action="store_true", help="skip only the static figure")
    args = parser.parse_args()
    mp.mp.dps = args.dps or (32 if args.quick else 48)
    if mp.mp.dps < 25:
        parser.error("--dps must be at least 25")
    started = time.perf_counter()
    digits = mp.mp.dps - 3
    nodes = 32 if args.quick else 64
    count = max(40 if args.quick else 75, math.ceil(mp.mp.dps / math.log10(4)) + 2)
    tolerance = mp.mpf(10) ** (-min(mp.mp.dps - 10, 22 if args.quick else 34))
    records = []

    def number(value):
        value = mp.mpc(value)
        if value.imag == 0:
            return mp.nstr(value.real, digits)
        return {"real": mp.nstr(value.real, digits), "imag": mp.nstr(value.imag, digits)}

    def record(name, parameters, lhs, rhs, tol=tolerance):
        error = abs(lhs - rhs)
        scaled = error / max(mp.mpf(1), abs(lhs), abs(rhs))
        row = {
            "name": name,
            "parameters": parameters,
            "left_value": number(lhs),
            "right_value": number(rhs),
            "absolute_error": mp.nstr(error, 10),
            "scaled_error": mp.nstr(scaled, 10),
            "scaled_error_tolerance": mp.nstr(tol, 8),
            "passed": bool(scaled < tol),
        }
        records.append(row)
        print(f"{name}: absolute_error={mp.nstr(error, 6)}, passed={row['passed']}", flush=True)

    kernel_cases = [
        (mp.mpf("0.7"), mp.mpf("0.8"), mp.mpf("0.23")),
        (mp.mpc("0.4", "0.2"), mp.mpc("0.7", "-0.1"), mp.mpf("0.31")),
    ]
    if not args.quick:
        kernel_cases.append((mp.mpf("-1.2"), mp.mpf("0.2"), mp.mpf("0.6")))
    for s, t, a in kernel_cases:
        record(
            "ordinary_shifted_Hurwitz",
            {"s": number(s), "t": number(t), "a": number(a)},
            shifted_hurwitz_integral(s, t, a),
            shifted_hurwitz_formula(s, t, a),
        )

    critical_s = mp.mpc("0.37", "0.2")
    critical_a = mp.mpf("0.5")
    record(
        "critical_hyperplane_half_shift",
        {"s": number(critical_s), "t": number(1 - critical_s), "a": "0.5"},
        shifted_hurwitz_integral(critical_s, 1 - critical_s, critical_a),
        -mp.log(2),
    )

    coefficients = cusp_coefficients(count)
    r_zero = gamma_correlation_zero()
    shifts = [mp.mpf("0.18"), mp.mpf("0.5")]
    if not args.quick:
        shifts = [mp.mpf("0.01"), mp.mpf("0.18"), mp.mpf("0.37"), mp.mpf("0.5")]
    direct_values = {}
    for a in shifts:
        value = gamma_correlation_integral(a)
        direct_values[str(a)] = value
        record(
            "logGamma_cusp_series", {"a": number(a), "series_terms": count},
            value, gamma_correlation_series(a, r_zero, coefficients),
        )
        record(
            "logGamma_Stieltjes_curvature", {"a": number(a), "series_terms": count},
            gamma_curvature_series(a, coefficients),
            mp.pi**2 / 3 - mp.stieltjes(1, a) - mp.stieltjes(1, 1 - a),
        )

    reflected_shifts = [mp.mpf("0.23"), mp.mpf("0.5")]
    if not args.quick:
        reflected_shifts.append(mp.sqrt(2) - 1)
    for a in reflected_shifts:
        record(
            "reflected_logGamma_Hurwitz_jets", {"a": number(a)},
            reflected_gamma_integral(a), reflected_gamma_formula(a),
        )

    a = mp.mpf("0.18")
    z_plus, z_minus = mp.exp(2j * mp.pi * a), mp.exp(-2j * mp.pi * a)
    boundary_average = lambda w: (mp.polylog(w, z_plus) + mp.polylog(w, z_minus)) / 2
    contour = contour_derivatives(boundary_average, 2, 2, nodes=nodes)
    # The central integer-order value has its own stable direct implementation.
    contour[0] = boundary_average(2)
    record(
        "logGamma_polylog_Cauchy_order_derivatives",
        {"a": number(a), "center_order": 2, "radius": "0.125", "nodes": nodes},
        direct_values[str(a)], polylog_gamma_value(a, contour),
    )

    default_derivatives = [boundary_average(2), mp.diff(boundary_average, 2), mp.diff(boundary_average, 2, 2)]
    default_value = polylog_gamma_value(a, default_derivatives)
    diagnostic = {
        "name": "default_mpmath_polylog_order_difference_diagnostic",
        "a": number(a),
        "default_derivative_value": number(default_value),
        "independent_quadrature_value": number(direct_values[str(a)]),
        "absolute_discrepancy": mp.nstr(abs(default_value - direct_values[str(a)]), 12),
        "derivative_one_default": number(default_derivatives[1]),
        "derivative_one_Cauchy": number(contour[1]),
        "derivative_two_default": number(default_derivatives[2]),
        "derivative_two_Cauchy": number(contour[2]),
        "interpretation": (
            "Diagnostic only, excluded from pass/fail. The installed mpmath boundary "
            "polylogarithm series can terminate prematurely near an integer order. "
            "The Cauchy circle avoids the infinitesimal near-integer evaluations. "
            "A future mpmath version may repair this issue."
        ),
    }

    r_min = gamma_correlation_series(mp.mpf("0.5"), r_zero, coefficients)
    curvature_min = gamma_curvature_series(mp.mpf("0.5"), coefficients)
    artifacts = []
    if not args.no_figure:
        artifacts = make_figure(args.figure_dir, r_zero, coefficients, r_min, curvature_min)

    output = {
        "description": "Reproducible ordinary Hurwitz and log-Gamma correlation diagnostics",
        "certification": "High-precision numerical evidence; no interval-certification claim.",
        "parameters": {
            "mode": "quick" if args.quick else "default",
            "working_decimal_digits": mp.mp.dps,
            "reported_significant_digits": digits,
            "cusp_series_terms": count,
            "Cauchy_nodes": nodes,
            "Cauchy_radius": "0.125",
            "randomness": "None: all parameters and sampling grids are fixed.",
            "python_version": platform.python_version(),
            "mpmath_version": mp.__version__,
        },
        "summary": {
            "R_zero": number(r_zero),
            "R_half": number(r_min),
            "R_second_derivative_half": number(curvature_min),
            "leading_R_zero_minus_R_a_coefficient_of_a_log_squared_a": "0.5",
            "minimum_tested_cusp_coefficient_B_m": number(min(coefficients)),
            "number_of_checks": len(records),
            "all_checks_passed": all(row["passed"] for row in records),
        },
        "checks": records,
        "implementation_diagnostic": diagnostic,
        "figure_files": [path.name for path in artifacts],
        "runtime_seconds": round(time.perf_counter() - started, 3),
    }
    args.results.parent.mkdir(parents=True, exist_ok=True)
    args.results.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output["summary"], indent=2), flush=True)
    print(f"Results: {args.results}; runtime: {output['runtime_seconds']} s", flush=True)
    if not output["summary"]["all_checks_passed"]:
        raise SystemExit("A numerical diagnostic exceeded its documented tolerance.")


if __name__ == "__main__":
    main()
