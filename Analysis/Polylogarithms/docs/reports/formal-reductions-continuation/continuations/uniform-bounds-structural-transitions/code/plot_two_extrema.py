#!/usr/bin/env python3
"""Numerical scientific figure of the actual implicit radial derivative.

Requires mpmath and matplotlib. Every function evaluation solves E(t,v)=0
using the convergent B_j series at 85 decimal digits, then uses -E_t/E_v.
The plotted curve is numerical. The separate exact rational certificate
certify_two_extrema.py proves the root trapping, displayed sign intervals,
and existence/uniqueness of both extrema.

Outputs beside this script: PDF, PNG, a CSV table, diagnostic JSON, and a
plain-text caption. No network or external data are used.
"""

from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import csv
import json

import mpmath as mp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

mp.mp.dps = 85
TERMS = 24
CHECK_TERMS = 28
A = mp.mpf("1.0014289951689850677")
B = mp.mpf("0.9974958668828783544")
TMAX = F(7, 4000)
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/"figures"
DATA = ROOT/"data"


def mp_fraction(x):
    return mp.mpf(x.numerator)/x.denominator


def exact_tail_bound(tmax, dt=0, dv=0, terms=TERMS):
    # The written certificate proves this expression for |v|<=1.
    d = dt+dv+1
    q = 3*tmax
    return (15*F(4, 3)**dv*tmax**(-dt)*q**terms
            *terms**d*factorial(d)/(1-q)**(d+1))


def build_coefficients(terms):
    p = {}
    h = mp.mpf(0)
    for n in range(1, 2*terms+2):
        if n >= 2:
            p[n] = h/mp.power(n, A)
        h += mp.power(n, -B)
    polynomials = []
    for j in range(terms):
        coefficients = [(-1)**(j+1-k)*comb(j+1, k)*mp.power(2, k)
                        *p[2*j+3-k] for k in range(j+2)]
        derivatives = [k*coefficients[k] for k in range(1, j+2)]
        polynomials.append((coefficients, derivatives))
    return p[3]/(2*p[2]), polynomials


def horner(coefficients, x):
    total = mp.mpf(0)
    for c in reversed(coefficients):
        total = total*x+c
    return total


def equation(t, v, polynomials):
    values = [horner(c, v) for c, _ in polynomials]
    derivatives = [horner(dc, v) for _, dc in polynomials]
    E = horner(values, t)
    Ev = horner(derivatives, t)
    Et = horner([j*values[j] for j in range(1, len(values))], t)
    return E, Ev, Et


def implicit(t, mu, polynomials, initial=None):
    v = mu if initial is None else initial
    for _ in range(12):
        E, Ev, _ = equation(t, v, polynomials)
        change = E/Ev
        v -= change
        if abs(change) < mp.mpf("1e-72"):
            break
    E, Ev, Et = equation(t, v, polynomials)
    assert abs(E) < mp.mpf("1e-70") and Ev > mp.mpf("0.99")
    return v, -Et/Ev, abs(E)


def fmt(x, digits=60):
    return mp.nstr(x, digits)


def main():
    mu, polynomials = build_coefficients(TERMS)
    mu_check, polynomials_check = build_coefficients(CHECK_TERMS)
    t_signs = [F(1, 4000), F(1, 1000), F(7, 4000)]
    mesh = sorted(set([TMAX*F(j, 280) for j in range(281)]+t_signs))
    rows = []
    previous = mu
    max_residual = mp.mpf(0)
    for rational_t in mesh:
        t = mp_fraction(rational_t)
        v, U, residual = implicit(t, mu, polynomials, previous)
        previous = v
        max_residual = max(max_residual, residual)
        rows.append((t, mp.sqrt(t), 1000*t, v, v-mu, U, mp.mpf("1e17")*U))

    def U_of_t(t, use_check=False):
        data = (mu_check, polynomials_check) if use_check else (mu, polynomials)
        return implicit(t, *data)[1]

    t_min = mp.findroot(U_of_t, (mp.mpf("0.0004"), mp.mpf("0.0006")),
                        tol=mp.mpf("1e-65"))
    t_max = mp.findroot(U_of_t, (mp.mpf("0.0013"), mp.mpf("0.0017")),
                        tol=mp.mpf("1e-65"))
    t_min_check = mp.findroot(lambda t: U_of_t(t, True), (t_min*mp.mpf(".99"), t_min*mp.mpf("1.01")),
                              tol=mp.mpf("1e-65"))
    t_max_check = mp.findroot(lambda t: U_of_t(t, True), (t_max*mp.mpf(".99"), t_max*mp.mpf("1.01")),
                              tol=mp.mpf("1e-65"))
    checks = [mp_fraction(TMAX)*j/12 for j in range(13)]+[t_min, t_max]
    max_derivative_difference = max(abs(U_of_t(t)-U_of_t(t, True)) for t in checks)
    assert max_derivative_difference < mp.mpf("1e-45")
    assert abs(t_min-t_min_check) < mp.mpf("1e-30")
    assert abs(t_max-t_max_check) < mp.mpf("1e-30")

    csv_path = DATA/"radial_two_extrema_samples.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["t", "rho", "1000_t", "eta", "eta_minus_eta0", "Phi_prime", "1e17_Phi_prime"])
        for row in rows:
            writer.writerow([fmt(x) for x in row])

    data = {
        "status": "High-precision numerical diagnostics for a scientific figure; rigorous proof is in two_extrema_certificate.json.",
        "a_exact_decimal": str(A), "b_exact_decimal": str(B),
        "decimal_precision": mp.mp.dps, "terms": TERMS, "check_terms": CHECK_TERMS,
        "eta_at_zero": fmt(mu),
        "critical_points": {
            "minimum": {"t": fmt(t_min), "rho": fmt(mp.sqrt(t_min)), "1000_t": fmt(1000*t_min)},
            "maximum": {"t": fmt(t_max), "rho": fmt(mp.sqrt(t_max)), "1000_t": fmt(1000*t_max)}
        },
        "uniform_analytic_tail_bounds": {
            "E": {"exact_fraction": str(exact_tail_bound(TMAX)), "decimal": fmt(mp_fraction(exact_tail_bound(TMAX)), 15)},
            "E_t": {"exact_fraction": str(exact_tail_bound(TMAX, dt=1)), "decimal": fmt(mp_fraction(exact_tail_bound(TMAX, dt=1)), 15)},
            "E_v": {"exact_fraction": str(exact_tail_bound(TMAX, dv=1)), "decimal": fmt(mp_fraction(exact_tail_bound(TMAX, dv=1)), 15)}
        },
        "numerical_checks": {
            "maximum_truncated_equation_residual": fmt(max_residual, 15),
            "maximum_Phi_prime_difference_24_vs_28_terms": fmt(max_derivative_difference, 15),
            "minimum_t_difference_24_vs_28_terms": fmt(abs(t_min-t_min_check), 15),
            "maximum_t_difference_24_vs_28_terms": fmt(abs(t_max-t_max_check), 15)
        },
        "plot_axes": {"horizontal": "1000 t", "vertical": "10^17 Phi'(t)"},
        "csv_rows": len(rows)
    }
    (DATA/"radial_two_extrema_diagnostics.json").write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")

    matplotlib.rcParams.update({
        "font.family": "DejaVu Serif",
        "mathtext.fontset": "stix",
        "font.size": 10.5,
        "axes.titlesize": 14,
        "axes.labelsize": 13,
        "axes.edgecolor": "#56616a",
        "axes.linewidth": 0.8,
        "xtick.color": "#35414b",
        "ytick.color": "#35414b",
        "text.color": "#20303d",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })
    fig, ax = plt.subplots(figsize=(8.4, 5.3))
    fig.subplots_adjust(left=.11, right=.975, bottom=.15, top=.82)
    fig.suptitle("Two turning points of the normalized angular zero", fontsize=14.5, x=.515, y=.975)
    fig.text(.515, .918,
             r"$a=1.0014289951689850677,\quad b=0.9974958668828783544,\quad t=\rho^2$",
             ha="center", fontsize=10.5)

    x = [float(row[2]) for row in rows]
    y = [float(row[6]) for row in rows]
    line_color = "#193e59"
    cert_color = "#b96321"
    root_color = "#247d78"
    ax.axhline(0, color="#7e8a92", linewidth=1.0, zorder=1)
    ax.plot(x, y, color=line_color, linewidth=2.3, zorder=3)
    ax.fill_between(x, y, 0, where=[value >= 0 for value in y],
                    color="#dceee9", alpha=.85, interpolate=True, zorder=0)

    cert_bounds = [(-3.158, -3.156), (2.537, 2.538), (-3.136, -3.135)]
    for t, (low, high) in zip(t_signs, cert_bounds):
        py = float(mp.mpf("1e17")*U_of_t(mp_fraction(t)))
        ax.errorbar(float(1000*t), py, yerr=[[py-low], [high-py]],
                    fmt="o", markersize=5.5, color=cert_color, markeredgecolor="white",
                    markeredgewidth=.7, ecolor=cert_color, capsize=4,
                    elinewidth=1.25, zorder=5)

    roots_x = [float(1000*t_min), float(1000*t_max)]
    ax.plot(roots_x, [0, 0], "o", markerfacecolor="white", markeredgecolor=root_color,
            markeredgewidth=1.8, markersize=6.5, zorder=6)
    for root_x in roots_x:
        ax.vlines(root_x, -8.2, 0, color=root_color, linewidth=.85,
                  linestyle=(0, (3, 3)), alpha=.55, zorder=1)
    ax.annotate("Minimum of $\\eta$\n$\\rho \\approx %.6f$" % float(mp.sqrt(t_min)),
                xy=(roots_x[0], 0), xytext=(.08, 1.35), textcoords="data",
                fontsize=10.4, color=root_color,
                arrowprops={"arrowstyle": "-", "color": root_color, "linewidth": .9},
                bbox={"boxstyle": "round,pad=.24", "facecolor": "white", "edgecolor": "none", "alpha": .94})
    ax.annotate("Maximum of $\\eta$\n$\\rho \\approx %.6f$" % float(mp.sqrt(t_max)),
                xy=(roots_x[1], 0), xytext=(1.28, 2.62), textcoords="data",
                fontsize=10.4, color=root_color,
                arrowprops={"arrowstyle": "-", "color": root_color, "linewidth": .9},
                bbox={"boxstyle": "round,pad=.24", "facecolor": "white", "edgecolor": "none", "alpha": .94})

    ax.set_xlim(-.025, 1.81)
    ax.set_ylim(-8.2, 4.15)
    ax.set_xticks([j/4 for j in range(8)])
    ax.set_xticklabels(["0", "0.25", "0.50", "0.75", "1.00", "1.25", "1.50", "1.75"])
    ax.set_yticks([-8, -6, -4, -2, 0, 2, 4])
    ax.set_xlabel(r"$1000\,t$", labelpad=9)
    ax.set_ylabel(r"$10^{17}\,\Phi'(t)$", labelpad=10)
    ax.grid(axis="y", color="#e5e9ed", linewidth=.6, zorder=0)
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    legend_handles = [Line2D([0], [0], color=line_color, linewidth=2.3,
                             label="Numerical implicit derivative"),
                      Line2D([0], [0], marker="o", color=cert_color, linestyle="None",
                             markersize=5.5, label="Certified sign intervals")]
    ax.legend(handles=legend_handles, loc="lower center", bbox_to_anchor=(.54, .05),
              frameon=True, facecolor="white", edgecolor="#d9e0e5", framealpha=.98,
              fontsize=9.4, handlelength=2.4)
    fig.text(.515, .03,
             "Curve and crossing locations are numerical; the exact rational certificate proves both extrema.",
             ha="center", fontsize=9.0, color="#5a6771")
    fig.savefig(OUT/"radial_two_extrema.pdf", bbox_inches="tight", metadata={
        "Title": "Two turning points of the normalized angular zero",
        "Subject": "High-precision derivative of the actual implicit radial zero, with certified sign enclosures",
        "Creator": "plot_two_extrema.py; mpmath and Matplotlib"})
    fig.savefig(OUT/"radial_two_extrema.png", dpi=220, bbox_inches="tight")
    plt.close(fig)

    caption = (
        "The actual derivative Phi'(t), where Phi(t)=eta_{a,b}(sqrt(t)), for the exact rational orders "
        "a=1.0014289951689850677 and b=0.9974958668828783544. The horizontal axis is 1000t and the "
        "vertical axis is 10^17 Phi'(t). The blue curve and marked zero-crossing locations are numerical: "
        "each value solves the convergent implicit B_j equation at 85 decimal digits using 24 terms, "
        "with a 28-term check and explicit analytic tail bounds. Orange markers and their narrow "
        "vertical error bars show the three exact rational sign enclosures. The separate exact "
        "certificate proves Phi'''<0 on the whole displayed t interval and the signs -,+,-, "
        "establishing exactly one strict minimum and one strict maximum of eta there. "
        "The certificate, not the plotted curve, is the proof."
    )
    (OUT/"radial_two_extrema_caption.txt").write_text(caption+"\n", encoding="utf-8")
    print(json.dumps({"outputs": [str((DATA if name.endswith((".csv", ".json")) else OUT)/name) for name in [
        "radial_two_extrema.pdf", "radial_two_extrema.png", "radial_two_extrema_samples.csv",
        "radial_two_extrema_diagnostics.json", "radial_two_extrema_caption.txt"]],
        "critical_points": data["critical_points"], "checks": data["numerical_checks"],
        "tail_E_t": data["uniform_analytic_tail_bounds"]["E_t"]["decimal"]}, indent=2))


if __name__ == "__main__":
    main()
