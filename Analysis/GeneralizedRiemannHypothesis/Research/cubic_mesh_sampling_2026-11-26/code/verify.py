#!/usr/bin/env python3
"""Deterministic supplementary checks for the cubic mesh-energy theorem.

Run from any directory with Python 3 and mpmath, sympy, numpy, matplotlib:
    python code/verify.py

The mathematical proofs are in report.tex. These finite calculations check
formulas, the illustrative construction, and figure data; they are not a
computer proof of the analytic transfer theorem or of RH/GRH.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path

import mpmath as mp
import sympy as sp


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FIGURES = ROOT / "figures"
mp.mp.dps = 100


def dec(value, digits=45):
    """Decimal strings retain precision in JSON and CSV."""
    return mp.nstr(value, digits)


def relative_error(actual, expected):
    return abs(actual - expected) / max(mp.mpf("1e-90"), abs(expected))


def defect(a, b, x):
    """Chord defect of M(x)=x log x; the linear c*x term cancels."""
    a, b, x = map(mp.mpf, (a, b, x))
    t = (x - a) / (b - a)
    return (1 - t) * a * mp.log(a) + t * b * mp.log(b) - x * mp.log(x)


def integrated_half(a, b):
    """Integral defect(x) * x**(-3/2) dx, exactly as a formula."""
    a, b = map(mp.mpf, (a, b))
    sa, sb = mp.sqrt(a), mp.sqrt(b)
    return 4 * (sb - sa) - 4 * sa * sb / (sa + sb) * mp.log(b / a)


def exact_peak(a, b):
    a, b = map(mp.mpf, (a, b))
    slope = (b * mp.log(b) - a * mp.log(a)) / (b - a)
    location = mp.exp(slope - 1)
    return location, defect(a, b, location)


def check_symbolic():
    a, b, x = sp.symbols("A B x", positive=True)
    d = b - a
    g_times_x = b * (x - a) / d * sp.log(b / a) - x * sp.log(x / a)
    second = sp.simplify(sp.diff(g_times_x, x, 2))
    assert second == -1 / x
    parabola_integral = sp.factor(sp.integrate((x - a) * (b - x), (x, a, b)))
    assert sp.simplify(parabola_integral - d**3 / 6) == 0

    t = sp.symbols("t", positive=True)
    formula = 4 * (sp.sqrt(1 + t) - 1) - 4 * sp.sqrt(1 + t) / (
        1 + sp.sqrt(1 + t)
    ) * sp.log(1 + t)
    expansion = sp.series(formula, t, 0, 7)
    assert sp.expand(expansion.removeO()).coeff(t, 3) == sp.Rational(1, 12)
    assert sp.expand(expansion.removeO()).coeff(t, 4) == -sp.Rational(5, 48)

    n, m = sp.symbols("N M", positive=True, integer=True)
    gap = sp.expand((n + m) ** 4 - n**4)
    assert gap == 4 * n**3 * m + 6 * n**2 * m**2 + 4 * n * m**3 + m**4
    return {
        "second_derivative_identity": str(second),
        "parabola_integral": str(parabola_integral),
        "small_relative_gap_series": str(expansion),
        "fourth_power_gap_identity": str(gap),
        "status": "passed exact symbolic checks",
    }


def check_quadrature():
    cases = [(1, 2), (100, 101), (16777216, 21381376), (10**12, 10**12 + 10**6)]
    rows = []
    for aa, bb in cases:
        a, b = mp.mpf(aa), mp.mpf(bb)
        exact = integrated_half(a, b)
        # Integrate in the relative interval coordinate to avoid scale issues.
        integral = mp.quad(
            lambda t: defect(a, b, a + t * (b - a))
            * (a + t * (b - a)) ** (-mp.mpf(3) / 2)
            * (b - a),
            [0, mp.mpf("0.5"), 1],
        )
        error = relative_error(exact, integral)
        lower = (b - a) ** 3 / (12 * b ** mp.mpf("2.5"))
        upper = (b - a) ** 3 / (12 * a ** mp.mpf("2.5"))
        assert error < mp.mpf("1e-70")
        assert lower < exact < upper
        rows.append({
            "A": aa, "B": bb,
            "closed_form": dec(exact),
            "numerical_integral": dec(integral),
            "relative_difference": dec(error),
            "lower_bound": dec(lower),
            "upper_bound": dec(upper),
        })
    return rows


def check_asymptotic():
    rows = []
    for power in (1, 2, 3, 4, 6, 8):
        gap = mp.mpf(10) ** (-power)
        ratio = integrated_half(1, 1 + gap) / (gap**3 / 12)
        assert 0 < ratio < 1
        rows.append({"relative_gap": dec(gap), "ratio_to_cubic_leading_term": dec(ratio)})
    assert abs(mp.mpf(rows[-1]["ratio_to_cubic_leading_term"]) - 1) < mp.mpf("2e-8")
    return rows


def check_global_extremizer():
    nodes = [2, 5, 9, 16, 27, 49]
    a = mp.mpf(1) / 3
    c = -a * mp.log(nodes[0])
    centers = [
        mp.mpf(left) * right * mp.log(mp.mpf(right) / left) / (right - left)
        for left, right in zip(nodes, nodes[1:])
    ]
    weights = [a * centers[0]] + [
        a * (current - previous) for previous, current in zip(centers, centers[1:])
    ]
    assert all(w > 0 for w in weights)
    assert all(left < center < right for left, center, right in zip(nodes, centers, nodes[1:]))

    def e(x):
        x = mp.mpf(x)
        convex = sum(w * max(x / n - 1, 0) for n, w in zip(nodes, weights))
        return convex - a * x * mp.log(x) - c * x

    sample_residual = max(abs(e(n)) for n in nodes)
    interior_residual = mp.mpf(0)
    for left, right in zip(nodes, nodes[1:]):
        for t in (mp.mpf(1) / 7, mp.mpf(1) / 2, mp.mpf(6) / 7):
            x = left + t * (right - left)
            interior_residual = max(interior_residual, abs(e(x) - a * defect(left, right, x)))
    assert sample_residual < mp.mpf("1e-90")
    assert interior_residual < mp.mpf("1e-90")
    return {
        "integer_nodes": nodes,
        "a": "1/3", "c": dec(c),
        "positive_weights_at_all_but_last_node": [dec(w) for w in weights],
        "max_sample_residual": dec(sample_residual),
        "max_interior_defect_residual": dec(interior_residual),
        "scope": "arbitrary nonnegative arithmetic weights, not von Mangoldt weights",
    }


def deleted_gap_rows():
    rows = []
    for k in range(2, 11):
        n, m = 2 ** (3 * k), 2**k
        a, b = n**4, (n + m) ** 4
        gap = b - a
        expanded = 4 * 2 ** (10 * k) + 6 * 2 ** (8 * k) + 4 * 2 ** (6 * k) + 2 ** (4 * k)
        assert gap == expanded
        assert m**3 == n
        assert gap <= 15 * n**3 * m
        assert gap**3 <= 3375 * n**10  # critical energy <= 3375, exactly in integers
        location, peak = exact_peak(a, b)
        integral = integrated_half(a, b)
        rows.append({
            "k": k, "N": n, "M": m, "A": a, "B": b,
            "gap": gap, "deleted_sample_nodes": m - 1,
            "gap_over_A_to_5_over_6": dec(mp.mpf(gap) / mp.mpf(a) ** (mp.mpf(5) / 6)),
            "critical_cubic_energy": dec(mp.mpf(gap**3) / n**10),
            "exact_weighted_defect": dec(integral),
            "defect_over_16_over_3": dec(integral / (mp.mpf(16) / 3)),
            "peak_location": dec(location), "peak_E": dec(peak),
            "peak_E_over_A_to_2_over_3": dec(peak / mp.mpf(a) ** (mp.mpf(2) / 3)),
            "peak_E_over_sqrt_A": dec(peak / mp.sqrt(a)),
        })
    return rows


def check_finite_mesh_energy():
    rows = []
    for largest_index in (64, 512, 4096, 32768):
        jumps = {2 ** (3 * k): 2**k for k in range(2, 12) if 2 ** (3 * k) <= largest_index}
        n = 1
        terms = []
        exceptional_count = 0
        while n <= largest_index:
            m = jumps.get(n, 1)
            gap = (n + m) ** 4 - n**4
            assert m <= n
            assert gap <= 15 * n**3 * m
            # Every bound in the last line is checked by exact integer algebra.
            terms.append(gap**3 / n**10)
            exceptional_count += int(m > 1)
            n += m
        x = largest_index**4
        energy = math.fsum(terms)
        bound = 3375 * (1 + (1 / 4 + 1 / (12 * math.log(2))) * math.log(x))
        assert energy <= bound
        rows.append({
            "largest_underlying_quartic_index": largest_index,
            "X": x,
            "retained_gap_count_with_left_endpoint_at_most_X": len(terms),
            "exceptional_gap_count": exceptional_count,
            "critical_energy_approximation": energy,
            "proved_general_upper_bound_at_X": bound,
        })
    return rows


def make_figures(rows):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np

    FIGURES.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 9,
        "axes.titlesize": 11,
        "axes.labelsize": 9,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "figure.facecolor": "white",
        "axes.facecolor": "white",
        "savefig.facecolor": "white",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })
    blue, teal, gold, gray = "#173F5F", "#177E89", "#B8791B", "#66717E"

    fig, ax = plt.subplots(figsize=(7.0, 4.3), constrained_layout=True)
    alpha = np.linspace(0.50, 1.0, 501)
    dense = 1 - alpha
    budget = 2.5 - 3 * alpha
    feasible = np.maximum(0, np.minimum(dense, budget))
    ax.fill_between(alpha, 0, feasible, color=teal, alpha=0.16, linewidth=0)
    ax.plot(alpha, budget, color=blue, linewidth=2.2,
            label=r"Cubic energy boundary: $\kappa+3\alpha=5/2$")
    ax.plot(alpha, dense, color=gray, linewidth=1.6, linestyle=(0, (4, 3)),
            label=r"Maximum disjoint-gap count: $\kappa+\alpha=1$")
    ax.scatter([0.75, 5 / 6], [0.25, 0], color=[blue, gold], s=45, zorder=4, clip_on=False)
    ax.annotate("Ordinary fourth-power mesh\n" + r"$(\alpha,\kappa)=(3/4,1/4)$",
                xy=(0.75, 0.25), xytext=(0.56, 0.34), fontsize=9,
                bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.92, "pad": 2.5},
                arrowprops={"arrowstyle": "-", "color": blue, "lw": 1.0})
    ax.annotate("Rare deleted blocks\n" + r"$(\alpha,\kappa)=(5/6,0)$",
                xy=(5 / 6, 0), xytext=(0.83, 0.14), fontsize=9,
                bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.92, "pad": 2.5},
                arrowprops={"arrowstyle": "-", "color": gold, "lw": 1.0})
    ax.text(0.56, 0.08, "Subpower total cost", color=teal, fontsize=10)
    ax.set(xlim=(0.50, 1.0), ylim=(0, 0.55),
           xlabel=r"Gap length exponent $\alpha$: gap $\Delta\asymp X^\alpha$",
           ylabel=r"Gap count exponent $\kappa$: $X^\kappa$ gaps per dyadic interval")
    ax.set_title("Frequency and size share one cubic energy budget", loc="left", pad=13)
    ax.grid(color="#E7EAEE", linewidth=0.65)
    ax.set_axisbelow(True)
    ax.legend(loc="upper right", fontsize=8, frameon=True, facecolor="white", edgecolor="#DADFE5")
    for extension in ("pdf", "png"):
        fig.savefig(FIGURES / f"gap_frequency_budget.{extension}", dpi=220)
    plt.close(fig)

    fig, axes = plt.subplots(1, 2, figsize=(7.2, 3.5), constrained_layout=True,
                             gridspec_kw={"width_ratios": [1.2, 1]})
    ax, right = axes
    u_values = np.linspace(0, 1, 161)
    for k, color in [(2, gold), (3, teal), (6, blue)]:
        n, m = 2 ** (3 * k), 2**k
        a, b = n**4, (n + m) ** 4
        scale = mp.mpf(a) ** (mp.mpf(2) / 3)
        profile = [float(defect(a, b, mp.mpf(a) + mp.mpf(str(u)) * (b - a)) / scale)
                   for u in u_values]
        ax.plot(u_values, profile, color=color, linewidth=1.8, label=f"Deleted block $k={k}$")
    ax.plot(u_values, 8 * u_values * (1 - u_values), color="#333333", linewidth=1.2,
            linestyle=(0, (3, 3)), label=r"Limit $8u(1-u)$")
    ax.scatter([0, 1], [0, 0], color=blue, s=25, clip_on=False, zorder=5)
    ax.set(xlim=(0, 1), ylim=(0, 2.35), xlabel=r"Relative position $u=(x-A)/(B-A)$",
           ylabel=r"Excursion $E(x)/A^{2/3}$")
    ax.set_title("Sample endpoints are zero", loc="left")
    ax.legend(loc="upper center", bbox_to_anchor=(0.5, -0.23), ncol=2,
              fontsize=7.5, frameon=False, columnspacing=0.8)

    ks = [row["k"] for row in rows]
    costs = [float(row["exact_weighted_defect"]) for row in rows]
    right.plot(ks, costs, color=teal, marker="o", markersize=3.5, linewidth=1.8)
    right.axhline(16 / 3, color=gray, linewidth=1.2, linestyle=(0, (3, 3)))
    right.text(9.8, 16 / 3 - 0.05, r"Limit $16/3$", ha="right", va="top", color=gray, fontsize=8)
    right.set(xlim=(1.7, 10.3), ylim=(min(costs) * 0.96, 5.65), xticks=[2, 4, 6, 8, 10],
              xlabel="Deleted block index $k$",
              ylabel=r"Cost $\int_A^B E(x)x^{-3/2}\,dx$")
    right.set_title("Each long gap has bounded cost", loc="left")
    for axis in axes:
        axis.grid(color="#E7EAEE", linewidth=0.65)
        axis.set_axisbelow(True)
    for extension in ("pdf", "png"):
        fig.savefig(FIGURES / f"deleted_block_defect.{extension}", dpi=220)
    plt.close(fig)
    return ["gap_frequency_budget.pdf", "gap_frequency_budget.png",
            "deleted_block_defect.pdf", "deleted_block_defect.png"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-figures", action="store_true", help="Run checks and tables only.")
    args = parser.parse_args()
    rows = deleted_gap_rows()
    result = {
        "status": "all specified finite supplementary checks passed",
        "scope": "formula checks and illustration only; no numerical proof of RH, GRH, or the transfer theorem",
        "precision_decimal_digits": mp.mp.dps,
        "versions": {"mpmath": mp.__version__, "sympy": sp.__version__},
        "symbolic": check_symbolic(),
        "quadrature_checks": check_quadrature(),
        "asymptotic_constant_checks": check_asymptotic(),
        "global_integer_supported_extremizer": check_global_extremizer(),
        "finite_deleted_mesh_energy": check_finite_mesh_energy(),
        "deleted_gap_table_row_count": len(rows),
    }
    with (HERE / "gap_table.csv").open("w", newline="", encoding="utf-8") as output:
        writer = csv.DictWriter(output, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    if not args.no_figures:
        result["figure_files"] = make_figures(rows)
    (HERE / "verification_results.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(json.dumps({
        "status": result["status"],
        "results": str(HERE / "verification_results.json"),
        "table": str(HERE / "gap_table.csv"),
        "figures": result.get("figure_files", []),
    }, indent=2))


if __name__ == "__main__":
    main()
