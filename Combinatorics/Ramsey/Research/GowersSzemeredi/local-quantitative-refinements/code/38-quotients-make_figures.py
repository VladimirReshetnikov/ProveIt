#!/usr/bin/env python3
"""Reproduce the two asymptotic-coefficient plots and their numerical data.

Dependencies: mpmath and matplotlib.  All mathematical evaluations use
120 decimal digits; conversion to binary floats occurs only at plotting.
Both curves are explicit families, not claims of exact global optimality
at the plotted positive parameters.  The manuscript proves their limiting
coefficients and gives the corresponding universal asymptotic theorems.

Run from any working directory:
    python3 code/make_figures.py
"""
from pathlib import Path
import csv
import json

import mpmath as mp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter, LogLocator


ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "figures"
DATA = ROOT / "data"
mp.mp.dps = 120


def decimal(x):
    return mp.nstr(x, 75)


def logspace(start, end, count=121):
    a, b = mp.log10(mp.mpf(start)), mp.log10(mp.mpf(end))
    return [mp.power(10, a + (b - a) * j / (count - 1))
            for j in range(count)]


def five_point(t):
    q0 = mp.power(2, -mp.mpf(3) / 4)
    k = q0 / 3 + mp.mpf(31) * q0 ** 2 * t ** 2 / 27
    b = k * t ** 2
    # Solve for R=rho^2/t^2.  This equation is strictly increasing on
    # positive R, has value <1 at R=0 in the plotted range, and tends
    # to infinity.  Newton's iteration from q0 converges to its unique
    # positive root; the residual and positivity are checked below.
    def norm_equation(R):
        return (8 * R ** 4 + 16 * R ** 3 * k ** 2 * t ** 2 +
                48 * R ** 2 * k ** 4 * t ** 4 +
                16 * R * k ** 6 * t ** 6 + 8 * k ** 8 * t ** 8 - 1)

    R = mp.findroot(norm_equation, q0, tol=mp.mpf("1e-112"))
    if R <= 0 or abs(norm_equation(R)) > mp.mpf("1e-108"):
        raise ArithmeticError("The scaled five-point norm equation failed")
    rho2 = t ** 2 * R
    rho4 = rho2 ** 2
    Q = (1 + 24 * (rho4 + b ** 4) + 16 * rho4 * b +
         96 * rho4 * b ** 2 + 48 * rho2 * b ** 4 +
         32 * rho4 * b ** 3 + t ** 8)
    fourth = 6 * mp.sqrt(2)
    sixth = mp.power(2, mp.mpf(3) / 4) / 3
    eighth = mp.mpf(20) / 9
    residual = (Q - 1 - fourth * t ** 4 - sixth * t ** 6 -
                eighth * t ** 8) / t ** 10
    limit = mp.mpf(869) * q0 / 216
    return dict(t=t, rho=mp.sqrt(rho2), b=b, cube_count=Q,
                normalized_tenth_order_residual=residual,
                limit=limit, residual_minus_limit=residual - limit,
                scaled_norm_equation_residual=norm_equation(R))


def qutrit(t):
    F = 1 - t
    kappa = (F ** 4 + 6 * F ** 2 * t ** 2 +
             2 * mp.sqrt(2) * F ** (mp.mpf(3) / 2) *
             t ** (mp.mpf(5) / 2) + 4 * F * t ** 3 + t ** 4 / 2)
    epsilon = 1 - kappa
    if not 0 < epsilon < 1 or not t < mp.mpf(1) / 6:
        raise ArithmeticError("The qutrit parameter left its proved range")
    residual = ((t - epsilon / 4 - 3 * epsilon ** 2 / 16) /
                epsilon ** (mp.mpf(5) / 2))
    limit = mp.sqrt(2) / 64
    return dict(t=t, best_fidelity=F, kappa=kappa, epsilon=epsilon,
                normalized_fractional_residual=residual,
                limit=limit, residual_minus_limit=residual - limit)


def save_csv(filename, rows):
    with (DATA / filename).open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows({key: decimal(value) for key, value in row.items()}
                        for row in rows)


def make_plot(five, three):
    plt.rcParams.update({
        "font.family": "DejaVu Serif",
        "font.size": 8.5,
        "mathtext.fontset": "dejavuserif",
        "axes.titlesize": 9.5,
        "axes.labelsize": 9,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "legend.fontsize": 8,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.edgecolor": "#8A929B",
        "axes.linewidth": 0.65,
        "savefig.facecolor": "white",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })
    navy, teal, copper = "#174F75", "#117A72", "#B36635"
    # Size the figure at its actual printed width.  Residual definitions
    # are typeset in the article, so no small formula text is scaled down.
    fig, axes = plt.subplots(1, 2, figsize=(6.5, 3.05))
    fig.subplots_adjust(left=0.122, right=0.985, bottom=0.19,
                        top=0.87, wspace=0.42)

    ax = axes[0]
    x = [float(r["t"]) for r in five]
    y = [float(r["normalized_tenth_order_residual"]) for r in five]
    limit = float(five[0]["limit"])
    ax.semilogx(x, y, color=navy, lw=1.6, label="Explicit five-point family")
    ax.axhline(limit, color=copper, lw=1.15, ls=(0, (4, 3)),
               label=r"Limit $869/(216\,2^{3/4})$")
    ax.set_title("A. Five-point cube profile", loc="left", pad=10,
                 fontweight="semibold")
    ax.set_xlabel(r"$t=u/\delta$", labelpad=6)
    ax.set_ylabel(r"$\mathcal{C}_{10}(t)$", labelpad=6)
    ax.set_xlim(x[0], x[-1])
    ax.set_ylim(limit - 0.003, max(y) + 0.004)
    ax.yaxis.set_major_formatter(FormatStrFormatter("%.3f"))
    ax.xaxis.set_major_locator(LogLocator(base=10, numticks=6))
    ax.legend(loc="upper left", frameon=False, handlelength=2.0,
              borderaxespad=0.3)
    ax.grid(axis="y", color="#D8DDE2", alpha=0.8, linewidth=0.6)

    ax = axes[1]
    x = [float(r["epsilon"]) for r in three]
    y = [float(r["normalized_fractional_residual"]) for r in three]
    limit = float(three[0]["limit"])
    ax.semilogx(x, y, color=teal, lw=1.6, label="Explicit three-point family")
    ax.axhline(limit, color=copper, lw=1.15, ls=(0, (4, 3)),
               label=r"Limit $\sqrt{2}/64$")
    ax.set_title("B. Odd-order stability", loc="left", pad=10,
                 fontweight="semibold")
    ax.set_xlabel(r"$\varepsilon=1-\kappa(v_t)$", labelpad=6)
    ax.set_ylabel(r"$\mathcal{R}_{\rm odd}(\varepsilon)$", labelpad=6)
    ax.set_xlim(x[0], x[-1])
    ax.set_ylim(limit - 0.004, max(y) + 0.006)
    ax.yaxis.set_major_formatter(FormatStrFormatter("%.3f"))
    ax.xaxis.set_major_locator(LogLocator(base=10, numticks=6))
    ax.legend(loc="upper left", frameon=False, handlelength=2.0,
              borderaxespad=0.3)
    ax.grid(axis="y", color="#D8DDE2", alpha=0.8, linewidth=0.6)
    fig.savefig(FIGURES / "asymptotic_coefficients.pdf")
    fig.savefig(FIGURES / "asymptotic_coefficients.png", dpi=220)
    plt.close(fig)


def main():
    FIGURES.mkdir(parents=True, exist_ok=True)
    DATA.mkdir(parents=True, exist_ok=True)
    five = [five_point(t) for t in logspace("1e-6", "0.1")]
    three = [qutrit(t) for t in logspace("1e-8", "0.01")]
    # These only check numerical convergence for the explicit families;
    # the exact coefficient proofs are in the article.
    if abs(five[0]["residual_minus_limit"]) > mp.mpf("1e-10"):
        raise ArithmeticError("Five-point residual has not converged")
    if abs(three[0]["residual_minus_limit"]) > mp.mpf("1e-4"):
        raise ArithmeticError("Three-point residual has not converged")
    save_csv("five_point_coefficient_convergence.csv", five)
    save_csv("qutrit_coefficient_convergence.csv", three)
    summary = {
        "arithmetic_decimal_digits": mp.mp.dps,
        "data_decimal_digits": 75,
        "points_per_panel": len(five),
        "curve_status": "Explicit families; not exact finite-parameter global maxima",
        "five_point_family": {
            "parameters": "q0=2^(-3/4), b=(q0/3)t^2+(31q0^2/27)t^4, theta=0, phi=pi/2",
            "norm": "rho is the unique positive solution of N(rho,b,0,pi/2)=t^8",
            "limit": decimal(five[0]["limit"]),
            "first_point": {k: decimal(v) for k, v in five[0].items()},
            "last_point": {k: decimal(v) for k, v in five[-1].items()},
            "max_scaled_norm_equation_residual": decimal(max(
                abs(row["scaled_norm_equation_residual"]) for row in five)),
        },
        "three_point_family": {
            "parameters": "v_t=sqrt(1-t)e0+sqrt(t/2)(e1+e2), epsilon=1-kappa(v_t)",
            "limit": decimal(three[0]["limit"]),
            "first_point": {k: decimal(v) for k, v in three[0].items()},
            "last_point": {k: decimal(v) for k, v in three[-1].items()},
        },
        "plotted_data": ["five_point_coefficient_convergence.csv",
                         "qutrit_coefficient_convergence.csv"],
    }
    (DATA / "figure_numerics.json").write_text(json.dumps(summary, indent=2) + "\n")
    make_plot(five, three)
    print(json.dumps({"status": "figures and numerical data written",
                      "figure": str(FIGURES / "asymptotic_coefficients.pdf"),
                      "five_point_limit": summary["five_point_family"]["limit"],
                      "three_point_limit": summary["three_point_family"]["limit"]},
                     indent=2))


if __name__ == "__main__":
    main()
