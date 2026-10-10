#!/usr/bin/env python3
"""Reproduce the two-panel Bessel figure from exact polynomial formulas.

Dependencies: matplotlib, numpy, mpmath. No coefficients are fitted.
The numerical plots illustrate the analytic theorems; they are not
proof-bearing zero or sign certificates.
"""

from fractions import Fraction
import csv
from math import factorial
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np


OUTPUT = Path(__file__).resolve().parents[2] / "figures"


def elementary_coefficients(k):
    e = [1]
    for ell in range(1, k + 1):
        e.append(0)
        for j in range(ell, 0, -1):
            e[j] += ell * e[j - 1]
    return e


def profile_coefficients(k):
    # H_{0,k}^0(z) = sum_j e_j(1,...,k) (-z)^j / (k^(2j) j!).
    e = elementary_coefficients(k)
    return [Fraction((-1) ** j * e[j], k ** (2 * j) * factorial(j))
            for j in range(k + 1)]


def first_scaled_zero(k, lam):
    c = profile_coefficients(k)
    cm = [mp.mpf(v.numerator) / v.denominator for v in reversed(c)]
    second = lam - 5 * lam / (3 * k) + lam * (lam + 20) / (9 * k ** 2)
    return mp.findroot(lambda z: mp.polyval(cm, z),
                       (second * mp.mpf("0.99"), second * mp.mpf("1.01")))


def main():
    OUTPUT.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = 90
    navy, teal, rust = "#183B50", "#258F8B", "#B86743"
    plt.rcParams.update({
        "font.family": "STIXGeneral", "font.size": 10,
        "mathtext.fontset": "stix", "axes.labelsize": 10,
        "axes.titlesize": 10.5, "legend.fontsize": 8.7,
        "xtick.labelsize": 8.5, "ytick.labelsize": 8.5,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.edgecolor": "#68747B", "axes.linewidth": 0.65,
        "xtick.color": "#445059", "ytick.color": "#445059",
        "text.color": "#183B50", "axes.labelcolor": "#183B50",
        "pdf.fonttype": 42, "ps.fonttype": 42,
        "savefig.facecolor": "white",
    })
    fig, axes = plt.subplots(1, 2, figsize=(7.3, 3.45),
                             gridspec_kw={"width_ratios": [1.16, 1]})
    fig.subplots_adjust(left=0.09, right=0.985, bottom=0.235,
                        top=0.885, wspace=0.315)

    z = np.linspace(0, 20, 601)
    limit = np.array([float(mp.besselj(0, mp.sqrt(2 * v))) for v in z])
    values = {}
    for k in (10, 30, 100):
        c = np.array([float(v) for v in profile_coefficients(k)])
        values[k] = np.polynomial.polynomial.polyval(z, c)
    ax = axes[0]
    ax.axhline(0, color="#D3DADD", linewidth=0.65, zorder=0)
    ax.plot(z, values[10], color=rust, linewidth=1.45,
            linestyle=(0, (5, 2, 1, 2)), label="$k=10$")
    ax.plot(z, values[30], color=teal, linewidth=1.6,
            linestyle=(0, (5, 2.5)), label="$k=30$")
    ax.plot(z, values[100], color=navy, linewidth=1.5,
            linestyle=(0, (1, 1.9)), label="$k=100$")
    ax.plot(z, limit, color=navy, linewidth=1.7,
            label=r"$J_0(\sqrt{2z})$")
    ax.set(xlim=(0, 20), ylim=(-0.555, 1.06),
           xlabel=r"Scaled parameter $z=k^2\log a$",
           ylabel=r"$\mathcal{H}_{0,k}^{0}(z)$")
    ax.set_title("(a)  Elementary normalized profile", loc="left", pad=10)
    ax.legend(loc="upper right", frameon=False, handlelength=2.7,
              labelspacing=0.35, borderaxespad=0.25)
    ax.set_xticks([0, 5, 10, 15, 20])

    lam = mp.besseljzero(0, 1) ** 2 / 2
    lam_float = float(lam)
    ks = (10, 12, 16, 20, 30, 40, 60, 100, 160, 250)
    roots = [first_scaled_zero(k, lam) for k in ks]
    x = np.linspace(0, 0.102, 401)
    first = lam_float - 5 * lam_float * x / 3
    second = first + lam_float * (lam_float + 20) * x ** 2 / 9
    ax = axes[1]
    ax.axhline(lam_float, color="#9CACB5", linewidth=0.7,
               linestyle=(0, (1, 3)))
    ax.plot(x, first, color=rust, linewidth=1.35,
            linestyle=(0, (5, 2.5)), label="First correction")
    ax.plot(x, second, color=navy, linewidth=1.6,
            label="First + second corrections")
    ax.scatter([1 / k for k in ks], [float(v) for v in roots],
               s=20, linewidths=1.05, facecolor="white", edgecolor=teal,
               zorder=5, label="Elementary zeros")
    ax.text(0.101, lam_float + 0.008, r"$\lambda=j_{0,1}^{2}/2$",
            ha="right", va="bottom", fontsize=8.8, color=navy)
    ax.set(xlim=(-0.001, 0.104), ylim=(2.36, 2.955),
           xlabel=r"$1/k$", ylabel=r"$k^2\log a_{0,1,k}^{0}$")
    ax.set_title("(b)  First scaled zero", loc="left", pad=10)
    ax.set_xticks([0, 0.025, 0.05, 0.075, 0.1])
    ax.set_xticklabels(["0", "0.025", "0.05", "0.075", "0.1"])
    ax.legend(loc="lower left", frameon=False, handlelength=2.25,
              fontsize=8.1, labelspacing=0.35, borderaxespad=0.25)

    fig.text(0.09, 0.092,
             "Exact finite-polynomial formulas evaluated numerically; no coefficients are fitted.",
             fontsize=8.4, color="#4F5D66", va="center")
    fig.text(0.09, 0.046,
             r"The spectral-tail theorem proves uniformity for $0\leq\rho\leq1$; the plots are diagnostics.",
             fontsize=8.4, color="#4F5D66", va="center")
    for extension in ("pdf", "png"):
        fig.savefig(OUTPUT / f"bessel_profile_and_zeros.{extension}", dpi=220,
                    metadata={"Title": "Adjacent-index Bessel profiles and zeros",
                              "Author": "OpenAI-assisted research for ProveIt"})
    plt.close(fig)

    with (Path(__file__).resolve().parents[2] / "data" / "zeros" / "bessel_profile_samples.csv").open("w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["z", "J0_sqrt_2z", "H_k10", "H_k30", "H_k100"])
        for j, point in enumerate(z):
            writer.writerow([point, limit[j], values[10][j], values[30][j], values[100][j]])
    with (Path(__file__).resolve().parents[2] / "data" / "zeros" / "bessel_first_zero_samples.csv").open("w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["k", "one_over_k", "scaled_zero", "first_correction", "second_correction"])
        for k, root in zip(ks, roots):
            first = lam - 5 * lam / (3 * k)
            second = first + lam * (lam + 20) / (9 * k ** 2)
            writer.writerow([k, 1 / k, mp.nstr(root, 45), mp.nstr(first, 45), mp.nstr(second, 45)])
    (OUTPUT / "caption.tex").write_text(
        r"\caption{Bessel scaling at $r=n-k=0$. Left: the exact elementary "
        r"polynomial profiles $\mathcal H_{0,k}^{0}(z)$, evaluated numerically, "
        r"approach $J_0(\sqrt{2z})$. Right: the first elementary scaled zero "
        r"against $1/k$, with the proved first and second corrections "
        r"$\lambda-5\lambda/(3k)$ and "
        r"$\lambda-5\lambda/(3k)+\lambda(\lambda+20)/(9k^2)$, "
        r"where $\lambda=j_{0,1}^2/2$. No coefficients are fitted. "
        r"The spectral-tail theorem, rather than these diagnostic plots, "
        r"establishes uniformity throughout $0\leq\rho\leq1$.}" + "\n")
    print("Created vector PDF, PNG, two CSV data files, and a LaTeX caption.")


if __name__ == "__main__":
    main()
