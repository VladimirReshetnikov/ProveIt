#!/usr/bin/env python3
"""Illustrate odd dyadic filters using mpmath and Matplotlib.

Run with python3 code/illustrate.py. Outputs are relative to this file.
The CSV uses the upper conjugate minimizer and exponents indexed from one.
beta_last_rad = |Arg(-z^L)|.  The density coefficient multiplies a gain
tolerance, not a tolerance in the squared gain. Decimals are illustrative.
"""

import csv
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np


ROOT = Path(__file__).resolve().parent.parent


def bisect_increasing_sign(remainder, low, high):
    """Find a sign-changing contact by bisection, without assuming monotonicity."""
    assert remainder(low) < 0 < remainder(high)
    for _ in range(205):
        mid = (low + high) / 2
        if remainder(mid) < 0:
            low = mid
        else:
            high = mid
    return (low + high) / 2


def odd_contact(n):
    p = mp.pi / 3
    L = 2 ** (n - 1)

    def parameters(w):
        v = mp.exp(-w / 2)
        v2 = v * v
        h = v * (3 - v2)
        sine_half = h / (1 + mp.sqrt(1 + 4 * v * h))
        beta = 2 * mp.asin(sine_half)
        radius = mp.exp(-w / L)
        alpha = p - (p - beta) / L
        d_first = radius * (2 * mp.cos(alpha) - radius)
        d_last = v2 * (2 * mp.cos(beta) - v2)
        return radius, beta, alpha, d_first, d_last

    def remainder(w):
        *_, first, last = parameters(w)
        return first - last

    w = bisect_increasing_sign(remainder, mp.log(2), mp.log(L) + 3)
    r, beta, alpha, first, d = parameters(w)
    c = mp.sqrt(1 - d)
    theta = mp.pi - alpha
    slope_pen = (L // 2) * r ** (L // 2) * mp.cos(beta / 2) / c
    slope_first_or_last = max(r * mp.sin(alpha), L * r ** L * mp.sin(beta)) / c
    density = (1 / slope_pen + 1 / slope_first_or_last) / mp.pi
    assert abs(first - d) < mp.mpf("1e-56")
    return r, c, beta, theta, density


def even_gain(n):
    L = 2 ** (n - 1)

    def remainder(w):
        return 1 - mp.exp(-w / L) - mp.exp(-w)

    w = bisect_increasing_sign(remainder, mp.mpf(0), mp.log(L) + 3)
    r = mp.exp(-w / L)
    return mp.sqrt(1 - r + r * r)


def main():
    mp.mp.dps = 96
    odds = {}
    parity = {0: [], 1: []}
    csv_path = ROOT / "data" / "odd_constants.csv"
    csv_path.parent.mkdir(exist_ok=True)
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["n", "L", "r", "c", "one_minus_c", "beta_last_rad",
                         "pi_over_3_minus_beta", "upper_argument_rad",
                         "density_coefficient_K", "two_L_times_one_minus_c_minus_W_L"])
        for n in range(2, 82):
            L = 2 ** (n - 1)
            if n % 2:
                odds[n] = odd_contact(n)
                r, c, beta, theta, density = odds[n]
            else:
                c = even_gain(n)
            gap = 2 * L * (1 - c) - mp.lambertw(L)
            if n % 2:
                row = [r, c, 1 - c, beta, mp.pi / 3 - beta, theta, density, gap]
                writer.writerow([n, L, *(mp.nstr(value, 40) for value in row)])
            parity[n % 2].append((n, float(gap)))

    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 8.6, "mathtext.fontset": "dejavusans",
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.labelcolor": "#263849", "axes.edgecolor": "#7b8790",
        "xtick.color": "#425462", "ytick.color": "#425462",
        "axes.titlesize": 10, "pdf.fonttype": 42,
    })
    figure, (local, trend) = plt.subplots(1, 2, figsize=(6.55, 2.83))
    figure.subplots_adjust(left=.09, right=.983, bottom=.21, top=.84, wspace=.42)
    colors = ["#2670a6", "#b15527", "#168171"]
    r, c, _, theta, _ = map(float, odds[5])
    offset = np.linspace(-1.8, 1.8, 451)
    gains = {}
    for k, color, style in zip((1, 8, 16), colors, ("--", "-.", "-")):
        modulus = np.abs(1 + r ** k * np.exp(1j * k * (theta + offset / 1000)))
        gains[k] = (modulus - c) * 1000
        local.plot(offset, gains[k], color=color, linestyle=style, linewidth=1.45,
                   label=rf"$k={k}$")
    local.axhline(0, color="#a0aab1", linewidth=.65, zorder=0)
    local.scatter([0], [0], c="#182a38", marker="o", s=17, zorder=8)
    local.set_title("Three active powers at $n=5$", loc="left", fontweight="bold", pad=10)
    local.set(xlabel="Angle from the minimizer (mrad)",
              ylabel=r"$10^3\,(|1+z^k|-c_5)$", xlim=(-1.8, 1.8), ylim=(-5.15, 5.15))
    local.set_xticks([-1.5, 0, 1.5])
    local.set_yticks([-4, -2, 0, 2, 4])
    local.legend(loc="lower right", frameon=False, handlelength=2, labelspacing=.2,
                 borderpad=.12, fontsize=7.8)

    limit = float(mp.log(2) + mp.pi / mp.sqrt(3))
    trend.axhline(0, color="#697a83", lw=.8, ls=":", zorder=0)
    trend.axhline(limit, color="#697a83", lw=.8, ls=":", zorder=0)
    for p, label, color, marker in [(1, "Odd", "#168171", "o"),
                                    (0, "Even", "#2670a6", "s")]:
        n_values, gap_values = zip(*parity[p])
        trend.plot(n_values, gap_values, color=color, linewidth=1.35,
                   marker=marker, markevery=3, markersize=2.7, label=label)
    trend.set_title("The parity gap", loc="left", fontweight="bold", pad=10)
    trend.set(xlabel="Number of filters $n$", ylabel=r"$2L(1-c_n)-W(L)$",
              xlim=(0, 83), ylim=(-.55, 2.95))
    trend.set_xticks([0, 20, 40, 60, 80])
    trend.set_yticks([0, 1, 2])
    trend.text(80, limit + .10, r"$\log 2+\pi/\sqrt{3}$", ha="right",
               va="bottom", color="#425462", fontsize=8.1)
    trend.legend(loc="center right", frameon=False, handlelength=2, fontsize=8)
    for ax in (local, trend):
        ax.tick_params(direction="out", length=3, width=.65)
    path = ROOT / "figures" / "dyadic_contacts.pdf"
    path.parent.mkdir(exist_ok=True)
    figure.savefig(path, metadata={"Title": "Odd dyadic filters: numerical illustrations",
                                   "Creator": "code/illustrate.py",
                                   "CreationDate": None, "ModDate": None})
    plt.close(figure)


if __name__ == "__main__":
    main()
