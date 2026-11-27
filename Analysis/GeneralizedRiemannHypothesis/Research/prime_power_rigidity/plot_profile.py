#!/usr/bin/env python3
"""Plot the zeta lag envelope and its one-sided derivatives at log(5).

Run with Python 3, NumPy and Matplotlib. Optional argument: PDF output path.
The gamma-factor sum is evaluated directly, with a uniform truncation bound
on the plotted range. The slopes are analytic one-sided derivatives.
"""
import argparse
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator, FormatStrFormatter
import numpy as np


def prime_powers(limit):
    """Return prime powers and their von Mangoldt weights through limit."""
    primes = [p for p in range(2, limit + 1)
              if all(p % d for d in range(2, int(p**0.5) + 1))]
    result = []
    for p in primes:
        n = p
        while n <= limit:
            result.append((n, np.log(p)))
            n *= p
    return sorted(result)


def profile(t, *, side="right"):
    """Evaluate E(t) and its indicated one-sided derivative, for t > 0."""
    t = np.atleast_1d(np.array(t, dtype=float))
    if np.min(t) <= 0:
        raise ValueError("formula requires positive lag")
    x = np.exp(t)
    prime_terms = np.zeros(t.shape)
    prime_sum = np.zeros(t.shape)
    for n, weight in prime_powers(int(np.ceil(max(x)))):
        # Compare on the log scale so that t=np.log(n) has an exact side.
        log_n = np.log(n)
        included = t >= log_n if side == "right" else t > log_n
        # Avoid subtracting nearly equal reciprocals at the cusp.
        prime_terms += included * weight * (-np.expm1(log_n - t)) / n
        prime_sum += included * weight
    root = np.exp(t / 2)
    w = root * (prime_terms - t + 1 + np.euler_gamma)
    w_prime = w / 2 + root * (prime_sum / x - 1)
    # Both tails are bounded by sum_{k>N} exp(-2k min(t)).
    z_max = np.exp(-2 * min(t))
    n_terms = max(1, int(np.ceil(np.log(1e-17 * (1 - z_max)) / np.log(z_max))))
    correction_sum = np.zeros(t.shape)
    derivative_sum = np.zeros(t.shape)
    for k in range(1, n_terms + 1):
        q = np.exp(-2 * k * t) / (2 * k + 1)
        derivative_sum += q
        correction_sum += q / (2 * k)
    correction = (np.log(2 * np.pi) - correction_sum) / root
    correction_prime = -correction / 2 + derivative_sum / root
    k0 = 2 + np.euler_gamma - np.log(4 * np.pi)
    return 2 * (k0 - w + correction), -2 * (w_prime - correction_prime)


def build_figure(path):
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 8.2,
        "mathtext.fontset": "dejavusans", "pdf.fonttype": 42,
        "axes.spines.right": False, "axes.spines.top": False,
        "axes.labelcolor": "#243742", "xtick.color": "#425564",
        "ytick.color": "#425564", "axes.edgecolor": "#70818a",
        "figure.facecolor": "white",
    })
    blue, copper, gray = "#17546a", "#a84f2c", "#ced8dc"
    fig, (main, detail) = plt.subplots(
        1, 2, figsize=(7.0, 2.95), gridspec_kw={"width_ratios": [1.72, 1]},
        layout="constrained")
    x_min, x_max = 1.15, 13.6
    nodes = np.array([np.log(n) for n, _ in prime_powers(int(x_max))])
    grid = np.unique(np.r_[np.linspace(np.log(x_min), np.log(x_max), 2401), nodes])
    main.plot(grid, profile(grid)[0], color=blue, lw=1.4)
    main.scatter(nodes, profile(nodes)[0], s=10, c=blue, zorder=3)
    t5 = np.log(5)
    main.scatter([t5], profile([t5])[0], s=28, c=copper, zorder=4)
    main.set_xticks(np.log([2, 3, 5, 8, 13]),
                    [r"$\log 2$", r"$\log 3$", r"$\log 5$", r"$\log 8$", r"$\log 13$"])
    main.set(xlim=(grid[0], grid[-1]), xlabel="Logarithmic lag  $h$", ylabel=r"$E(h)$")
    main.yaxis.set_major_locator(MaxNLocator(nbins=5))
    main.yaxis.set_major_formatter(FormatStrFormatter("%.2f"))
    main.set_title("A    Lag envelope", loc="left", fontweight="semibold")

    # Separate domains and endpoint conventions preserve the discontinuity.
    span = 0.045
    offsets_left = np.linspace(-span, 0, 181)
    offsets_right = np.linspace(0, span, 181)
    for offsets, side in [(offsets_left, "left"), (offsets_right, "right")]:
        _, slope = profile(t5 + offsets, side=side)
        detail.plot(offsets, slope, color=blue, lw=1.6)
    left_value = profile([t5], side="left")[1].item()
    right_value = profile([t5], side="right")[1].item()
    jump = right_value - left_value
    assert abs(jump + 2 * np.log(5) / np.sqrt(5)) < 1e-12
    detail.plot([0, 0], [right_value, left_value], ls=":", lw=1.1, color=copper)
    detail.scatter([0, 0], [right_value, left_value], facecolor="white",
                   edgecolor=copper, linewidth=1.4, s=27, zorder=4)
    detail.set(xlabel=r"$h-\log 5$", ylabel=r"$E'(h)$", xlim=(-span, span))
    detail.set_xticks([-.04, 0, .04], ["−0.04", "0", "0.04"])
    detail.set_title("B    Slopes at $\\log 5$", loc="left", fontweight="semibold")
    detail.yaxis.set_major_locator(MaxNLocator(nbins=5))
    for ax in (main, detail):
        ax.grid(axis="y", color=gray, lw=.5, alpha=.75)
        ax.set_axisbelow(True)
        ax.tick_params(length=3, width=.7, labelsize=7.8)
    fig.savefig(path, bbox_inches="tight", pad_inches=.05)
    plt.close(fig)
    print(f"Slope jump at log(5): {jump:.12f}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", nargs="?", type=Path,
                        default=Path(__file__).with_name("lag_profile.pdf"))
    build_figure(parser.parse_args().output)
