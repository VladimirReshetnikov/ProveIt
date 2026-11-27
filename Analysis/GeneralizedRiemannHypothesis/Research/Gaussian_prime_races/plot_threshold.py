"""Draw the two finite-sum curves and two certified endpoints for the mod-4 race.

Requires Python 3, NumPy, and Matplotlib. Run next to certify_threshold.py.
The curves use floating-point approximations to the first ten ordinates.
Only the diamond symbols use outward rational enclosures for the full sums.
"""

from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from certify_threshold import (
    CENTERS, F, H_HIGH, H_LOW, WITNESS, centered_sum, cos_at, pi_bracket,
)


def main():
    baseline = F("0.04007656500")
    x_scale = 10**11
    y_scale = 10**9
    x_left = float((H_LOW - baseline) * x_scale)
    x_right = float((H_HIGH - baseline) * x_scale)
    x = np.linspace(45, 125, 301)
    h = float(baseline) + x / x_scale
    gamma = np.array(CENTERS, dtype=float)
    amplitudes = 2 * np.exp(-h[:, None] * gamma**2)
    envelope = y_scale * (0.5 - amplitudes.sum(axis=1))
    # At this witness, binary64 loses digits in the unreduced phase. Reduce
    # the product of rational centers first, then use floating-point plotting.
    pi_bounds = pi_bracket()
    phase_cosines = np.array([
        float(sum(cos_at(ordinate * WITNESS, pi_bounds)) / 2) for ordinate in CENTERS
    ])
    witness = y_scale * (0.5 + amplitudes @ phase_cosines)

    low_bounds = centered_sum(H_LOW, WITNESS)
    high_bounds = centered_sum(H_HIGH, F(0), envelope=True)
    assert low_bounds[1] < 0 < high_bounds[0]
    endpoint_y = [
        y_scale * float((upper + lower) / 2)
        for lower, upper in (low_bounds, high_bounds)
    ]
    endpoint_radius = [
        y_scale * float((upper - lower) / 2)
        for lower, upper in (low_bounds, high_bounds)
    ]

    plt.rcParams.update({
        "font.family": "DejaVu Sans", "mathtext.fontset": "stix",
        "font.size": 8.5, "pdf.fonttype": 42, "axes.linewidth": 0.6,
    })
    fig, ax = plt.subplots(figsize=(6.15, 2.9))
    fig.subplots_adjust(left=0.135, right=0.975, bottom=0.19, top=0.82)
    ink = "#263943"
    teal = "#187781"
    rust = "#a44728"
    ax.axvspan(x_left, x_right, facecolor="#e7edef", zorder=-4)
    for endpoint in (x_left, x_right):
        ax.axvline(endpoint, color="#84949b", linewidth=0.7, linestyle=":", zorder=-1)
    ax.axhline(0, color="#52626a", linewidth=0.9, zorder=0)
    ax.plot(x, witness, color=teal, linewidth=1.8, label="Witness (10 zeros)")
    ax.plot(x, envelope, color=rust, linewidth=1.8, linestyle="--",
            label="Lower envelope (10 zeros)")
    ax.errorbar((x_left, x_right), endpoint_y, yerr=endpoint_radius,
                fmt="D", color=ink, markersize=4.2, markeredgewidth=0.8,
                linewidth=1.2, capsize=4, label="Certified endpoints", zorder=5)
    for point, text_xy, annotation in (
        ((x_left, endpoint_y[0]), (58.9, 3.45), "Upper bound < −0.074"),
        ((x_right, endpoint_y[1]), (110.2, -3.9), "Lower bound > 0.047"),
    ):
        ax.annotate(annotation, xy=point, xytext=text_xy, color=ink, fontsize=8,
                    ha="center", va="center",
                    arrowprops={"arrowstyle": "-", "color": ink, "linewidth": 0.7,
                                "shrinkA": 2, "shrinkB": 4})
    ax.text((x_left + x_right) / 2, 10.65, r"Certified interval for $h_*$",
            color=ink, ha="center", va="center", fontsize=8)
    ax.set(xlim=(x[0], x[-1]), ylim=(-13.65, 12.85), xticks=(50, 62, 75, 90, 109, 120),
           yticks=(-10, -5, 0, 5, 10), xlabel=r"$10^{11}\,(h-0.04007656500)$",
           ylabel=r"Race value $\times\,10^9$")
    ax.grid(axis="y", color="#d7dde0", linewidth=0.4)
    ax.set_axisbelow(True)
    ax.spines[["top", "right"]].set_visible(False)
    ax.spines[["left", "bottom"]].set_color("#586b75")
    ax.tick_params(color="#586b75", labelcolor=ink, width=0.6, length=3)
    ax.legend(loc="lower center", bbox_to_anchor=(0.5, 1.035), ncol=3,
              frameon=False, handlelength=1.9, columnspacing=1.35,
              borderaxespad=0, fontsize=7.8)
    fig.savefig(Path(__file__).with_name("threshold_bounds.pdf"),
                metadata={"Title": "Certified bracket for the modulo-four smoothing threshold",
                          "CreationDate": None, "ModDate": None})
    plt.close(fig)


if __name__ == "__main__":
    main()
