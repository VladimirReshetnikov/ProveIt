#!/usr/bin/env python3
"""Create the article's static coupon-window figure from bounded evaluations.

Run after, or independently of, verify.py: python3 code/make_figures.py
Dependencies: matplotlib, mpmath, SymPy. No network access is used.
The finite-k curves use the same Bonferroni/pole error accounting as verify.py.
The curves are numerical diagnostics; see that script's rounding qualification.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import sys

sys.dont_write_bytecode = True

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp

from verify import coupon_probability, text_number, write_csv, write_json


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-root", type=Path,
                        default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    figures = args.output_root / "figures"
    data = args.output_root / "data"
    figures.mkdir(parents=True, exist_ok=True)
    data.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = 120
    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["DejaVu Serif"],
        "mathtext.fontset": "stix",
        "font.size": 11,
        "axes.labelsize": 12,
        "legend.fontsize": 10,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.linewidth": 0.7,
        "xtick.major.width": 0.7,
        "ytick.major.width": 0.7,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })
    figure, axis = plt.subplots(figsize=(6.7, 4.2), layout="constrained")
    records = []
    for k, color in ((20, "#2878B5"), (100, "#D16824"), (1000, "#277747")):
        sizes = sorted({int(mp.nint(k * (mp.log(k) - mp.mpf("1.5")
                                        + mp.mpf("3.5") * i / 160)))
                        for i in range(161)})
        abscissas, probabilities = [], []
        for n in sizes:
            s = mp.mpf(n) / k - mp.log(k)
            bounds = coupon_probability(n, k)
            abscissas.append(float(s))
            probabilities.append(float(bounds["midpoint"]))
            records.append({"k": k, "n": n, "s": text_number(s),
                            "probability": text_number(bounds["midpoint"]),
                            "analytic_bracket_width": text_number(bounds["width"])})
        axis.plot(abscissas, probabilities, color=color, linewidth=1.65,
                  label=rf"$k={k}$")
    grid = [-1.5 + 3.5 * i / 500 for i in range(501)]
    axis.plot(grid, [float(mp.exp(-mp.exp(-s))) for s in grid],
              color="#262626", linewidth=1.5, linestyle=(0, (4, 2.2)),
              label=r"Limit $\exp(-e^{-s})$")
    axis.set(xlim=(-1.5, 2), ylim=(-0.01, 1),
             xlabel=r"$s=n/k-\log k$",
             ylabel="Probability of no empty row")
    axis.set_xticks([-1.5, -1, -0.5, 0, 0.5, 1, 1.5, 2])
    axis.set_yticks([0, 0.2, 0.4, 0.6, 0.8, 1])
    axis.grid(axis="y", color="#DFE3E7", linewidth=0.55)
    axis.set_axisbelow(True)
    axis.legend(loc="upper left", frameon=False)
    figure.savefig(figures / "coupon_window.pdf", metadata={
        "Title": "Coupon window for packed matrix compositions",
        "Subject": "Finite-height probabilities and their limiting distribution",
        "Creator": "code/make_figures.py"})
    figure.savefig(figures / "coupon_window.png", dpi=220)
    plt.close(figure)
    write_csv(data / "coupon_curve.csv", records)
    write_json(data / "figure_generation_summary.json", {
        "status": "PASS",
        "generator": "code/make_figures.py",
        "matplotlib": matplotlib.__version__,
        "decimal_precision": mp.mp.dps,
        "finite_k_points": len(records),
        "height_values": [20, 100, 1000],
        "figure_inches": [6.7, 4.2],
        "png_dpi": 220,
        "files": ["figures/coupon_window.pdf", "figures/coupon_window.png"],
        "scope": "Numerical illustration; not a proof or directed-rounding certification.",
    })
    print(f"Wrote coupon_window.pdf and coupon_window.png ({len(records)} finite-k points).")


if __name__ == "__main__":
    main()
