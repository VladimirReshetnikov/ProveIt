#!/usr/bin/env python3
"""Recreate publication figures from the recorded measurements, without reruns."""
from __future__ import annotations
import json
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
ROOT = Path(__file__).resolve().parents[1]


def main():
    data = json.loads((ROOT / "results" / "benchmarks.json").read_text())
    diagonal = [x["summary"] for x in data["recognition"]
                if x["summary"]["name"].startswith("diagonal")]
    local = [x["summary"] for x in data["local"]]
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 10,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.labelcolor": "#16324f", "text.color": "#16324f",
        "svg.fonttype": "none",
    })
    fig, (ax, bx) = plt.subplots(2, 1, figsize=(6.3, 7.3),
                                gridspec_kw={"height_ratios": [1.05, 1]})
    x = [d["crossings"] for d in diagonal]
    completed = [d for d in diagonal if d["completed_baseline"]]
    ax.plot([d["crossings"] for d in completed],
            [d["median_baseline_seconds"] * 1000 for d in completed],
            "o-", color="#bb4f35", label="Previous path: completed")
    censored = [d for d in diagonal if not d["completed_baseline"]]
    ax.scatter([d["crossings"] for d in censored],
               [d["median_baseline_seconds"] * 1000 for d in censored],
               marker="x", s=65, color="#bb4f35", label="Previous path: UNKNOWN")
    ax.plot(x, [d["median_new_end_to_end_seconds"] * 1000 for d in diagonal],
            "s-", color="#597a99", label="Arithmetic + PD construction")
    ax.plot(x, [d["median_new_seconds"] * 1000 for d in diagonal],
            "o-", color="#006b70", label="Arithmetic recognition")
    ax.set_yscale("log")
    ax.set_xlabel("Displayed crossings in a diagonal unknot")
    ax.set_ylabel("Median elapsed time (ms, log scale)")
    ax.set_xticks(x)
    ax.grid(axis="y", which="major", color="#dde4e8", linewidth=0.7)
    ax.set_axisbelow(True)
    ax.set_title("A. Supplied rational-pair presentations", loc="left", fontsize=11)
    ax.legend(fontsize=8, loc="center left", frameon=False)
    names = ["Conway control", "8-crossing unknot", "Trefoil control",
             "Two-summand planted", "Three-summand planted"]
    ratios = [d["median_paired_speedup"] for d in local]
    colors = ["#bb4f35" if r < 1 else "#006b70" for r in ratios]
    y = list(range(len(local)))
    for yi, ratio, color in zip(y, ratios, colors):
        bx.hlines(yi, min(1, ratio), max(1, ratio), color=color, linewidth=4)
        bx.scatter([ratio], [yi], color=color, s=42, zorder=3)
    bx.set_yticks(y, names)
    bx.invert_yaxis()
    bx.set_xscale("log")
    bx.set_xlim(0.1, 2.0)
    bx.set_xticks([0.1, 0.2, 0.5, 1, 2], ["0.1", "0.2", "0.5", "1", "2"])
    bx.axvline(1, color="#16324f", linewidth=1, linestyle="--")
    for yi, ratio in zip(y, ratios):
        bx.text(ratio * (0.95 if ratio < 1 else 1.04), yi, f"{ratio:.2f}",
                va="center", ha="right" if ratio < 1 else "left", fontsize=9)
    bx.set_xlabel("Paired speedup (log scale)\n"
                  "Below 1 = slower; above 1 = faster")
    bx.set_title("B. Literal local-tangle search", loc="left", fontsize=11)
    bx.grid(axis="x", color="#dde4e8", linewidth=0.7)
    bx.set_axisbelow(True)
    fig.tight_layout(h_pad=2.1)
    out = ROOT / "article" / "figures"
    out.mkdir(parents=True, exist_ok=True)
    fig.savefig(out / "benchmarks.png", dpi=220, facecolor="white")
    fig.savefig(out / "benchmarks.svg", facecolor="white")
    print("Created article/figures/benchmarks.png and benchmarks.svg.")


if __name__ == "__main__":
    main()
