#!/usr/bin/env python3
"""Rebuild the article's vector figures from the recorded raw measurements."""
import json
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "article" / "figures"
OUT.mkdir(parents=True, exist_ok=True)
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "axes.titleweight": "bold", "pdf.fonttype": 42,
                     "savefig.facecolor": "white"})
colors = ["#53657a", "#b2bfcd", "#0d8587"]
timing = json.loads((ROOT / "results/paired_native_benchmark.json").read_text())
native = json.loads((ROOT / "results/native_forest_solver_audit.json").read_text())
fig, axes = plt.subplots(1, 2, figsize=(8.3, 3.45), layout="constrained")
for index, (name, label) in enumerate((("baseline", "Baseline"),
                                    ("source_reuse", "Source reuse"), ("final", "Final patch"))):
    values = [timing["aggregate"][name][kind] for kind in ("produce", "replay", "total")]
    axes[0].bar(np.arange(3) + (index-1)*0.25, values, 0.25, label=label, color=colors[index])
axes[0].set_xticks(np.arange(3), ["Production", "Replay", "Full query"])
axes[0].set_ylabel("Sum of per-case medians (seconds)")
axes[0].set_title("A  Native runtime")
axes[0].legend(frameon=False, fontsize=8)
for index, (name, label) in enumerate((("canonical", "Canonical forest"), ("optimal", "$E_3$-first forest"))):
    counts = native["summary"][name]["parameters"]["k"]
    values = [counts.get(str(k), 0) for k in range(5)]
    bars = axes[1].bar(np.arange(5)+(index-0.5)*0.34, values, 0.34,
                       label=label, color=colors[0 if index==0 else 2])
    axes[1].bar_label(bars, labels=[str(v) if v else "" for v in values], padding=3, fontsize=8)
axes[1].set_xticks(np.arange(5))
axes[1].set_xlabel("Exceptional columns, $k$")
axes[1].set_ylabel("Native cases")
axes[1].set_ylim(0, 114)
axes[1].set_title("B  Raw source parameter")
axes[1].legend(frameon=False, fontsize=8, loc="upper right")
for ax in axes:
    ax.set_axisbelow(True)
    ax.grid(axis="y", color="#e5e9ed", linewidth=0.7)
for suffix in ("pdf", "png"):
    fig.savefig(OUT / f"native_results.{suffix}", dpi=180)
plt.close(fig)

micro = json.loads((ROOT / "results/gap_prefix_scaling.json").read_text())
fig, ax = plt.subplots(figsize=(6.5, 3.4), layout="constrained")
x = [case["pairings"] for case in micro["cases"]]
for method, color, label in (("naive", colors[0], "Naive prefix rescans"),
                             ("prefix", colors[2], "Prefix table + binary search")):
    medians = [case["median_seconds"][method] for case in micro["cases"]]
    low = [min(s[method] for s in case["samples"]) for case in micro["cases"]]
    high = [max(s[method] for s in case["samples"]) for case in micro["cases"]]
    ax.plot(x, medians, marker="o", linewidth=1.7, color=color, label=label)
    ax.fill_between(x, low, high, color=color, alpha=0.13)
ax.set_xscale("log", base=2)
ax.set_yscale("log")
ax.set_xticks(x, [str(n) for n in x])
ax.set_xlabel("Number of pairings (equal to number of gaps)")
ax.set_ylabel("Endpoint mapping time (seconds)")
ax.set_title("Isolated endpoint transport; five paired observations")
ax.legend(frameon=False)
ax.grid(color="#e5e9ed", linewidth=0.7)
for suffix in ("pdf", "png"):
    fig.savefig(OUT / f"prefix_scaling.{suffix}", dpi=180)
plt.close(fig)
