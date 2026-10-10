#!/usr/bin/env python3
"""Plot proved sufficient thresholds, not measured onset of zero saturation."""
import json
from math import log10
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

BASE = Path(__file__).resolve().parents[1]
rows = json.loads((BASE / "data/mesh_arithmetic_certificate.json").read_text())["thresholds"]
plt.rcParams.update({"font.size": 10, "axes.spines.top": False,
                     "axes.spines.right": False, "savefig.bbox": "tight"})
fig, axes = plt.subplots(1, 2, figsize=(9.2, 3.4),
                         gridspec_kw={"width_ratios": [1.55, 1]})
specs = [
    ("incoming_threshold", "Incoming sufficient threshold", "#66758c", "-"),
    ("polynomial_threshold", "Polynomial threshold", "#125d8b", "-"),
    ("hybrid_threshold", "Combined mesh bounds", "#c97732", "--"),
]
for ax, limit in zip(axes, (40, 8)):
    chosen = [r for r in rows if r["n"] <= limit]
    for key, label, color, style in specs:
        ax.plot([r["n"] for r in chosen],
                [log10(int(r[key])) for r in chosen],
                linestyle=style, color=color, label=label, linewidth=1.8,
                marker="o" if limit == 8 else None, markersize=3.5)
    ax.set_xlabel("Appell degree $n$")
    ax.grid(axis="y", color="#d8dde3", linewidth=.65, alpha=.75)
    ax.set_xlim(2, limit)
axes[0].set_ylabel(r"$\log_{10}$ of sufficient derivative order")
axes[0].set_title("Change in degree dependence", loc="left", fontsize=11)
axes[1].set_title("Small-degree comparison", loc="left", fontsize=11)
axes[1].set_xticks(range(2, 9))
handles, labels = axes[0].get_legend_handles_labels()
fig.legend(handles, labels, loc="lower center", ncol=3, frameon=False,
           bbox_to_anchor=(.5, -.035), fontsize=9)
fig.tight_layout(rect=(0, .06, 1, 1))
out = BASE / "figures"
out.mkdir(exist_ok=True)
for suffix in ("pdf", "png"):
    fig.savefig(out / ("mesh_threshold_comparison." + suffix), dpi=180)
plt.close(fig)
print("Wrote the mesh threshold comparison figure.")
