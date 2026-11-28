#!/usr/bin/env python3
"""Draw proved limiting formulas and create a compact table for the paper."""
import json
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / "results/profiles.json").read_text())
rows = data["profiles"]

def g(q, j):
    out = 1.0
    for a in range(1, j+1):
        out *= 1.0-q**(-a)
    return out

plt.rcParams.update({"font.size": 9, "axes.spines.top": False,
                     "axes.spines.right": False, "font.family": "DejaVu Sans",
                     "axes.titleweight": "semibold", "pdf.fonttype": 42})
fig, axes = plt.subplots(1, 2, figsize=(7.1, 3.0), layout="constrained")
offsets = list(range(-5, 6))
for q, color, marker in [(2, "#16324f", "o"), (3, "#168a81", "s"), (5, "#b86e22", "^")]:
    axes[0].plot(offsets, [g(q, 250)/g(q, abs(u)) for u in offsets],
                 marker=marker, markersize=3.8, color=color, linewidth=1.5, label=f"q = {q}")
axes[0].set(title="Maximal code-product dimension", xlabel="Length offset u = N − D",
            ylabel="Limiting probability", ylim=(0, 1.035))
axes[0].legend(frameon=False, loc="lower left")
binary = [r for r in rows if r["q"] == 2]
axes[1].plot([r["a"] for r in binary], [float(r["full_tv"]) for r in binary],
             color="#16324f", marker="o", markersize=3.8, linewidth=1.8, label="Full observations")
axes[1].plot([r["a"] for r in binary], [float(r["dimension_tv"]) for r in binary],
             color="#168a81", marker="s", markersize=3.5, linewidth=1.5, label="Dimension only")
axes[1].set(title="Detecting a hidden binary form", xlabel="Sample offset a = t − (D − 1)",
            ylabel="Limiting total variation", ylim=(0, 1.035))
axes[1].legend(frameon=False, loc="upper left")
for ax in axes:
    ax.set_xticks([-5, -3, -1, 0, 1, 3, 5])
    ax.grid(axis="y", color="#dfe6ec", linewidth=.65)
    ax.set_axisbelow(True)
fig.savefig(ROOT / "results/critical_profiles.pdf")
fig.savefig(ROOT / "results/critical_profiles.png", dpi=200)
plt.close(fig)

selected = [r for r in rows if (r["q"] == 2 and -3 <= r["a"] <= 3) or (r["q"] != 2 and r["a"] == 0)]
lines = [r"\begin{table}[htbp]", r"\centering\small",
         r"\begin{tabular}{@{}rrrrrr@{}}", r"\toprule",
         r"$q$ & $a$ & Full TV & Dimension TV & Recovery & Elimination \\", r"\midrule"]
for r in selected:
    vals = [f"{float(r[k]):.8f}" for k in ["full_tv", "dimension_tv", "optimal_recovery", "elimination_recovery"]]
    lines.append(f"{r['q']} & {r['a']} & " + " & ".join(vals) + r" \\")
lines += [r"\bottomrule", r"\end{tabular}",
          r"\caption{Selected limiting probabilities. Recovery is the optimal posterior success probability; elimination requires a one-dimensional compatible linear space. The full 44-profile table is included as CSV and JSON. Displayed digits are rounded from certified evaluations.}",
          r"\label{tab:selected-profiles}", r"\end{table}"]
(ROOT / "results/selected_profile_table.tex").write_text("\n".join(lines) + "\n")
print("Created critical_profiles.pdf/.png and selected_profile_table.tex")
