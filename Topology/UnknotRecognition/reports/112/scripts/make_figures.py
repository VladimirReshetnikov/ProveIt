#!/usr/bin/env python3
"""Recreate the article's figures and numerical tables from retained JSON."""
from pathlib import Path
import json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter

ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "article" / "figures"
TABLES = ROOT / "article" / "tables"
FIGURES.mkdir(parents=True, exist_ok=True)
TABLES.mkdir(parents=True, exist_ok=True)

synthetic = json.loads((ROOT / "results" / "synthetic_benchmark.json").read_text())
native = json.loads((ROOT / "results" / "native_benchmark.json").read_text())
chambers = json.loads((ROOT / "results" / "chamber_graph_audit.json").read_text())
ink, teal, rust = "#1c394d", "#14707c", "#a55d30"
plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 10,
    "axes.labelcolor": ink, "text.color": ink, "axes.edgecolor": "#aebdc4",
    "axes.spines.top": False, "axes.spines.right": False,
    "pdf.fonttype": 42, "ps.fonttype": 42,
})

fig, ax = plt.subplots(figsize=(7.3, 4.1), layout="constrained")
for backend, label, color in [
    ("flat", "Baseline flat replay", rust),
    ("lazy", "Lazy replay", teal),
]:
    hs = [c["steps"] for c in synthetic["cases"]]
    seconds = [c["medians"][backend] for c in synthetic["cases"]]
    ax.plot(hs, seconds, "o-", color=color, label=label, linewidth=2)
    for c in synthetic["cases"]:
        ax.scatter([c["steps"]] * len(c["samples"][backend]),
                   c["samples"][backend], color=color, alpha=.30, s=23)
ax.set_xscale("log", base=2)
ax.set_yscale("log")
ax.set_xticks(hs)
ax.xaxis.set_major_formatter(ScalarFormatter())
ax.set_xlabel(r"Star depth $H$; width $L=H^2$")
ax.set_ylabel("Complete weighted verification (seconds)")
ax.grid(axis="y", which="major", color="#e2e8ec")
ax.legend(frameon=False, loc="upper left")
ax.set_title("Complete legal certificates; three paired rounds", loc="left",
             fontweight="bold", pad=12)
fig.savefig(FIGURES / "synthetic_replay.pdf")
fig.savefig(FIGURES / "synthetic_replay.png", dpi=180)
plt.close(fig)

lines = [
    r"\begin{tabular}{rrrrr}",
    r"\toprule",
    r"$H$ & $L$ & Flat (s) & Lazy (s) & Ratio \\",
    r"\midrule",
]
for c in synthetic["cases"]:
    lines.append(f'{c["steps"]} & {c["width"]:,} & '
                 f'{c["medians"]["flat"]:.6f} & '
                 f'{c["medians"]["lazy"]:.6f} & '
                 f'{c["speedup"]:.3f}' + r"$\times$ \\")
lines.extend([r"\bottomrule", r"\end{tabular}"])
(TABLES / "synthetic.tex").write_text("\n".join(lines) + "\n")

labels = [
    "Pilot LST, moments", "Pilot trefoil, moments", "Solid torus/RP3, moments",
    "Interior mixed, moments", "Fibonacci 09 mixed, moments", "Trefoil mixed, moments",
    "Pilot LST, masks", "Interior mixed, masks",
    "Layered meridian $T=4$", "Layered meridian $T=8$", "Layered meridian $T=16$",
]
lines = [
    r"\begin{tabular}{lrrrr}",
    r"\toprule",
    r"Source/method & Flat replay & Lazy replay & Replay ratio & Query ratio \\",
    r"\midrule",
]
for label, c in zip(labels, native["cases"]):
    med = c["medians"]
    lines.append(f'{label} & {med["flat"]["replay_seconds"]:.4f} & '
                 f'{med["lazy"]["replay_seconds"]:.4f} & '
                 f'{c["replay_speedup"]:.3f} & {c["full_query_speedup"]:.3f}' + r" \\")
sums = native["sum_case_medians"]
lines.extend([
    r"\midrule",
    "Sum of case medians & "
    f'{sums["flat"]["replay_seconds"]:.4f} & '
    f'{sums["lazy"]["replay_seconds"]:.4f} & '
    f'{sums["flat"]["replay_seconds"]/sums["lazy"]["replay_seconds"]:.3f} & '
    f'{sums["flat"]["total_seconds"]/sums["lazy"]["total_seconds"]:.3f}' + r" \\",
    r"\bottomrule", r"\end{tabular}",
])
(TABLES / "native.tex").write_text("\n".join(lines) + "\n")

lines = [
    r"\begin{tabular}{rrrrrr}",
    r"\toprule",
    r"$T$ & Coordinate bits & Orbit cycles & Proof bytes & Produce (s) & Replay (s) \\",
    r"\midrule",
]
for c in chambers["connected_binary_stress"]:
    lines.append(f'{c["tetrahedra"]} & {c["maximum_coordinate_bits"]} & '
                 f'{c["stats"]["orbit_cycles"]} & {c["certificate_bytes"]:,} & '
                 f'{c["producer_seconds"]:.4f} & {c["replay_seconds"]:.4f}' + r" \\")
lines.extend([r"\bottomrule", r"\end{tabular}"])
(TABLES / "chambers.tex").write_text("\n".join(lines) + "\n")
print("Recreated one figure and three tables from the retained observations.")
