"""Regenerate exact profiles and plots from the delivered raw measurements."""
from pathlib import Path
import csv
import json
import statistics
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "fast"))
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator
from fastunknot.twist.core import Run
from fastunknot.twist.tail import tail_homology, expand_profile

OUT = ROOT / "article" / "figures"
OUT.mkdir(parents=True, exist_ok=True)
plt.rcParams.update({
    "font.family": "DejaVu Sans",
    "font.size": 9,
    "axes.titlesize": 10,
    "axes.labelsize": 9,
    "legend.fontsize": 8,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
})
NAVY, TEAL, GOLD = "#183347", "#008891", "#c28b32"


def save(fig, name):
    fig.savefig(OUT / (name + ".pdf"), bbox_inches="tight")
    fig.savefig(OUT / (name + ".png"), dpi=220, bbox_inches="tight")
    plt.close(fig)


fig, axes = plt.subplots(1, 2, figsize=(7, 2.65), sharex=True, sharey=True)
for ax, magnitude in zip(axes, (5, 13)):
    runs = [Run(1, magnitude), Run(2, -1), Run(1, 1), Run(2, -1)]
    answer = tail_homology(3, runs)
    profile = expand_profile(answer["degree_profile"])
    low, high = 3, magnitude - 3
    degrees = sorted(profile)
    colors = [TEAL if low <= h <= high else NAVY if h <= 2 else GOLD
              for h in degrees]
    if low <= high:
        ax.axvspan(low - .45, high + .45, color=TEAL, alpha=.08, zorder=0)
    ax.vlines(degrees, 0, [profile[h] for h in degrees], colors=colors, lw=2)
    ax.scatter(degrees, [profile[h] for h in degrees], c=colors, s=27, zorder=3)
    ax.set_title(f"m = {magnitude}  |  total reduced rank {answer['reduced_rank']}")
    ax.set_xlabel("Macro homological degree h")
    ax.set_xlim(-3, 15)
    ax.set_ylim(0, 4.1)
    ax.xaxis.set_major_locator(MaxNLocator(integer=True, nbins=7))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    ax.grid(axis="y", color="#d9dfe3", alpha=.65)
axes[0].set_ylabel("Dimension in degree h")
axes[1].text(6.5, 3.5, "inserted interval: slope 3", color=TEAL,
             ha="center", fontsize=8)
fig.tight_layout(w_pad=2)
save(fig, "exact_profile")

raw = json.loads((ROOT / "results" / "benchmark_tail.json").read_text())
families = [
    ("two_strand_", "Two strands"),
    ("figure_eight_context_", "Figure-eight context"),
    ("four_strand_mixed_", "Four-strand link"),
]
fig, axes = plt.subplots(1, 3, figsize=(7.15, 2.7), sharey=True)
for ax, (prefix, title) in zip(axes, families):
    records = [r for r in raw["records"] if r["name"].startswith(prefix)]
    lengths = [abs(r["runs"][r["selected"]][1]) for r in records]
    for method, label, color in (("a", "Ordinary macro", NAVY),
                                 ("b", "Exact recurrence", TEAL)):
        series = []
        for record in records:
            if method == "a":
                series.append([500*(r["a_before_seconds"]+r["a_after_seconds"])
                               for r in record["rounds"]])
            else:
                series.append([1000*r["b_seconds"] for r in record["rounds"]])
        medians = [statistics.median(s) for s in series]
        low = [statistics.quantiles(s, n=4)[0] for s in series]
        high = [statistics.quantiles(s, n=4)[2] for s in series]
        ax.plot(lengths, medians, marker="o", ms=3.5, color=color, label=label)
        ax.fill_between(lengths, low, high, color=color, alpha=.12)
    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.set_title(title)
    ax.set_xlabel("Selected run length m")
    ax.set_xticks((17, 65, 257, 1025), ("17", "65", "257", "1025"))
    ax.tick_params(axis="x", labelsize=8)
    ax.grid(which="major", alpha=.2)
axes[0].set_ylabel("Time per full homology call (ms)")
axes[0].legend(loc="upper left", frameon=False, fontsize=7)
fig.tight_layout(w_pad=1.2)
save(fig, "tail_scaling")

with (ROOT / "results" / "streaming_summary.csv").open(newline="") as handle:
    records = list(csv.DictReader(handle))
labels = [
    "Two strands, n=801",
    "Two strands, n=10001",
    "Opposite runs, n=81",
    "Mixed three strands, n=14",
    "Conjugated unknot, n=30",
    "Mixed four strands, n=37",
    "Weaving, n=8",
    "Morton unknot, n=11",
]
fig, axes = plt.subplots(1, 2, figsize=(7, 3.6), sharey=True,
                         gridspec_kw={"width_ratios": [1, 1.1]})
y = list(range(len(records)))
time_ratios = [float(r["paired_time_ratio"]) for r in records]
memory_ratios = [float(r["peak_allocation_ratio"]) for r in records]
axes[0].barh(y, time_ratios, color=NAVY, height=.63)
axes[1].barh(y, memory_ratios, color=TEAL, height=.63)
axes[0].set_yticks(y, labels)
axes[0].invert_yaxis()
for ax, values in zip(axes, (time_ratios, memory_ratios)):
    ax.axvline(1, color="#555555", lw=.8, linestyle="--")
    ax.grid(axis="x", alpha=.2)
    for yy, value in zip(y, values):
        ax.text(value + .025, yy, f"{value:.2f}", va="center", fontsize=8)
axes[0].set_xlim(0, 1.15)
axes[1].set_xlim(0, 3.65)
axes[0].set_xlabel("Time ratio: original / streamed")
axes[1].set_xlabel("Peak traced bytes: original / streamed")
axes[0].set_title("Full homology is slower")
axes[1].set_title("Peak allocation is smaller")
fig.tight_layout(w_pad=1)
save(fig, "streaming_tradeoff")
print("Generated three vector PDF figures and three PNG previews.")
