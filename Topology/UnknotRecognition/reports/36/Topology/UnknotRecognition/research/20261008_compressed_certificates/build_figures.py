"""Build publication figures from the recorded measurements, without rerunning them.

Run from any directory: python3 path/to/build_figures.py
Requires matplotlib; all numerical inputs are included in the release.
Ranges shown are observed sample ranges, not confidence intervals.
"""

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = HERE / "article" / "figures"
INK = "#193B4B"
TEAL = "#187F86"
ORANGE = "#B75B27"
GRAY = "#78838B"


def configure():
    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 9,
        "axes.titlesize": 10,
        "axes.labelsize": 9,
        "axes.edgecolor": "#B0BAC0",
        "axes.labelcolor": INK,
        "text.color": INK,
        "xtick.color": INK,
        "ytick.color": INK,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "grid.color": "#DCE3E6",
        "grid.linewidth": 0.6,
        "legend.frameon": False,
        "pdf.fonttype": 42,
    })


def save(fig, name):
    fig.savefig(OUT / (name + ".pdf"), bbox_inches="tight")
    fig.savefig(OUT / (name + ".png"), bbox_inches="tight", dpi=180)
    plt.close(fig)


def normal_figures():
    data = json.loads((ROOT / "fast/certificate_research/results/normal_disk_benchmark.json").read_text())
    rows = data["rows"]
    fig, axes = plt.subplots(1, 2, figsize=(9.0, 3.45), layout="constrained")
    ax = axes[0]
    compared = [row for row in rows if "regina" in row["completed"]]
    for arm, color, label in [
        ("checker", TEAL, "Independent certificate check"),
        ("regina", ORANGE, "Regina: known connected"),
    ]:
        valid = [r for r in compared if r["completed"].get(arm) == data["measured_rounds"]]
        x = [r["tetrahedra"] for r in valid]
        y = [1000 * r["median_seconds"][arm] for r in valid]
        ax.plot(x, y, "o-", color=color, label=label, markersize=4, linewidth=1.5)
        lo = [1000 * min(s["results"][arm]["seconds"] for s in r["samples"]) for r in valid]
        hi = [1000 * max(s["results"][arm]["seconds"] for s in r["samples"]) for r in valid]
        ax.fill_between(x, lo, hi, color=color, alpha=.12, linewidth=0)
    ax.set_yscale("log")
    ax.set_xticks([6, 10, 14, 18, 22])
    ax.set_xlabel("Tetrahedra")
    ax.set_ylabel("Completed predicate time (ms)")
    ax.set_title("A. Supplied-surface comparison", loc="left", pad=9)
    ax.grid(axis="y", which="major")
    ax.legend(loc="upper left", fontsize=7.3)
    ax.text(.99, .03, "Regina at t = 22: 5/5 memory failures\n768 MiB cap; no completion time plotted",
            ha="right", va="bottom", transform=ax.transAxes, fontsize=7,
            bbox={"facecolor": "white", "edgecolor": "none", "alpha": .92})
    ax.set_ylim(.2, 4000)
    ax = axes[1]
    x = [r["tetrahedra"] for r in rows]
    for arm, color, linestyle, label in [
        ("checker", TEAL, "-", "Certificate check"),
        ("checker_control", GRAY, "--", "Same-checker control"),
    ]:
        y = [1000 * r["median_seconds"][arm] for r in rows]
        ax.plot(x, y, "o", color=color, linestyle=linestyle, label=label,
                markersize=3.5, linewidth=1.3)
    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.set_xticks([1, 4, 16, 64, 256])
    ax.get_xaxis().set_major_formatter(ScalarFormatter())
    ax.set_xlabel("Tetrahedra (log scale)")
    ax.set_ylabel("Completed certificate time (ms)")
    ax.set_title("B. Encoded inputs through 256 tetrahedra", loc="left", pad=9)
    ax.grid(axis="y", which="major")
    ax.legend(loc="upper left", fontsize=7.5)
    save(fig, "normal_verification")


def gluing_figures():
    data = json.loads((ROOT / "fast/results/regular_cover_gluing_20261008.json").read_text())
    fig, ax = plt.subplots(figsize=(8.2, 3.6), layout="constrained")
    for scenario, color, name in [
        ("tree_boundary_constraints", TEAL, "Tree: 63 edges"),
        ("cycle_constraints", ORANGE, "Cycles: 80 edges"),
    ]:
        rows = [r for r in data["benchmark"]["cases"] if r["scenario"] == scenario]
        for metric, linestyle, scope in [
            ("validated_compare_seconds", "-", "full validation + comparison"),
            ("prepared_compare_seconds", "--", "prepared comparison"),
        ]:
            x = [r["bits"] for r in rows]
            y = [1000 * r["medians"][metric] for r in rows]
            ax.plot(x, y, "o", color=color, linestyle=linestyle, markersize=4,
                    linewidth=1.5, label=name + "; " + scope)
    ax.set_xscale("log", base=2)
    ax.set_xticks([39, 135, 519, 2055, 8199, 24007])
    ax.set_xticklabels(["39", "135", "519", "2,055", "8,199", "24,007"])
    ax.set_xlabel("Modulus bit length (log scale)")
    ax.set_ylabel("Median comparison time (ms)")
    ax.set_ylim(0, 8.7)
    ax.set_title("Regular-cover assemblies: 64 blocks and 32 boundary marks", loc="left", pad=10)
    ax.grid(axis="y")
    ax.legend(loc="upper left", fontsize=8)
    save(fig, "gluing_scaling")


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    configure()
    normal_figures()
    gluing_figures()
    for path in sorted(OUT.iterdir()):
        print(path.relative_to(HERE))


if __name__ == "__main__":
    main()
