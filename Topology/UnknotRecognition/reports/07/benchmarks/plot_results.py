"""Regenerate the paper's two-panel performance figure from archived JSON.

From fast/: python ../benchmarks/plot_results.py
Requires matplotlib.  This script plots recorded data; it runs no benchmarks.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from statistics import median

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FixedLocator, FuncFormatter, NullLocator


HERE = Path(__file__).resolve().parent
NAVY = "#15324F"
TEAL = "#14666B"
MUTED = "#5A6570"
GRID = "#DCE2E7"


def read_series(structural_path: Path, component_path: Path) -> tuple:
    structural = json.loads(structural_path.read_text(encoding="utf-8"))
    component = json.loads(component_path.read_text(encoding="utf-8"))
    weaving = sorted(
        (row for name, row in structural["cases"].items()
         if name.startswith("weaving_3_")),
        key=lambda row: row["crossings"],
    )
    if not weaving:
        raise ValueError("no weaving_3_* cases in the structural report")
    crossings = [row["crossings"] for row in weaving]
    # Convert seconds to milliseconds after recomputing medians from samples.
    baseline_ms = [1000 * median(s["A"]["wall_seconds"] for s in row["samples"])
                   for row in weaving]
    seifert_ms = [1000 * median(s["B"]["wall_seconds"] for s in row["samples"])
                  for row in weaving]
    rounds = {len(row["samples"]) for row in weaving}
    if len(rounds) != 1:
        raise ValueError("weaving cases have inconsistent numbers of rounds")
    names = ("conway", "conway_sum_2", "conway_sum_3")
    metric = "max_objects_before_elimination"
    baseline_objects, shared_objects = [], []
    for name in names:
        record = component["cases"][name]["metrics"]
        old = record["A1"]["stats"][metric]
        if old != record["A2"]["stats"][metric]:
            raise ValueError(f"A/A object counts differ for {name}")
        baseline_objects.append(old)
        shared_objects.append(record["full"]["stats"][metric])
    if any(value <= 0 for series in (crossings, baseline_ms, seifert_ms,
                                     baseline_objects, shared_objects) for value in series):
        raise ValueError("logarithmic plots require positive values")
    return (crossings, baseline_ms, seifert_ms, rounds.pop(),
            baseline_objects, shared_objects)


def draw(structural_path: Path, component_path: Path, output_dir: Path) -> list[Path]:
    (crossings, baseline_ms, seifert_ms, rounds,
     baseline_objects, shared_objects) = read_series(structural_path, component_path)
    style = {
        "font.family": "DejaVu Sans",
        "font.size": 8.2,
        "axes.labelsize": 8.4,
        "axes.titlesize": 9.5,
        "axes.titleweight": "bold",
        "axes.labelcolor": NAVY,
        "text.color": NAVY,
        "xtick.color": MUTED,
        "ytick.color": MUTED,
        "xtick.labelsize": 7.8,
        "ytick.labelsize": 7.8,
        "axes.edgecolor": MUTED,
        "axes.linewidth": 0.65,
        "legend.fontsize": 7.6,
        "legend.frameon": False,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "savefig.facecolor": "white",
        "figure.facecolor": "white",
    }
    with plt.rc_context(style):
        fig, (left, right) = plt.subplots(1, 2, figsize=(6.5, 3.15))
        fig.subplots_adjust(left=0.105, right=0.985, bottom=0.205,
                            top=0.795, wspace=0.46)
        for ax in (left, right):
            ax.spines[["top", "right"]].set_visible(False)
            ax.set_axisbelow(True)
            ax.grid(axis="y", which="major", color=GRID, linewidth=0.65)
            ax.tick_params(which="major", direction="out", length=3, width=0.6)

        # Panel A: empirical medians only. Lines connect recorded points.
        left.set_xscale("log")
        left.set_yscale("log")
        left.plot(crossings, baseline_ms, color=NAVY, marker="o", markersize=4.1,
                  linewidth=1.4, markeredgecolor="white", markeredgewidth=0.45,
                  label="Baseline")
        left.plot(crossings, seifert_ms, color=TEAL, marker="s", markersize=3.9,
                  linewidth=1.4, linestyle="--", markeredgecolor="white",
                  markeredgewidth=0.45, label="Seifert first")
        left.set_xlim(3.2, 1250)
        left.set_ylim(0.01, 120)
        left.xaxis.set_major_locator(FixedLocator([4, 10, 100, 1000]))
        left.xaxis.set_major_formatter(FuncFormatter(lambda value, _: f"{value:,.0f}"))
        left.yaxis.set_major_locator(FixedLocator([0.01, 0.1, 1, 10, 100]))
        left.yaxis.set_major_formatter(FuncFormatter(lambda value, _: f"{value:g}"))
        left.xaxis.set_minor_locator(NullLocator())
        left.yaxis.set_minor_locator(NullLocator())
        left.set_xlabel("Crossings", labelpad=6)
        left.set_ylabel("Median time (ms)", labelpad=6)
        left.set_title("A  Recognition function", loc="left", pad=28)
        left.text(0, 1.035, f"Weaving 3-braid knots; {rounds}-round medians",
                  transform=left.transAxes, fontsize=7.7, color=MUTED,
                  ha="left", va="bottom")
        left.legend(loc="upper left", borderaxespad=0.35, handlelength=2.3,
                    labelspacing=0.45)

        # Panel B: deterministic counts from raw scanners, not factored calls.
        positions = list(range(3))
        width = 0.32
        left_positions = [value - width / 2 - 0.015 for value in positions]
        right_positions = [value + width / 2 + 0.015 for value in positions]
        right.bar(left_positions, baseline_objects, width=width,
                  color=NAVY, label="Baseline", zorder=3)
        right.bar(right_positions, shared_objects, width=width,
                  color=TEAL, label="Shared components", zorder=3)
        right.set_yscale("log")
        right.set_ylim(100, 1_000_000)
        right.set_xlim(-0.55, 2.55)
        right.set_xticks(positions, ["Conway", r"Conway$^{\#2}$", r"Conway$^{\#3}$"])
        right.yaxis.set_major_locator(FixedLocator([100, 1000, 10_000, 100_000, 1_000_000]))
        right.yaxis.set_minor_locator(NullLocator())
        right.set_xlabel("Conway connected sums", labelpad=6)
        right.set_ylabel("Peak allocated objects", labelpad=6)
        right.set_title("B  Raw scanner", loc="left", pad=28)
        right.text(0, 1.035, "No geometric factorization",
                   transform=right.transAxes, fontsize=7.7, color=MUTED,
                   ha="left", va="bottom")
        right.legend(loc="upper left", borderaxespad=0.35, handlelength=1.35,
                     labelspacing=0.45)
        for locations, values in ((left_positions, baseline_objects),
                                  (right_positions, shared_objects)):
            for location, value in zip(locations, values):
                right.annotate(f"{value:,}", (location, value), xytext=(0, 4),
                               textcoords="offset points", ha="center", va="bottom",
                               fontsize=7.1, color=NAVY)

        output_dir.mkdir(parents=True, exist_ok=True)
        paths = [output_dir / "performance_summary.pdf",
                 output_dir / "performance_summary.png"]
        metadata = {"Title": "Unknot recognition: structural timing and raw scanner allocation",
                    "Author": "ProveIt research continuation",
                    "Subject": "Archived benchmark observations; no fitted asymptotic exponent",
                    "CreationDate": None, "ModDate": None}
        # Preserve the requested 6.5-inch canvas; avoid bbox='tight' resizing it.
        fig.savefig(paths[0], metadata=metadata)
        fig.savefig(paths[1], dpi=300)
        plt.close(fig)
    return paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--structural-data", type=Path,
                        default=HERE / "structural_benchmark_raw.json")
    parser.add_argument("--component-data", type=Path,
                        default=HERE / "component_benchmark.json")
    parser.add_argument("--output-dir", type=Path,
                        default=HERE.parent / "paper" / "figures")
    args = parser.parse_args()
    for path in draw(args.structural_data, args.component_data, args.output_dir):
        print(path)


if __name__ == "__main__":
    main()
