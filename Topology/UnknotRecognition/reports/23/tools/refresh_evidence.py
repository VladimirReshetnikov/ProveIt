#!/usr/bin/env python3
"""Regenerate article tables and its static plot from retained measured JSON."""
from __future__ import annotations

import json
from pathlib import Path
import statistics

ROOT = Path(__file__).resolve().parents[1]
ARTICLE = ROOT / "article"
TABLES = ARTICLE / "tables"


def read(relative):
    return json.loads((ROOT / relative).read_text())


def write_table(name, columns, header, rows):
    lines = [r"\begin{tabular}{@{}" + columns + r"@{}}", r"\toprule",
             " & ".join(header) + r" \\", r"\midrule"]
    lines.extend(" & ".join(row) + r" \\" for row in rows)
    lines.extend([r"\bottomrule", r"\end{tabular}"])
    (TABLES / name).write_text("\n".join(lines) + "\n")


def main():
    TABLES.mkdir(parents=True, exist_ok=True)
    validation = read("verification/integrated_validation.json")
    assert validation["status"] == "PASS"
    suite = next(r for r in validation["jobs"] if r["name"] == "full_suite")
    (TABLES / "validation_counts.tex").write_text(
        r"\newcommand{\FinalTestCount}{" + str(suite["test_count"]) + "}\n" +
        r"\newcommand{\FinalTestSeconds}{" + f'{suite["unittest_seconds"]:.3f}' + "}\n")

    graded = read("benchmarks/graded_transfer/paired_measurements.json")
    names = {"hard_unknot_8": "Hard unknot, 8 crossings", "conway": "Conway",
             "kinoshita_terasaka": "Kinoshita--Terasaka",
             "unknot_braid40": "Unknot braid, 40 crossings",
             "stress_braid5_36": "Stress braid, 36 crossings"}
    rows = []
    for record in graded["data"]:
        label = names[record["name"]] if "name" in record else f'Algebra: {record["objects"]} objects'
        rows.append([label, f'{record["median_seconds"]["baseline"]*1000:.3f}',
                     f'{record["baseline_over_transfer"]:.3f}',
                     f'{record["baseline_over_adaptive"]:.3f}', f'{record["aa_ratio"]:.3f}'])
    write_table("graded_benchmarks.tex", "lrrrr",
                ["Input", "Baseline (ms)", "Eager ratio", "Adaptive ratio", "A/A"], rows)

    tail = read("benchmarks/long_tail_benchmark.json")
    rows = []
    for record in tail["records"]:
        if record["magnitude"] != 801 or record["strands"] not in (4, 5):
            continue
        rows.append([str(record["strands"]), "+801" if record["sign"] == 1 else "$-801$",
                     f'{record["macro_stats"]["basis"]:,}', f'{record["cap_stats"]["basis"]:,}',
                     f'{record["median_paired_speedup"]:.2f}', f'{record["median_AA_ratio"]:.3f}'])
    write_table("tail_benchmarks.tex", "rrrrrr",
                ["Strands", "Exponent", "Original basis", "Cap basis", "Speedup", "A/A"], rows)

    structural = read("benchmarks/signed_run_structural_benchmark.json")
    rows = []
    for record in structural["records"]:
        rows.append([f'{record["magnitude"]:,}', f'{4*record["magnitude"]:,}',
                     f'{record["median_expanded_seconds"]*1000:.3f}',
                     f'{record["median_direct_seconds_per_call"]*1e6:.3f}',
                     f'{record["median_AA_ratio"]:.3f}'])
    write_table("structural_times.tex", "rrrrr",
                ["Magnitude", "Crossings", "Expanded (ms)", r"Direct ($\mu$s)", "A/A"], rows)
    (TABLES / "structural_benchmarks.tex").write_text(r"""
A focused interface benchmark uses this same four-run family with magnitudes
101, 1,001, and 10,001. Each arm starts with the identical already parsed run
tuple. The expanded arm includes letter expansion, fresh PD construction and
validation, and the maintained Seifert certificate; the direct arm evaluates
the signed-run certificate. The latter batches 100 fresh calls per sample.
Seven shuffled paired rounds include an expanded A/A arm. Every common
certificate field agrees, and all 2,100 direct certificates pass independent
verification outside the timers.
\begin{table}[htbp]
\centering\small
\input{tables/structural_times.tex}
\caption{Structural certificate evaluation from the same run input. Note the
different time units. These timings include the representation conversion
required by the expanded route and do not measure the full recognition portfolio.}
\label{tab:structural}
\end{table}
The direct call takes roughly five microseconds at these sizes while the
expanded route grows from about five to 484 milliseconds. The input has four
runs throughout; this measures the work avoided by the representation change.
The shared environment included a concurrent regression run, recorded in the
raw JSON. The exact timings and especially very large ratios should therefore
be read as interface measurements, not transferable hardware constants.
""".lstrip())

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import ScalarFormatter
    import numpy as np
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "axes.titleweight": "bold"})
    fig, axes = plt.subplots(1, 2, figsize=(10, 3.6), sharey=True)
    for axis, strands in zip(axes, (4, 5)):
        records = sorted((r for r in tail["records"] if r["strands"] == strands and r["sign"] == 1),
                         key=lambda r: r["magnitude"])
        magnitudes = [r["magnitude"] for r in records]
        for arm, label, color in (("macro", "Original macro", "#235789"),
                                  ("cap", "Finite cap", "#ba5a31")):
            samples = np.array([r["timings_seconds"][arm] for r in records])
            medians = np.median(samples, axis=1)
            q1, q3 = np.quantile(samples, (.25, .75), axis=1)
            axis.plot(magnitudes, medians, "o-", color=color, label=label, linewidth=2, markersize=5)
            axis.fill_between(magnitudes, q1, q3, color=color, alpha=.15, linewidth=0)
        axis.set_xscale("log")
        axis.set_yscale("log")
        axis.set_xticks(magnitudes)
        axis.xaxis.set_major_formatter(ScalarFormatter())
        axis.set_xlabel("Selected exponent magnitude")
        axis.set_title(f"{strands}-strand fixed context")
        axis.grid(True, which="major", color="#e1e5e9", linewidth=.7)
    axes[0].set_ylabel("Raw homology time (seconds)")
    axes[1].legend(frameon=False, loc="upper left")
    fig.tight_layout(pad=1.1)
    (ARTICLE / "figures").mkdir(exist_ok=True)
    fig.savefig(ARTICLE / "figures" / "tail_timings.png", dpi=240, facecolor="white")
    fig.savefig(ARTICLE / "figures" / "tail_timings.svg", facecolor="white",
                metadata={"Date": None})
    plt.close(fig)
    print("Regenerated article tables and tail timing figure from retained evidence.")


if __name__ == "__main__":
    main()
