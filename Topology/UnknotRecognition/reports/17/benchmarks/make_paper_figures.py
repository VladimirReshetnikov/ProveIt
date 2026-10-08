"""Rebuild vector figures, raster previews, and compact benchmark tables.

python make_paper_figures.py --paper-dir /path/to/paper \
    --kernel-data /path/to/potts_benchmark.json \
    --pipeline-data /path/to/pipeline_benchmark.json

All plotted ratios and intervals are recomputed from the recorded raw
rounds and checked against their stored summaries before rendering.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import statistics

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import FixedLocator, FuncFormatter, LogLocator, NullFormatter


BLUE = "#245D85"
ORANGE = "#B96335"
INK = "#25323A"
GRAY = "#71808A"


def median_interval(values):
    ordered = sorted(values)
    count = len(ordered)
    tail, rank = 0.0, 0
    for candidate in range(1, (count + 1) // 2 + 1):
        tail += math.comb(count, candidate - 1) / 2 ** count
        if tail <= .025:
            rank = candidate
        else:
            break
    return [ordered[rank - 1], ordered[count - rank]] if rank else [ordered[0], ordered[-1]]


def quantile(values, fraction):
    values = sorted(values)
    position = (len(values) - 1) * fraction
    left = int(position)
    right = min(left + 1, len(values) - 1)
    return values[left] + (position - left) * (values[right] - values[left])


def checked_comparison(case, arm, pipeline=False):
    values = [sample["ns"]["matching_A1"] / sample["ns"][arm]
              for sample in case["samples"]]
    aa = [sample["ns"]["matching_A1"] / sample["ns"]["matching_A2"]
          for sample in case["samples"]]
    median, interval = statistics.median(values), median_interval(values)
    recorded = case["comparisons"][arm]
    assert math.isclose(median, recorded["median_matching_over_arm"], rel_tol=1e-13)
    for actual, expected in zip(interval, recorded["median_ratio_interval_at_least_95pct"]):
        assert math.isclose(actual, expected, rel_tol=1e-13)
    claim = "no_clear_timing_claim"
    if (pipeline and not case["backend_exercised"][arm]
            and not case["backend_exercised"]["matching_A1"]):
        claim = "backend_bypassed_no_backend_speed_claim"
    elif interval[0] > 1 and median > quantile(aa, .75):
        claim = "faster_on_this_input"
    elif interval[1] < 1 and median < quantile(aa, .25):
        claim = "slower_on_this_input"
    assert claim == recorded["claim"]
    return dict(median=median, low=interval[0], high=interval[1], claim=claim)


def display_name(name):
    names = {"conway": "Conway", "conway_sum_2": "Conway #2",
             "conway_sum_3": "Conway #3", "conway_sum_8": "Conway #8",
             "figure_eight": "Figure-eight", "grid_determinant_one_knot": "Grid determinant one",
             "grid_scrambled_unknot": "Grid scrambled unknot", "hard_unknot_8": "Hard unknot (8)",
             "kinoshita_terasaka": "Kinoshita–Terasaka", "stress_braid5_36": "5-strand stress (36)",
             "torus_3_5": "$T(3,5)$", "trefoil": "Trefoil", "unknot": "Crossing-free unknot",
             "unknot_braid40": "Unknot braid (40)"}
    if name.startswith("random_order_"):
        return "Random order " + name.rsplit("_", 1)[1]
    if name.startswith("weaving_W3_"):
        return "$W(3," + name.rsplit("_", 1)[1] + ")$"
    return names[name]


def tex_name(name):
    names = {"conway": "Conway", "kinoshita_terasaka": "Kinoshita--Terasaka",
             "conway_sum_2": r"Conway \#2", "conway_sum_3": r"Conway \#3",
             "conway_sum_8": r"Conway \#8"}
    if name.startswith("random_order_"):
        return "Random " + name.rsplit("_", 1)[1]
    return names[name]


def save_figure(fig, directory, name, title):
    fig.savefig(directory / (name + ".pdf"), facecolor="white", metadata={
        "Title": title, "Author": "ProveIt research continuation",
        "Creator": "make_paper_figures.py / Matplotlib", "CreationDate": None, "ModDate": None})
    fig.savefig(directory / (name + ".png"), facecolor="white", dpi=300,
                metadata={"Title": title, "Software": "make_paper_figures.py / Matplotlib"})
    plt.close(fig)


def ratio_figure(cases, values, directory):
    fig, ax = plt.subplots(figsize=(6.5, 8.05))
    fig.subplots_adjust(left=.30, right=.977, top=.897, bottom=.14)
    fig.text(.03, .979, "Paired filter-kernel timings", fontsize=12.3, weight="semibold", color=INK)
    fig.text(.03, .949, "All 29 inputs · 15 rounds · supplied crossing orders", fontsize=8.7, color=GRAY)
    for row in range(len(cases)):
        if row % 2 == 0:
            ax.axhspan(row - .5, row + .5, color="#F3F5F7", zorder=0)
    for boundary in (13.5, 25.5):
        ax.axhline(boundary, color="#ADB7BE", linewidth=.7, zorder=1)
    ax.axvline(1, color=INK, linewidth=1.05, zorder=2)
    for index, case in enumerate(cases):
        for arm, offset, color, marker in (("exact_q6", -.145, BLUE, "o"),
                                            ("factored_exact_q6", .145, ORANGE, "s")):
            value = values[case["name"]][arm]
            supported = value["claim"] in ("faster_on_this_input", "slower_on_this_input")
            ax.errorbar(value["median"], index + offset,
                        xerr=[[value["median"] - value["low"]], [value["high"] - value["median"]]],
                        fmt=marker, markersize=4.0, color=color,
                        markerfacecolor=color if supported else "white",
                        markeredgecolor=color, markeredgewidth=.9,
                        elinewidth=1.0 if supported else .75, capsize=1.5,
                        alpha=1 if supported else .62, zorder=4)
    ax.set_xscale("log")
    ax.set_xlim(.06, 18)
    ax.set_ylim(len(cases) - .45, -.75)
    ax.set_yticks(range(len(cases)), [display_name(case["name"]) for case in cases])
    ax.tick_params(axis="y", length=0, pad=8, labelsize=8.3)
    ax.xaxis.set_major_locator(FixedLocator([.1, .2, .5, 1, 2, 5, 10]))
    ax.xaxis.set_major_formatter(FuncFormatter(lambda value, position: f"{value:g}"))
    ax.xaxis.set_minor_locator(LogLocator(base=10, subs=range(2, 10)))
    ax.xaxis.set_minor_formatter(NullFormatter())
    ax.tick_params(axis="x", which="major", length=3, color=GRAY, labelsize=8.5)
    ax.tick_params(axis="x", which="minor", length=0)
    ax.grid(axis="x", which="major", color="#D9DFE4", linewidth=.55, zorder=0)
    ax.set_xlabel("Matching time / backend time", fontsize=9.3, labelpad=9)
    for spine in ax.spines.values():
        spine.set_visible(False)
    handles = [Line2D([], [], marker="o", color=BLUE, linestyle="", markersize=5,
                      label=r"Exact $q=6$"),
               Line2D([], [], marker="s", color=ORANGE, linestyle="", markersize=5,
                      label=r"Factored exact $q=6$")]
    fig.legend(handles=handles, loc="upper right", bbox_to_anchor=(.977, .946),
               ncol=2, frameon=False, fontsize=8.5, columnspacing=1.5, handletextpad=.4)
    fig.text(.03, .043, "Filled: interval + A/A rule met; hollow: no clear claim. Bars: nominal pointwise intervals.",
             fontsize=7.6, color=INK)
    fig.text(.03, .020, "Matching uses the q=5 point; exact backends use q=6. Ratios above 1 favor Potts.",
             fontsize=7.6, color=GRAY)
    save_figure(fig, directory, "kernel_ratios", "All 29 paired Jones filter-kernel timing comparisons")


def resource_figure(cases, directory):
    selected = [case for case in cases if case["name"].startswith("random_order_")]
    assert len(selected) == 12
    fig, axes = plt.subplots(2, 1, figsize=(6.5, 5.2), sharex=True)
    fig.subplots_adjust(left=.115, right=.978, top=.83, bottom=.105, hspace=.40)
    fig.text(.03, .975, "Resources across the random-order controls", fontsize=12.0,
             weight="semibold", color=INK)
    fig.text(.03, .935, "Exact six-color arithmetic · all 12 accepted controls from seed 764259",
             fontsize=8.6, color=GRAY)
    handles = [Line2D([], [], marker="o", color=BLUE, linestyle="", markersize=5,
                      label=r"Exact $q=6$"),
               Line2D([], [], marker="s", color=ORANGE, linestyle="", markersize=5,
                      label=r"Factored exact $q=6$")]
    fig.legend(handles=handles, loc="upper right", bbox_to_anchor=(.98, .905), ncol=2,
               frameon=False, fontsize=8.5, handletextpad=.4, columnspacing=1.5)
    specifications = [("peak_states", "(a) Peak represented keys", "Keys", (8, 12000)),
                      ("transitions", "(b) Transfer updates", "Transitions", (65, 70000))]
    for ax, (field, title, ylabel, limits) in zip(axes, specifications):
        for index, case in enumerate(selected):
            global_value = case["counters"]["exact_q6"][field]
            factor_value = case["counters"]["factored_exact_q6"][field]
            ax.plot([index - .10, index + .10], [global_value, factor_value],
                     color="#A3ADB5", linewidth=1, zorder=2)
            ax.plot(index - .10, global_value, marker="o", color=BLUE, markersize=5, zorder=3)
            ax.plot(index + .10, factor_value, marker="s", color=ORANGE, markersize=4.6, zorder=3)
        ax.set_yscale("log")
        ax.set_ylim(*limits)
        ax.set_xlim(-.55, 11.55)
        ax.set_title(title, loc="left", fontsize=9.2, color=INK, pad=7)
        ax.set_ylabel(ylabel, fontsize=9, color=INK)
        ax.yaxis.set_major_locator(LogLocator(base=10, numticks=5))
        ax.yaxis.set_minor_locator(LogLocator(base=10, subs=(2, 5)))
        ax.yaxis.set_minor_formatter(NullFormatter())
        ax.yaxis.set_major_formatter(FuncFormatter(lambda v, p: f"{v:,.0f}" if v >= 1 else f"{v:g}"))
        ax.grid(axis="y", which="major", color="#D9DFE4", linewidth=.6, zorder=0)
        ax.grid(axis="y", which="minor", color="#EDF0F3", linewidth=.45, zorder=0)
        ax.tick_params(axis="both", labelsize=8.5, color=GRAY, length=2.5)
        ax.tick_params(axis="y", which="minor", length=0)
        for side in ("top", "right", "left"):
            ax.spines[side].set_visible(False)
        ax.spines["bottom"].set_color("#AEB9C1")
    axes[0].annotate("4,111 → 205", xy=(4, 4111), xytext=(4.9, 7300), fontsize=8.0,
                     color=INK, ha="center", arrowprops=dict(arrowstyle="-", color=GRAY, lw=.6))
    axes[1].annotate("30,197 → 1,558", xy=(4, 30197), xytext=(5.4, 49000), fontsize=8.0,
                     color=INK, ha="center", arrowprops=dict(arrowstyle="-", color=GRAY, lw=.6))
    axes[-1].set_xticks(range(12), [f"{i:02}" for i in range(1, 13)])
    axes[-1].set_xlabel("Random-order control", fontsize=9.2, labelpad=8)
    save_figure(fig, directory, "component_resources", "Exact and factored Potts resource counts for all random-order controls")


def format_ratio(value):
    text = f"{value['median']:.3f}"
    if value["claim"] in ("faster_on_this_input", "slower_on_this_input"):
        return "$" + text + r"^{\dagger}$"
    return text


def write_tables(kernel, pipeline, values, directory):
    by_name = {case["name"]: case for case in kernel["cases"]}
    names = ("conway", "kinoshita_terasaka", "conway_sum_8", "random_order_04",
             "random_order_05", "random_order_11")
    lines = [r"% Generated by make_paper_figures.py; do not edit values by hand.",
             r"\begin{table}[htbp]", r"\centering", r"\footnotesize",
             r"\setlength{\tabcolsep}{3.5pt}",
             r"\begin{tabular*}{\linewidth}{@{\extracolsep{\fill}}lrrrrrrrr@{}}",
             r"\toprule", r"Input & $n$ & $w$ & $f$ & $g$ & $K_E$ & $K_F$ & $T_M/T_E$ & $T_M/T_F$ \\",
             r"\midrule"]
    table_values = []
    for name in names:
        case = by_name[name]
        exact = case["counters"]["exact_q6"]
        factor = case["counters"]["factored_exact_q6"]
        row = [tex_name(name), str(case["crossings"]), str(case["boundary_profile"][0]),
               str(exact["max_spin_frontier"]), str(factor["max_component_frontier"]),
               f"{exact['peak_states']:,}", f"{factor['peak_states']:,}",
               format_ratio(values[name]["exact_q6"]), format_ratio(values[name]["factored_exact_q6"])]
        lines.append(" & ".join(row) + r" \\")
        table_values.append(dict(name=name, cells=row))
    lines += [r"\bottomrule", r"\end{tabular*}", r"\par\smallskip",
              r"\begin{minipage}{\linewidth}\scriptsize",
              r"$M$: matching kernel at the five-color evaluation point; $E$: exact $q=6$;",
              r"$F$: factored exact $q=6$. $K_E,K_F$ count peak represented keys; $K_F$",
              r"sums represented component tables. $f$ is the full active spin frontier",
              r"and $g$ the largest active frontier of one processed component.",
              r"Ratios are paired medians; values above one favor the denominator.",
              r"$\dagger$ marks a comparison meeting both the pointwise interval and A/A rule.",
              r"\end{minipage}",
              r"\caption{Selected supplied-order kernel results. The companion CSV retains all 29 cases, including every measured regression.}",
              r"\label{tab:kernel-selected}", r"\end{table}"]
    (directory / "kernel_selected.tex").write_text("\n".join(lines) + "\n")

    cases = [case for case in pipeline["cases"] if case["backend_exercised"]["matching_A1"]]
    assert len(cases) == 5
    lines = [r"% Generated by make_paper_figures.py; do not edit values by hand.",
             r"\begin{table}[htbp]", r"\centering", r"\footnotesize",
             r"\setlength{\tabcolsep}{3.5pt}",
             r"\begin{tabular*}{\linewidth}{@{\extracolsep{\fill}}lrccc@{}}",
             r"\toprule", r"Input & $n$ & $T_M/T_E$ [interval] & $T_M/T_F$ [interval] & Supported claim \\",
             r"\midrule"]
    pipeline_values = []
    for case in cases:
        ratios = []
        for arm in ("exact_q6", "factored_exact_q6"):
            value = checked_comparison(case, arm, pipeline=True)
            assert value["claim"] == "no_clear_timing_claim"
            ratios.append(f"{value['median']:.3f} [{value['low']:.3f}, {value['high']:.3f}]")
        row = [tex_name(case["name"]), str(case["warmup_results"]["matching_A1"]["input_crossings"]),
               *ratios, "None"]
        lines.append(" & ".join(row) + r" \\")
        pipeline_values.append(dict(name=case["name"], cells=row))
    lines += [r"\bottomrule", r"\end{tabular*}", r"\par\smallskip",
              r"\begin{minipage}{\linewidth}\scriptsize",
              r"$M$: the normal pipeline with its native generic matching evaluation;",
              r"$E,F$: the normal pipeline with exact or factored exact $q=6$.",
              r"Nominal pointwise intervals; see the experimental-design assumptions in the text.",
              r"All five inputs reached Jones evaluation; the other twelve inputs bypassed it.",
              r"No comparison in this seven-round pipeline run met the timing-claim rule.",
              r"\end{minipage}",
              r"\caption{The five normal-pipeline cases that exercised the selected Jones backend. Timings include input parsing, checked diagram conversion, recognition, and JSON output encoding in a hot process.}",
              r"\label{tab:pipeline-selected}", r"\end{table}"]
    (directory / "pipeline_selected.tex").write_text("\n".join(lines) + "\n")
    return table_values, pipeline_values


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--paper-dir", type=Path, required=True)
    parser.add_argument("--kernel-data", type=Path,
                        default=Path(__file__).resolve().parent / "potts_benchmark.json")
    parser.add_argument("--pipeline-data", type=Path,
                        default=Path(__file__).resolve().parent / "pipeline_benchmark.json")
    args = parser.parse_args()
    kernel = json.loads(args.kernel_data.read_text())
    pipeline = json.loads(args.pipeline_data.read_text())
    assert kernel["complete"] and pipeline["complete"]
    assert len(kernel["cases"]) == 29 and len(pipeline["cases"]) == 17
    assert kernel["total_timed_calls"] == 3045 and pipeline["total_timed_calls"] == 476
    values = {}
    for case in kernel["cases"]:
        values[case["name"]] = {arm: checked_comparison(case, arm)
                                for arm in ("exact_q6", "factored_exact_q6")}
        exact, factor = case["counters"]["exact_q6"], case["counters"]["factored_exact_q6"]
        assert exact["partition_function"] == factor["partition_function"]
        assert factor["max_component_frontier"] <= exact["max_spin_frontier"]
        assert 2 * exact["max_spin_frontier"] <= case["boundary_profile"][0]
        for result in (exact, factor):
            for field in ("peak_states", "transitions"):
                assert type(result[field]) is int and result[field] >= 0
    for case in pipeline["cases"]:
        for arm in ("exact_q6", "factored_exact_q6"):
            checked_comparison(case, arm, pipeline=True)
    figures = args.paper_dir / "figures"
    generated = args.paper_dir / "sections" / "generated"
    figures.mkdir(parents=True, exist_ok=True)
    generated.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9,
                         "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK,
                         "pdf.fonttype": 42, "ps.fonttype": 42,
                         "mathtext.fontset": "dejavusans", "savefig.bbox": None})
    ratio_figure(kernel["cases"], values, figures)
    resource_figure(kernel["cases"], figures)
    table, pipeline_table = write_tables(kernel, pipeline, values, generated)
    paths = [figures / name for name in ("kernel_ratios.pdf", "kernel_ratios.png",
                                         "component_resources.pdf", "component_resources.png")]
    paths += [generated / name for name in ("kernel_selected.tex", "pipeline_selected.tex")]
    validation = dict(kernel_source_sha256=hashlib.sha256(args.kernel_data.read_bytes()).hexdigest(),
                      pipeline_source_sha256=hashlib.sha256(args.pipeline_data.read_bytes()).hexdigest(),
                      matplotlib=matplotlib.__version__, kernel_cases=29, plotted_estimates=58,
                      random_resource_cases=12, kernel_ratio_values=values,
                      kernel_table=table, pipeline_table=pipeline_table,
                      all_ratios_intervals_and_claim_markers_recomputed=True,
                      exact_partition_functions_agree=True,
                      output_sha256={str(path.relative_to(args.paper_dir)):
                                     hashlib.sha256(path.read_bytes()).hexdigest() for path in paths})
    (figures / "figure_data_validation.json").write_text(json.dumps(validation, indent=2) + "\n")
    print("Rendered two vector PDFs, two 300-dpi PNGs, and two compact TeX tables.")
    print("Validated all 58 plotted ratios/intervals/claim markers and all 34 pipeline comparisons.")


if __name__ == "__main__":
    main()
