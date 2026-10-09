#!/usr/bin/env python3
"""Regenerate report tables, CSVs and exact-count plots from saved evidence.

Default inputs are the package's reproduction snapshot and provenance.
The two override arguments are for assembling the original research package.
No algorithm benchmark is rerun and no raw observation is modified.
"""
import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
import statistics


ROOT = Path(__file__).resolve().parents[1]


def read(path):
    return json.loads(path.read_text())


def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def table(path, caption, label, spec, header, rows, note=""):
    content = [
        r"\begin{table}[tbp]", r"\centering", r"\small",
        r"\setlength{\tabcolsep}{4pt}",
        r"\caption{" + caption + "}",
        r"\label{" + label + "}",
        r"\begin{tabular}{@{}" + spec + r"@{}}",
        r"\toprule", header + r"\\", r"\midrule",
        *[row + r"\\" for row in rows],
        r"\bottomrule", r"\end{tabular}",
    ]
    if note:
        content += [r"\par\smallskip", r"\begin{minipage}{0.97\textwidth}",
                    r"\footnotesize " + note, r"\end{minipage}"]
    content += [r"\end{table}", ""]
    path.write_text("\n".join(content))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fast-source", type=Path, default=ROOT / "repro/fast")
    parser.add_argument("--provenance", type=Path, default=ROOT / "provenance")
    args = parser.parse_args()
    fast = args.fast_source
    out = ROOT / "article/tables"
    figures = ROOT / "article/figures"
    out.mkdir(parents=True, exist_ok=True)
    figures.mkdir(parents=True, exist_ok=True)
    geometric_path = fast / "commitment_research/results/benchmark.json"
    lp_path = fast / "lp_cache_research/summary.json"
    geometric = read(geometric_path)
    lp = read(lp_path)
    regression = read(args.provenance / "full_tests.json")
    grow = []
    for case in geometric["cases"]:
        p = case["regions"]
        expected_naive = sum(math.factorial(p) // math.factorial(p-j)
                             for j in range(p+1))
        samples = [s for s in case["samples"] if not s["warmup"]]
        assert len(samples) == 3
        for sample in samples:
            assert sample["stats"]["naive"]["nodes"] == expected_naive
            assert sample["stats"]["sleep"]["nodes"] == 2**p
        ratio = statistics.median(s["paired_speedup"] for s in samples)
        assert ratio == case["median_paired_speedup"]
        grow.append(dict(
            regions=p, tetrahedra=case["tetrahedra"],
            naive_nodes=expected_naive, sleep_nodes=2**p,
            naive_median_seconds=case["median_naive_ns"]/1e9,
            sleep_median_seconds=case["median_sleep_ns"]/1e9,
            median_paired_speedup=ratio,
        ))
    write_csv(out / "geometric_benchmark.csv", grow)
    table(
        out / "geometric_benchmark.tex",
        "Genuine independent-collapse controls. Times are medians in "
        "milliseconds; the final column is the median within-pair ratio.",
        "tab:geometric", "rrrrrrr",
        r"$p$ & $t$ & $N_{\rm naive}$ & $N_{\rm sleep}$ & "
        r"Naive (ms) & Sleep (ms) & Paired ratio",
        [f"{r['regions']} & {r['tetrahedra']} & {r['naive_nodes']:,} & "
         f"{r['sleep_nodes']:,} & {1000*r['naive_median_seconds']:,.3f} & "
         f"{1000*r['sleep_median_seconds']:,.3f} & "
         f"{r['median_paired_speedup']:.3f}" for r in grow],
        "One warm-up pair is excluded. Three measured pairs per size; "
        "seeded randomized arm order. Full sources and certificates are saved."
    )
    lrows = []
    display = {
        "layered_1": "Layered, 1 tet.",
        "layered_2": "Layered, 2 tet.",
        "layered_4": "Layered, 4 tet.",
        "layered_6": "Layered, 6 tet.",
        "layered_8": "Layered, 8 tet.",
        "branching_torus": "Branching torus",
        "finite_trefoil": "Finite trefoil",
        "frozen_figure-eight": "Figure-eight, frozen",
        "frozen_figure-eight-relabeled": "Figure-eight, relabelled",
        "native_figure_eight_regenerated": "Figure-eight, native",
    }
    for r in lp["results"]:
        lrows.append({
            "name": r["name"], "kind": r["kind"],
            "baseline_status": r["baseline_status"],
            "screened_status": r["screened_status"],
            "baseline_lp_calls": r["baseline_lp_calls"],
            "screened_lp_calls": r["screened_lp_calls"],
            "baseline_lp_pivots": r["baseline_lp_pivots"],
            "screened_lp_pivots": r["screened_lp_pivots"],
            "baseline_median_seconds": r["median_seconds"]["baseline"],
            "screened_median_seconds": r["median_seconds"]["screened"],
            "ratio_of_median_times": r["median_speedup"],
            "local_hits": r["local_hits"],
            "antichain_hits": r["antichain_hits"],
            "complete_certificates_equal": r["complete_certificates_equal"],
        })
    write_csv(out / "lp_benchmark.csv", lrows)
    genuine = [r for r in lrows if r["kind"] == "genuine_triangulation"]
    status = {"POSITIVE_EULER": "+", "NO_POSITIVE_EULER": "0",
              "INCONCLUSIVE": "cap"}
    table(
        out / "lp_genuine.tex",
        "Exact LP screening on genuine triangulations. Each paired entry "
        "is baseline/screened; times are seconds.",
        "tab:lp-genuine", "lrrrrl",
        r"Source & LP calls & Pivots & Median seconds & Ratio & Result",
        [f"{display[r['name']]} & "
         f"{r['baseline_lp_calls']}/{r['screened_lp_calls']} & "
         f"{r['baseline_lp_pivots']:,}/{r['screened_lp_pivots']:,} & "
         f"{r['baseline_median_seconds']:.3f}/"
         f"{r['screened_median_seconds']:.3f} & "
         f"{r['ratio_of_median_times']:.3f} & "
         f"{status[r['baseline_status']]}" for r in genuine],
        r"$+$: completed positive-Euler query; $0$: completed negative "
        r"positive-Euler query; cap: inconclusive at 600 pivots. "
        "Three alternating-order pairs per case; ratio of arm medians. "
        "The result concerns the stated surface query, not an unauthenticated "
        "knot-diagram verdict."
    )
    algebraic = [r for r in lrows if r["kind"] == "algebraic_cone"]
    for r in algebraic:
        s = int(r["name"].rsplit("_", 1)[1])
        r["parameter"] = s
        assert r["baseline_lp_calls"] == 3*s*s + 2*s + 1
        assert r["screened_lp_calls"] == 2*s + 1
        assert r["baseline_lp_pivots"] == 6*s**3 + 3*s*s + s
        assert r["screened_lp_pivots"] == 3*s*s + s
    table(
        out / "lp_algebraic.tex",
        "Algebraic controls, with no asserted triangulation realization. "
        "Every call and pivot total agrees with the proved formula.",
        "tab:lp-algebraic", "rrrrr",
        r"$s$ & LP calls (base/screen) & Pivots (base/screen) & "
        r"Median seconds & Ratio",
        [f"{r['parameter']} & {r['baseline_lp_calls']}/"
         f"{r['screened_lp_calls']} & {r['baseline_lp_pivots']:,}/"
         f"{r['screened_lp_pivots']:,} & "
         f"{r['baseline_median_seconds']:.3f}/"
         f"{r['screened_median_seconds']:.3f} & "
         f"{r['ratio_of_median_times']:.3f}" for r in algebraic],
        "Both producers complete with the same substituted algebraic "
        "certificate. Ratios are baseline median divided by screened median."
    )
    assert regression["status"] == "PASSED"
    assert regression["zero_module_omissions"]
    assert regression["final_source_hashes_match_each_selected_batch"]
    assert regression["tests_run"] == regression["tests_loaded"]
    table(
        out / "regression_gate.tex",
        "Complete final regression gate. Each test module belongs to one "
        "selected passing batch.",
        "tab:regression", "rrrrl",
        r"Batch & Modules & Tests & Seconds & Result",
        [f"{b['batch']} & {len(b['modules'])} & {b['tests_run']:,} & "
         f"{b['elapsed_seconds']:.3f} & PASS"
         for b in regression["batches"]] +
        [r"\midrule " + f"Total & {regression['total_modules']} & "
         f"{regression['tests_run']:,} & "
         f"{regression['sum_of_passing_batch_elapsed_seconds']:.3f} & PASS"],
        "Zero failures, errors or skips in the final selected batches; "
        "zero module omissions. The preliminary interrupted run and the "
        "corrected native-fixture test failure are preserved separately."
    )
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 9,
        "axes.titlesize": 10, "axes.labelsize": 9,
        "axes.spines.top": False, "axes.spines.right": False,
        "pdf.fonttype": 42, "ps.fonttype": 42,
    })
    fig, axes = plt.subplots(1, 2, figsize=(6.8, 3.35), layout="constrained")
    orange, teal = "#B55D28", "#087E8B"
    ax = axes[0]
    ax.plot([r["regions"] for r in grow], [r["naive_nodes"] for r in grow],
            "o-", color=orange, label="Naive traces", linewidth=1.7)
    ax.plot([r["regions"] for r in grow], [r["sleep_nodes"] for r in grow],
            "s-", color=teal, label="Sleep sets", linewidth=1.7)
    ax.set(title="Genuine solid-torus controls",
           xlabel="Independent regions p", ylabel="Visited trace nodes",
           yscale="log")
    ax.set_xticks([r["regions"] for r in grow])
    ax.legend(frameon=False, loc="upper left", fontsize=8)
    ax = axes[1]
    ax.plot([r["parameter"] for r in algebraic],
            [r["baseline_lp_pivots"] for r in algebraic],
            "o-", color=orange, label="Baseline pivots", linewidth=1.7)
    ax.plot([r["parameter"] for r in algebraic],
            [r["screened_lp_pivots"] for r in algebraic],
            "s-", color=teal, label="Screened pivots", linewidth=1.7)
    ax.set(title="Declared algebraic LP controls",
           xlabel="Family parameter s", ylabel="Total simplex pivots",
           yscale="log")
    ax.set_xticks([r["parameter"] for r in algebraic])
    ax.legend(frameon=False, loc="upper left", fontsize=8)
    for ax in axes:
        ax.grid(axis="y", which="major", alpha=.2)
        ax.margins(x=.07, y=.18)
    fig.savefig(figures / "performance.pdf")
    fig.savefig(figures / "performance.png", dpi=200)
    plt.close(fig)
    summary = {
        "geometric_cases": len(grow),
        "lp_cases": len(lrows),
        "genuine_lp_cases": len(genuine),
        "algebraic_lp_cases": len(algebraic),
        "all_control_formulas_checked": True,
        "regression_modules": regression["total_modules"],
        "regression_tests": regression["tests_run"],
        "inputs": {
            str(path.relative_to(fast)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [geometric_path, lp_path]
        },
    }
    (out / "evidence_summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
