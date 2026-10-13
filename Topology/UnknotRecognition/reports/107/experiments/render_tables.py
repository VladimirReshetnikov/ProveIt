"""Regenerate manuscript tables from the retained exact-audit and timing records."""
from __future__ import annotations

import json
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    article = root / "article"
    benchmark = json.loads((root / "results/benchmark.json").read_text())
    records = {record["name"]: record for record in benchmark["records"]}
    selected = [
        ("unique_late_q1", r"Unique last, $q=1$"),
        ("unique_late_q4", r"Unique last, $q=4$"),
        ("unique_late_q8", r"Unique last, $q=8$"),
        ("unique_late_q12", r"Unique last, $q=12$"),
        ("easy_first_q12", r"Easy first, $q=12$"),
        ("obstructed_q12", r"Obstructed, $q=12$"),
        ("repository_loop_matrix", "Repository loop matrix"),
    ]
    lines = [
        r"\begin{table}[htbp]\centering\small",
        r"\begin{tabular}{lrrrr}\toprule",
        r"Input & Selector (ms) & Trees (ms) & Ratio & A/A\\\midrule",
    ]
    for key, label in selected:
        rec = records[key]
        lines.append(
            f"{label} & {1000*rec['selector_median_s']:.3f} & "
            f"{1000*rec['enumeration_median_s']:.3f} & "
            f"{rec['median_paired_ratio']:.3f} & {rec['aa_median_ratio']:.3f}"
            + r"\\"
        )
    lines += [
        r"\bottomrule\end{tabular}",
        r"\caption{Matrix-stage medians and paired ratios, not native recognition timings. The loop row uses the general FPT kernel; the star rows use the polynomial pair-column kernel. A/A compares two identical selector executions.}",
        r"\end{table}",
    ]
    (article / "benchmark_table.tex").write_text("\n".join(lines) + "\n")
    macros = {
        "UniqueLastRatio": f"{records['unique_late_q12']['median_paired_ratio']:.0f}",
        "ObstructedRatio": f"{records['obstructed_q12']['median_paired_ratio']:.0f}",
        "EasyFirstRatio": f"{records['easy_first_q12']['median_paired_ratio']:.3f}",
        "LoopRatio": f"{records['repository_loop_matrix']['median_paired_ratio']:.4f}",
        "LoopSlowdown": f"{1/records['repository_loop_matrix']['median_paired_ratio']:.1f}",
    }
    (article / "measurements.tex").write_text(
        "% Generated from results/benchmark.json; see experiments/render_tables.py.\n"
        + "\n".join("\\newcommand{\\" + key + "}{" + value + "}" for key, value in macros.items())
        + "\n"
    )
    validation = json.loads((root / "results/validation.json").read_text())
    stages = validation["stages"]
    if validation["mismatches"] != 0:
        raise ValueError("The manuscript table requires a zero-mismatch audit.")
    stage_labels = [
        ("exhaustive_three_rows_two_columns_all_rooted_two_vertex_multigraphs",
         "All three-row, two-column ternary matrices on all connected two-vertex dual multigraphs"),
        ("exhaustive_ternary_three_by_three_fixed_loop_graph",
         r"All ternary $3\times3$ matrices on the loop graph"),
        ("random_mixed_up_to_ten_rows_exceptional_boundary_at_most_four",
         r"Mixed random matrices, $m\le10$, $b\le4$"),
        ("random_five_by_five_unrestricted", r"Unrestricted random $5\times5$ matrices"),
        ("independent_transversal_assignment_comparisons", "Matroid solver versus assignment enumeration"),
        ("pair_optimal_defect_and_all_seed_sets", "Pair-column optimal deficits"),
        ("inherited_peeling_vs_all_positive_pivot_orders", "Peeling versus all positive-pivot orders"),
    ]
    lines = [
        r"\begin{table}[htbp]\centering\small",
        r"\begin{tabular}{p{3.7in}rr}\toprule",
        r"Audit & Inputs & Mismatches\\\midrule",
    ]
    for key, label in stage_labels:
        lines.append(f"{label} & {stages[key]['instances']:,} & 0" + r"\\")
    seed_sets = stages["pair_optimal_defect_and_all_seed_sets"]["seed_sets"]
    lines += [
        r"\bottomrule\end{tabular}",
        r"\caption{Executed finite audits. The pair-column stage also checks all "
        + f"{seed_sets:,}" + r" seed subsets of its 500 inputs. Counts in different stages are different comparison tasks, not a single disjoint population.}",
        r"\end{table}",
    ]
    (article / "validation_table.tex").write_text("\n".join(lines) + "\n")
    print("Refreshed validation_table.tex, benchmark_table.tex, and measurements.tex.")


if __name__ == "__main__":
    main()
