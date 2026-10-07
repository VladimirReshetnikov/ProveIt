"""Regenerate the article's measured table and portable CSV summaries.

Example, from the dated research directory in the integration bundle:
  python3 summarize_results.py --results ../../fast/results --output-dir . \
      --article unknot_recognition_progress.tex

Only Python's standard library is required. This does not rerun experiments.
"""
from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path


def label(case):
    name = case["name"]
    if case["family"] in ("positive", "alternating"):
        return case["family"].capitalize() + r" three-braid, \(r=" + name.rsplit("_", 1)[1] + r"\)"
    if case["family"] == "scrambled_unknot":
        suffix = "" if case["options"]["use_r3"] else " (R3 off)"
        return "Scrambled unknot, seed " + str(case["seed"]) + suffix
    return {
        "morton_four_braid_unknot": "Morton's four-braid unknot",
        "stabilized_unknot_16_strands": "Stabilized unknot, 16 strands",
        "stabilized_unknot_64_strands": "Stabilized unknot, 64 strands",
        "stabilized_unknot_256_strands": "Stabilized unknot, 256 strands",
        "conway": "Conway",
        "kinoshita_terasaka": "Kinoshita--Terasaka",
        "hard_unknot_8": "Eight-crossing unknot (braid)",
        "grid_scrambled_unknot": "Grid unknot",
    }[name]


def write_csv(path, rows):
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--article", type=Path)
    args = parser.parse_args()
    benchmark = json.loads((args.results / "braid_benchmark.json").read_text())
    residue = json.loads((args.results / "residue_profiles.json").read_text())
    args.output_dir.mkdir(parents=True, exist_ok=True)
    paired = []
    lines = []
    for case in benchmark["cases"]:
        comparison = case["paired_comparison"]
        old_ms = 1000 * case["baseline"]["total_seconds"]["median"]
        new_ms = 1000 * case["new"]["total_seconds"]["median"]
        n = case["new"]["samples"][0]["input_crossings"]
        verdict = comparison["comparison_rule_result"]
        paired.append({
            "case": case["name"], "family": case["family"], "crossings": n,
            "use_r3": case["options"].get("use_r3", True),
            "baseline_median_ms": old_ms, "new_median_ms": new_ms,
            "median_paired_speedup": comparison["median_speedup"],
            "new_over_old_ci_lower": comparison["ci95_median_new_over_old"][0],
            "new_over_old_ci_upper": comparison["ci95_median_new_over_old"][1],
            "aa_lower_quartile": comparison["aa_quartiles"][0],
            "aa_upper_quartile": comparison["aa_quartiles"][1],
            "comparison_rule_result": verdict,
            "new_methods": ";".join(case["new"]["methods"]),
        })
        short = {"measured faster": "Faster", "measured slower": "Slower",
                 "no timing claim": "None"}[verdict]
        lines.append(f"{label(case)} & {n} & {old_ms:.3f} & {new_ms:.3f} & "
                     + f"{comparison['median_speedup']:.2f}" + r"\(\times\) & " + short + r" \\")
    write_csv(args.output_dir / "paired_timings.csv", paired)
    raw = []
    for row in benchmark["raw_scaling"]:
        raw.append({"letters": row["letters"], "backend": row["backend"],
                    "median_seconds": row["median_seconds"],
                    "token_operations": row.get("stats", {}).get("token_operations", ""),
                    "cyclic_tokens": row.get("stats", {}).get("cyclic_tokens", ""),
                    "largest_final_matrix_entry_bits": row.get("max_entry_bits", "")})
    write_csv(args.output_dir / "raw_word_scaling.csv", raw)
    profiles = []
    for case in residue["cases"]:
        for run in case["runs"]:
            profiles.append({"case": case["name"], "crossings": case["crossings"],
                             "configuration": run["configuration"],
                             "peak_boundary_points": run["peak_boundary_points"],
                             "peak_objects_before": run["peak_objects_before"],
                             "peak_canonical_objects": run["peak_canonical_objects"],
                             "compositions": run["stats"]["compositions"],
                             "final_unreduced_rank": run["final_unreduced_rank"]})
    write_csv(args.output_dir / "residue_profile_summary.csv", profiles)
    table = r"""The final run used CPython 3.12.14 on x86\_64 Linux, with 15 paired
rounds per case and a rotating three-arm order: baseline, new, and a
second baseline call. Each implementation had one warm-up. The timed
region includes fresh PD construction and recognition; it excludes
process startup, imports, and JSON decoding. All published samples
finished with the expected exact verdict.

The comparison rule uses an order-statistic interval with at least 95\%
coverage for the median new/old ratio under independent sampling. It
labels a case faster only when the interval lies below one and the
median ratio is below the first quartile of the paired baseline-control
ratios. The slower rule is symmetric. These are exploratory workload
comparisons with a local A/A noise control; they are not simultaneous
confidence guarantees across the whole corpus.

Twenty-one of 28 cases satisfy the faster rule, seven support no timing
claim, and none satisfy the slower rule. This is a statement about these
completed measurements, not a proof that regressions are impossible.
The default-pipeline speedup ranges are 3.97--7.04 for positive
three-braids, 2.39--3.88 for alternating three-braids, and 2.44--5.29
for the five scrambled three-braid unknots. The larger 10.72--51.05
range belongs to the explicitly labeled R3-disabled ablation.

\begingroup
\small
\setlength{\tabcolsep}{4pt}
\begin{longtable}{@{}p{0.38\textwidth}rrrrl@{}}
\caption{All paired pipeline measurements. Times are separate medians in
milliseconds; speedup is the median of paired old/new ratios, which need
not equal the quotient of the displayed medians. ``None'' means no timing
claim under the stated rule.}\label{tab:paired}\\
\toprule
Case & \(n\) & Old ms & New ms & Speedup & Claim\\
\midrule
\endfirsthead
\toprule
Case & \(n\) & Old ms & New ms & Speedup & Claim\\
\midrule
\endhead
\midrule
\multicolumn{6}{r}{\emph{Continued on next page}}\\
\endfoot
\bottomrule
\endlastfoot
""" + "\n".join(lines) + r"""
\end{longtable}
\endgroup

Raw word timings are separate five-repetition experiments. At 128,000
letters the symbolic median is 0.112884 seconds and the matrix median
is 0.626293 seconds; the latter's largest final entry has 88,863 bits.
At 1,024,000 letters the symbolic median is 1.044478 seconds, with exactly
2,048,000 quotient-token operations. At 1,000 letters, however, the matrix
code is faster (0.000258 versus 0.000744 seconds). The asymptotically better
symbolic method does not win every small case. Raw scaling samples do not
use the three-arm comparison rule and are reported as descriptive timings.
"""
    (args.output_dir / "measured_results.tex").write_text(table, encoding="utf-8")
    if args.article:
        start = "% BENCHMARK_TABLE_BEGIN"
        end = "% BENCHMARK_TABLE_END"
        article = args.article.read_text(encoding="utf-8")
        assert article.count(start) == article.count(end) == 1
        before, remaining = article.split(start)
        _, after = remaining.split(end)
        args.article.write_text(before + start + "\n" + table + "\n" + end + after,
                                encoding="utf-8")
    print(f"Wrote {len(paired)} pipeline, {len(raw)} scaling, and {len(profiles)} profile rows.")


if __name__ == "__main__":
    main()
