"""Export all cases and comparisons from a completed Potts benchmark."""
import argparse
import csv
import json
from pathlib import Path
import statistics

from benchmark_potts import median_interval


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    if not data.get("complete"):
        raise ValueError("benchmark is incomplete")
    rows = []
    for case in data["cases"]:
        counters = case["counters"]
        global_exact = counters["exact_q6"]
        factored = counters["factored_exact_q6"]
        ratios = [sample["ns"]["exact_q6"] / sample["ns"]["factored_exact_q6"]
                  for sample in case["samples"]]
        interval = median_interval(ratios)
        row = dict(name=case["name"], corpus=case["corpus"], crossings=case["crossings"],
                   max_cut_edges=case["boundary_profile"][0],
                   max_spin_frontier=global_exact["max_spin_frontier"],
                   max_component_frontier=factored["max_component_frontier"],
                   exact_q5_detects=counters["exact_q5"]["differs"],
                   exact_q6_detects=global_exact["differs"],
                   generic_jones_detects=case["diagnostics"]["original_generic_jones_detects"],
                   exact_q6_peak_keys=global_exact["peak_states"],
                   factor_q6_peak_total_keys=factored["peak_states"],
                   factor_q6_peak_component_keys=factored["peak_component_states"],
                   exact_q6_transitions=global_exact["transitions"],
                   factor_q6_transitions=factored["transitions"],
                   exact_q6_max_coefficient_bits=global_exact["max_coefficient_bits"],
                   factor_q6_max_coefficient_bits=factored["max_coefficient_bits"],
                   global_q6_over_factor_q6_median=statistics.median(ratios),
                   global_q6_over_factor_q6_ci_low=interval[0],
                   global_q6_over_factor_q6_ci_high=interval[1],
                   aa_median=case["aa_median"], aa_iqr_low=case["aa_iqr"][0],
                   aa_iqr_high=case["aa_iqr"][1])
        for arm, median in case["median_ms"].items():
            row[arm + "_median_ms"] = median
        for arm, comparison in case["comparisons"].items():
            row["matching_over_" + arm + "_median"] = comparison["median_matching_over_arm"]
            interval = comparison["median_ratio_interval_at_least_95pct"]
            row["matching_over_" + arm + "_ci_low"] = interval[0]
            row["matching_over_" + arm + "_ci_high"] = interval[1]
            row[arm + "_timing_claim"] = comparison["claim"]
        rows.append(row)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


if __name__ == "__main__":
    main()
