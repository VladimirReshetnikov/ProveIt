"""Paired complete searches in finite abstract languages, not knot benchmarks.

Grammar construction and mesh replay are outside both timers. Both algorithms
perform the same exact-state dominance, transitions, and source digest. The
basis route additionally generates features and reduces. Feature caches start
empty on every timed call. Timing order is deterministically randomized.
"""
from __future__ import annotations
import csv, gc, json, platform, random, statistics, sys, time
from pathlib import Path
from experiments.common import workload
from rooted_disc.kernel import feature
from rooted_disc.assembly import solve
from rooted_disc.mesh import replay_assignment

CASES = [("narrow-control", 2, 2, 4, True), ("width-3", 3, 6, 4, True),
         ("width-4", 4, 6, 4, True), ("width-5", 5, 6, 4, True),
         ("no-reset-control", 4, 6, 1, False)]


def run(repetitions: int = 3) -> dict:
    rng = random.Random(314159)
    output = {"python": sys.version, "platform": platform.platform(), "repetitions": repetitions,
              "order_seed": 314159, "grammar_seed": 271828,
              "timing_scope": "complete abstract search; grammar construction and independent mesh replay excluded",
              "cases": []}
    for name, width, layers, q, resets in CASES:
        g = workload(width, layers, q, include_reset=resets)
        samples = {"exact": [], "basis": [], "exact_control": []}
        stats, order_log = {}, []
        for repetition in range(repetitions):
            order = ["exact", "basis", "exact_control"]; rng.shuffle(order); order_log.append(order)
            for label in order:
                feature.cache_clear(); gc.collect()
                start = time.perf_counter_ns()
                answer = solve(g, reduced=(label == "basis"))
                elapsed = (time.perf_counter_ns() - start) / 1e9
                samples[label].append(elapsed)
                stats[label] = {"cost": answer.cost, "status": answer.status, "transitions": answer.transitions,
                                "peak_exact_table": answer.peak_exact_table, "peak_retained": answer.peak_retained}
                if answer.witness is not None:
                    mesh = replay_assignment(g, answer.witness)
                    assert mesh.succeeds(g.target) and mesh.cost == answer.cost
            assert stats["exact"]["cost"] == stats["basis"]["cost"] == stats["exact_control"]["cost"]
            assert stats["exact"]["status"] == stats["basis"]["status"]
        med = {label: statistics.median(values) for label, values in samples.items()}
        case = {"name": name, "width": width, "layers_before_cap": layers, "q": q, "resets": resets,
                "source_sha256": g.digest(), "samples_seconds": samples, "median_seconds": med,
                "speedup_exact_over_basis": med["exact"] / med["basis"],
                "aa_ratio": med["exact"] / med["exact_control"], "stats": stats, "order": order_log}
        output["cases"].append(case)
        print(name, med, "gain", case["speedup_exact_over_basis"], flush=True)
    return output

if __name__ == "__main__":
    result = run()
    Path("results/benchmark.json").write_text(json.dumps(result, indent=2) + "\n")
    with Path("results/benchmark.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["case", "width", "q", "exact_ms", "basis_ms", "ratio", "AA_ratio", "exact_transitions", "basis_transitions", "exact_peak", "basis_peak"])
        for c in result["cases"]:
            writer.writerow([c["name"], c["width"], c["q"], 1000*c["median_seconds"]["exact"], 1000*c["median_seconds"]["basis"],
                             c["speedup_exact_over_basis"], c["aa_ratio"], c["stats"]["exact"]["transitions"], c["stats"]["basis"]["transitions"],
                             c["stats"]["exact"]["peak_retained"], c["stats"]["basis"]["peak_retained"]])
