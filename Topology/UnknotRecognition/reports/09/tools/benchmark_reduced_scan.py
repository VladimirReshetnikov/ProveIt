"""Paired baseline/direct-reduced timings with randomized A/A/B/B order."""
import json
import argparse
import math
import hashlib
from pathlib import Path
import platform
import random
import statistics
import shutil
import sys
import time

def interval(values, rng):
    samples = sorted(statistics.median(rng.choices(values, k=len(values)))
                     for _ in range(2000))
    return [samples[50], samples[1949]]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--fast-root", type=Path, default=Path(__file__).resolve().parents[1] / "fast")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "data/reduced_benchmark_final.json")
    options = parser.parse_args()
    fast_root = options.fast_root.resolve()
    sys.path.insert(0, str(fast_root))
    from fastunknot import Diagram, khovanov_rank
    from fastunknot.simplify import simplify
    from hard_unknots import SURVIVORS
    from fastunknot.reduced_scan import reduced_khovanov_rank
    # Capture the exact files before the timed blocks. Paths in the manifest
    # are relative to this snapshot, so the record remains portable.
    snapshot = options.output.resolve().parent / "benchmark_sources" / options.output.stem
    sources = {"tools/benchmark_reduced_scan.py": Path(__file__).resolve(),
               "fast/hard_unknots.py": fast_root / "hard_unknots.py"}
    sources.update({"fast/fastunknot/" + path.name: path
                    for path in sorted((fast_root / "fastunknot").glob("*.py"))})
    sources.update({"fast/examples/" + path.name: path
                    for path in sorted((fast_root / "examples").glob("*.json"))})
    hashes = {}
    for name, source in sources.items():
        target = snapshot / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
        hashes[name] = hashlib.sha256(target.read_bytes()).hexdigest()
    (snapshot / "source_hashes.json").write_text(json.dumps(hashes, indent=2) + "\n")
    seed = 7291107
    provenance = {
        "random_seed": seed,
        "per_block_job_order_recorded": True,
        "ratio_definition": "sqrt(b[0] * b[1] / (a[0] * a[1])): geometric mean of the two pointed times divided by geometric mean of the two baseline times",
        "aa_ratio_definition": "a[1] / a[0], with labels independent of randomized chronological order",
        "bootstrap": {"resamples": 2000, "statistic": "median paired ratio",
                      "sorted_resample_indices": [50, 1949],
                      "rng_stream": "same seeded stream as job shuffling; ratio and A/A bootstrap calls follow each case"},
        "source_snapshot_captured_before_timing": True,
        "snapshot_directory_relative_to_output": "benchmark_sources/" + options.output.stem,
        "source_sha256": hashes,
        "source_files_unchanged_after_last_completed_case": True,
        "timed_api": "final packaged fastunknot.reduced_scan.reduced_khovanov_rank; no early decision API",
    }
    cases = []
    for name in ("conway", "kinoshita_terasaka", "hard_unknot_8", "unknot_braid40",
                 "stress_braid5_36"):
        cases.append((name, Diagram.from_json(json.loads(
            (fast_root / "examples" / (name + ".json")).read_text()))))
    cases.append(("T3_11", Diagram.from_braid(3, [1, 2] * 11)))
    for i, (_, strands, word) in enumerate(SURVIVORS[:3]):
        d, _ = simplify(Diagram.from_braid(strands, word))
        cases.append(("survivor_" + str(i), d))
    rng = random.Random(seed)
    results = []
    for name, d in cases:
        baseline = khovanov_rank(d.pd)
        order = baseline["order"]
        reduced = reduced_khovanov_rank(d.pd, order=order)
        assert reduced["by_degree"] == {h: v // 2 for h, v in baseline["by_degree"].items()}
        rounds = 21 if name == "stress_braid5_36" else 51
        data = []
        for _ in range(rounds):
            jobs = [("a", 0), ("a", 1), ("b", 0), ("b", 1)]
            rng.shuffle(jobs)
            times = {"a": [None, None], "b": [None, None]}
            for mode, i in jobs:
                start = time.perf_counter_ns()
                r = khovanov_rank(d.pd, order=order) if mode == "a" else reduced_khovanov_rank(d.pd, order=order)
                times[mode][i] = (time.perf_counter_ns() - start) / 1e9
                assert r["by_degree"] == (baseline if mode == "a" else reduced)["by_degree"]
            a, b = times["a"], times["b"]
            data.append({"baseline_seconds": a, "reduced_seconds": b,
                         "job_order": [[mode, index] for mode, index in jobs],
                         "ratio": math.sqrt(b[0] * b[1] / (a[0] * a[1])),
                         "aa_ratio": a[1] / a[0]})
        ratios = [r["ratio"] for r in data]
        aa = [r["aa_ratio"] for r in data]
        row = {"case": name, "crossings": d.crossings, "reduced_rank": reduced["rank"],
               "rounds": rounds, "ratio_median": statistics.median(ratios),
               "ratio_ci95_bootstrap_median": interval(ratios, rng),
               "aa_ratio_median": statistics.median(aa),
               "aa_ci95_bootstrap_median": interval(aa, rng),
               "baseline_seconds_median": statistics.median(x for r in data for x in r["baseline_seconds"]),
               "reduced_seconds_median": statistics.median(x for r in data for x in r["reduced_seconds"]),
               "baseline_stats": baseline["stats"], "reduced_stats": reduced["stats"],
               "order": order, "marked_edge": reduced["marked_edge"],
               "pd": [list(crossing) for crossing in d.pd], "raw": data}
        results.append(row)
        print({k: v for k, v in row.items() if k not in ("raw", "order", "pd", "baseline_stats", "reduced_stats")}, flush=True)
        provenance["source_files_unchanged_after_last_completed_case"] = all(
            hashlib.sha256(source.read_bytes()).hexdigest() == hashes[name]
            for name, source in sources.items())
        options.output.parent.mkdir(parents=True, exist_ok=True)
        options.output.write_text(json.dumps(
            {"python": platform.python_version(), "platform": platform.platform(),
             "method": "same precomputed order; randomized A/A/B/B blocks; geometric arm-mean ratio; bootstrap median of paired ratios",
             "provenance": provenance, "results": results}, indent=2) + "\n")
        if not provenance["source_files_unchanged_after_last_completed_case"]:
            raise RuntimeError("benchmark source changed during the run; timing data retained with warning")


if __name__ == "__main__":
    main()
