#!/usr/bin/env python3
"""Paired timings against the byte-identical previous balancing implementation."""
import argparse
import hashlib
import json
import platform
import random
import statistics
import time
from pathlib import Path
import cached_balancing as improved
import reference_balanced_packing as reference


def benchmark(repeats=5):
    rng = random.Random(20261027)
    results = []
    for nrows, ncols, labels in [(12, 16, 4), (16, 24, 8),
                                (20, 32, 12), (24, 40, 16), (24, 40, 24)]:
        adjacency = [[(1+rng.randrange(2)) if rng.random() < .17 else 0
                       for _ in range(ncols)] for _ in range(nrows)]
        expected = reference.balance_pair_labels(adjacency, labels, keep_certificate=False)
        if improved.balance_pair_labels(adjacency, labels, keep_certificate=False) != expected:
            raise RuntimeError("Benchmark results disagree")
        old_times, new_times = [], []
        for trial in range(repeats):
            for new in ((False, True) if trial % 2 == 0 else (True, False)):
                start = time.perf_counter_ns()
                answer = (improved if new else reference).balance_pair_labels(
                    adjacency, labels, keep_certificate=False)
                elapsed = (time.perf_counter_ns()-start)/1e9
                if answer != expected:
                    raise RuntimeError("Benchmark results changed")
                (new_times if new else old_times).append(elapsed)
        old, new = statistics.median(old_times), statistics.median(new_times)
        results.append({"rows": nrows, "columns": ncols, "labels": labels,
                        "edges": sum(map(sum, adjacency)),
                        "baseline_median_seconds": old, "cached_median_seconds": new,
                        "baseline_over_cached": old/new,
                        "baseline_trials_seconds": old_times,
                        "cached_trials_seconds": new_times,
                        "adjacency": adjacency})
    return {"scope": "actual prior deterministic packet-labeling subroutine; not full SAT",
            "python": platform.python_version(), "platform": platform.platform(),
            "seed": 20261027, "paired_repeats": repeats,
            "certificate_text_enabled": False,
            "exact_potential_checks_enabled_in_both": True,
            "reference_sha256": hashlib.sha256(Path(reference.__file__).read_bytes()).hexdigest(),
            "results": results}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    parser.add_argument("--repeats", type=int, default=5)
    options = parser.parse_args()
    report = json.dumps(benchmark(options.repeats), indent=2)+"\n"
    if options.output:
        Path(options.output).write_text(report)
    print(report)
