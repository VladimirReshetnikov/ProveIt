#!/usr/bin/env python3
"""Reproducible inner-kernel benchmark, explicitly not SAT solver timings.

Both branches receive the same frozen canonical residues.  The peeled timing
includes checking and normalizing them.  Input generation is excluded from
both timings.  Median paired trials alternate execution order.
"""
from __future__ import annotations
import argparse
import json
import platform
import random
import statistics
import time
from pathlib import Path
from precision_peeling import (ScaledMatrix, full_precision_cycle, peeled_cycle,
                               require)


def benchmark(precision=2048, dimension=12, groups=5, repeats=7) -> dict:
    rng = random.Random(20261027)
    results = []
    for total_valuation in (0, precision//4, precision//2,
                            3*precision//4, 7*precision//8, 31*precision//32):
        valuations = [total_valuation//groups+(j < total_valuation % groups)
                      for j in range(groups)]
        modulus = 1 << precision
        matrices = []
        for valuation in valuations:
            entries = tuple(tuple((rng.getrandbits(precision) << valuation) % modulus
                                  for _ in range(dimension))
                            for _ in range(dimension))
            matrices.append(ScaledMatrix(entries, valuation))
        expected = full_precision_cycle(matrices, precision)
        require(peeled_cycle(matrices, precision) == expected, "benchmark mismatch")
        old_times, new_times = [], []
        for trial in range(repeats):
            for peeled in ((False, True) if trial % 2 == 0 else (True, False)):
                before = time.perf_counter_ns()
                result = (peeled_cycle if peeled else full_precision_cycle)(matrices, precision)
                elapsed = (time.perf_counter_ns()-before)/1e9
                require(result == expected, "benchmark result changed")
                (new_times if peeled else old_times).append(elapsed)
        old, new = statistics.median(old_times), statistics.median(new_times)
        results.append({"P": precision, "V": total_valuation,
                        "Q": precision-total_valuation,
                        "baseline_median_seconds": old,
                        "peeled_median_seconds": new,
                        "baseline_over_peeled": old/new,
                        "baseline_trials_seconds": old_times,
                        "peeled_trials_seconds": new_times})
    return {"scope": "dense cyclic tensor arithmetic only; not SAT timings",
            "python": platform.python_version(), "platform": platform.platform(),
            "processor": platform.processor(), "seed": 20261027,
            "dimension": dimension, "groups": groups, "paired_repeats": repeats,
            "normalization_included_in_peeled_timing": True,
            "input_generation_timed": False, "results": results}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    parser.add_argument("--precision", type=int, default=2048)
    parser.add_argument("--dimension", type=int, default=12)
    parser.add_argument("--groups", type=int, default=5)
    parser.add_argument("--repeats", type=int, default=7)
    options = parser.parse_args()
    report = json.dumps(benchmark(options.precision, options.dimension,
                                 options.groups, options.repeats), indent=2)+"\n"
    if options.output:
        Path(options.output).write_text(report)
    print(report)
