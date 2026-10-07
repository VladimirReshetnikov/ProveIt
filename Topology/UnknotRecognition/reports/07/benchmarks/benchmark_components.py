"""Bounded, interleaved scanner benchmark with an A/A control.

This deliberately bypasses recognition filters and geometric connected-sum
factoring.  It measures the new backend, not the total recognition pipeline.
"""
import argparse
import json
import math
from pathlib import Path
import platform
import random
import statistics
import sys
import time

# Prefer the implementation delivered beside this script, regardless of cwd.
FAST_ROOT = Path(__file__).resolve().parents[1] / "fast"
if FAST_ROOT.is_dir():
    sys.path.insert(0, str(FAST_ROOT))

from fastunknot import Diagram
from fastunknot.scan import khovanov_rank
from fastunknot.component_scan import compressed_khovanov_decide, compressed_khovanov_rank


def load(path):
    data = json.loads(path.read_text())
    if "pd" in data:
        return Diagram.from_pd(data["pd"])
    return Diagram.from_braid(data["braid"]["strands"], data["braid"]["word"])


def metrics(result):
    stats = result["stats"]
    return dict(rank=result.get("rank"), rank_capped=result.get("rank_capped"),
                work=stats.get("entries", 0) + stats.get("compositions", 0),
                stats=stats)


def run(examples, rounds):
    rng = random.Random(20261007)
    report = dict(python=platform.python_version(), platform=platform.platform(),
                  rounds=rounds,
                  scope="Raw scanner, without geometric factoring or recognition filters",
                  timing_caution="Interleaved ratios with two baseline calls per round; shared host; small sample",
                  cases={})
    for name in ["conway", "torus_3_5", "stress_braid5_36", "conway_sum_2", "conway_sum_3"]:
        d = load(examples / (name + ".json"))
        functions = dict(A1=khovanov_rank, A2=khovanov_rank,
                         full=compressed_khovanov_rank, saturated=compressed_khovanov_decide)
        samples = []
        results = {}
        for _ in range(rounds):
            labels = list(functions)
            rng.shuffle(labels)
            sample = {}
            for label in labels:
                begin = time.perf_counter()
                result = functions[label](d.pd)
                sample[label] = time.perf_counter() - begin
                results[label] = metrics(result)
            if results["A1"]["rank"] != results["full"]["rank"]:
                raise AssertionError("rank mismatch")
            if min(3, results["A1"]["rank"]) != results["saturated"]["rank_capped"]:
                raise AssertionError("decision mismatch")
            samples.append(sample)
        ratios = {label: [sample[label] / math.sqrt(sample["A1"] * sample["A2"])
                           for sample in samples] for label in ["full", "saturated"]}
        aa = [sample["A2"] / sample["A1"] for sample in samples]
        row = dict(crossings=len(d.pd), metrics=results, samples_seconds=samples,
                   median_seconds={label: statistics.median(s[label] for s in samples)
                                   for label in functions},
                   median_ratios={label: statistics.median(values) for label, values in ratios.items()},
                   ratio_ranges={label: [min(values), max(values)] for label, values in ratios.items()},
                   aa_median=statistics.median(aa), aa_range=[min(aa), max(aa)])
        report["cases"][name] = row
        print(name, json.dumps({k: row[k] for k in ["median_seconds", "median_ratios", "aa_range"]}), flush=True)
    d = load(examples / "conway_sum_8.json")
    row = {}
    for label, fn in [("full", compressed_khovanov_rank), ("saturated", compressed_khovanov_decide)]:
        begin = time.perf_counter()
        result = fn(d.pd)
        row[label] = dict(seconds=time.perf_counter() - begin, **metrics(result))
    report["cases"]["conway_sum_8_no_expansion"] = row
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--examples", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=7)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error("rounds must be positive")
    args.output.write_text(json.dumps(run(args.examples, args.rounds), indent=2) + "\n")
