"""Paired A/B and A/A timings for the signed Seifert front end.

The timed boundary is a recognition call on a validated PD diagram.  A fresh
uncached Diagram record is supplied to every call.  Input validation, file
I/O, imports, and JSON serialization are excluded symmetrically.

The sibling fast/ directory is selected automatically in the delivered
package.  Against an external baseline, put that tree on PYTHONPATH instead
and place this script outside the delivered package.  No multiprocessing.
"""
from __future__ import annotations

import argparse
import gc
from inspect import signature
import json
import math
import os
from pathlib import Path
import platform
import random
import statistics
import sys
from time import perf_counter_ns, process_time_ns

# Prefer the implementation delivered beside this script, regardless of cwd.
FAST_ROOT = Path(__file__).resolve().parents[1] / "fast"
if FAST_ROOT.is_dir():
    sys.path.insert(0, str(FAST_ROOT))

import fastunknot
from fastunknot import Diagram, recognize
try:
    from fastunknot.seifert import seifert_certificate
except ImportError:
    from seifert import seifert_certificate

BASELINE_OPTIONS = {"use_seifert": False} if "use_seifert" in signature(recognize).parameters else {}


def baseline(pd):
    result = recognize(Diagram(pd), **BASELINE_OPTIONS)
    return result.status, result.method


def structural(pd):
    diagram = Diagram(pd)
    certificate = seifert_certificate(diagram)
    if certificate is not None:
        return certificate["status"], certificate["criterion"]
    result = recognize(diagram, **BASELINE_OPTIONS)
    return result.status, result.method


def cases():
    result = []
    for m in (2, 5, 10, 20, 50, 100, 250, 500):
        diagram = Diagram.from_braid(3, [1, -2] * m)
        result.append((f"weaving_3_{m}", "weaving3", diagram.pd))
    for m in (5, 20, 100, 500):
        diagram = Diagram.from_braid(3, [1, 2] * m)
        result.append((f"positive_3_{m}", "positive3", diagram.pd))
    for m in (7, 31, 101, 251):
        diagram = Diagram.from_braid(5, [1, 2, 3, 4] * m)
        result.append((f"positive_5_{m}", "positive5", diagram.pd))
    examples = Path(fastunknot.__file__).resolve().parent.parent / "examples"
    for name in ("conway", "kinoshita_terasaka", "hard_unknot_8", "grid_scrambled_unknot"):
        diagram = Diagram.from_json(json.loads((examples / f"{name}.json").read_text()))
        result.append((name, "inconclusive_control", diagram.pd))
    return result


def timed(function, pd, loops):
    cpu_start = process_time_ns()
    wall_start = perf_counter_ns()
    answer = None
    for _ in range(loops):
        answer = function(pd)
    wall = (perf_counter_ns() - wall_start) / loops / 1e9
    cpu = (process_time_ns() - cpu_start) / loops / 1e9
    return {"wall_seconds": wall, "cpu_seconds": cpu, "status": answer[0], "method": answer[1]}


def geometric(values):
    return math.exp(statistics.mean(math.log(v) for v in values))


def bootstrap(values):
    logs = [math.log(v) for v in values]
    rng = random.Random(2026100704)
    means = sorted(math.exp(statistics.mean(rng.choices(logs, k=len(logs)))) for _ in range(3000))
    return [means[75], means[2924]]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True)
    parser.add_argument("--rounds", type=int, default=9)
    parser.add_argument("--target-batch-seconds", type=float, default=0.01)
    parser.add_argument("--max-loops", type=int, default=128)
    parser.add_argument("--pin-cpu", type=int)
    parser.add_argument("--disable-gc", action="store_true")
    args = parser.parse_args()
    if args.rounds < 2 or args.target_batch_seconds <= 0 or args.max_loops < 1:
        parser.error("positive timing settings and at least two rounds required")
    if args.pin_cpu is not None:
        if not hasattr(os, "sched_setaffinity"):
            parser.error("CPU affinity is unavailable on this platform")
        os.sched_setaffinity(0, {args.pin_cpu})
    if args.disable_gc:
        gc.collect()
        gc.disable()
    tasks = cases()
    records = {}
    for name, family, pd in tasks:
        a, b = baseline(pd), structural(pd)
        if a[0] != b[0] or a[0] == "UNKNOWN":
            raise AssertionError((name, a, b))
        pilot = timed(baseline, pd, 1)
        loops = max(1, min(args.max_loops, math.ceil(args.target_batch_seconds / pilot["wall_seconds"])))
        records[name] = {"family": family, "crossings": len(pd), "loops": loops,
                         "status": a[0], "baseline_method": a[1], "structural_method": b[1],
                         "samples": []}
    rng = random.Random(2026100703)
    for round_index in range(args.rounds):
        shuffled = list(tasks)
        rng.shuffle(shuffled)
        for name, _, pd in shuffled:
            arms = [("A", baseline), ("B", structural), ("AA1", baseline), ("AA2", baseline)]
            rng.shuffle(arms)
            record = records[name]
            sample = {"round": round_index, "arm_order": [name for name, _ in arms]}
            for arm, function in arms:
                sample[arm] = timed(function, pd, record["loops"])
                if sample[arm]["status"] != record["status"]:
                    raise AssertionError((name, arm, sample[arm]))
            record["samples"].append(sample)
        print(f"completed round {round_index + 1}/{args.rounds}", flush=True)
    for record in records.values():
        samples = record["samples"]
        ratios = [s["A"]["wall_seconds"] / s["B"]["wall_seconds"] for s in samples]
        aa = [s["AA1"]["wall_seconds"] / s["AA2"]["wall_seconds"] for s in samples]
        record["summary"] = {
            "median_A_seconds": statistics.median(s["A"]["wall_seconds"] for s in samples),
            "median_B_seconds": statistics.median(s["B"]["wall_seconds"] for s in samples),
            "paired_AB_geometric_speedup": geometric(ratios),
            "paired_AB_speedup_95pct_bootstrap": bootstrap(ratios),
            "paired_AB_min_max": [min(ratios), max(ratios)],
            "paired_AA_geometric_ratio": geometric(aa),
            "paired_AA_min_max": [min(aa), max(aa)],
        }
    output = {
        "protocol": "random-order interleaved A/B plus A/A; fresh uncached validated PD per invocation",
        "boundary": "recognition only; excludes input validation, imports, file I/O and JSON output",
        "A": "unmodified baseline fastunknot.recognize with default settings",
        "B": "seifert_certificate first; on inconclusive, same default baseline recognizer",
        "AA1_AA2": "two independent identical baseline arms",
        "uncertainty": "95% percentile bootstrap of mean paired log speedups; 3000 fixed-seed resamples",
        "rounds": args.rounds,
        "baseline_options": BASELINE_OPTIONS,
        "target_batch_seconds": args.target_batch_seconds,
        "max_loops": args.max_loops,
        "gc_disabled": args.disable_gc,
        "cpu_affinity": sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None,
        "environment": {"python": sys.version, "platform": platform.platform(),
                        "logical_cpus": os.cpu_count(), "baseline_package": str(Path(fastunknot.__file__).resolve())},
        "cases": records,
    }
    Path(args.output).write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({name: value["summary"] for name, value in records.items()}, indent=2))


if __name__ == "__main__":
    main()
