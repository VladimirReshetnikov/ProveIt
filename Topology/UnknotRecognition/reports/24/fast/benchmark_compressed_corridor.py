"""Targeted follow-up: sparse scalar setup and port-count direction selection.

The earlier full-matrix benchmark is frozen. This experiment compares only the
new setup strategy, the frozen corridor's forward/auto modes, and the production
sparse scanner with an identical control. Actual timing includes fresh scanner
construction; synthetic preparation and all explicit verification are excluded.
"""
import argparse
import gc
import hashlib
import importlib.util
import json
from math import ceil
from pathlib import Path
import platform
import random
import statistics
from time import monotonic, perf_counter

from benchmark_corridor import make_kernel, kernel_invariant
from fastunknot import Diagram
from fastunknot.corridor import CorridorScan
from fastunknot.graded import GradedScan
from fastunknot.ordering import best_scan_order
from fastunknot.scan_fast import FastScan


def load_frozen(path):
    spec = importlib.util.spec_from_file_location("fastunknot.corridor_v1_reference", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def report(samples, strategies):
    ratios = {
        "standard_over_control": ("standard", "control"),
        "standard_over_compressed": ("standard", "compressed"),
        "auto_over_compressed": ("baseline_auto", "compressed"),
        "forward_over_compressed": ("baseline_forward", "compressed"),
        "ports_global_over_compressed": ("ports_global", "compressed"),
        "auto_over_ports_global": ("baseline_auto", "ports_global"),
    }
    return dict(seconds={arm: statistics.median(s[arm] for s in samples) for arm in strategies},
                paired_ratios={name: statistics.median(s[a] / s[b] for s in samples)
                               for name, (a, b) in ratios.items()})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--sample-seconds", type=float, default=0.02)
    parser.add_argument("--scan-seconds", type=float, default=30)
    parser.add_argument("--scope", choices=("all", "actual", "kernel"), default="all")
    parser.add_argument("--frozen", type=Path, default=Path(__file__).parent.parent /
                        "reference" / "corridor_v1.py")
    args = parser.parse_args()
    if args.rounds < 1 or args.sample_seconds <= 0 or args.scan_seconds <= 0:
        parser.error("round count and time limits must be positive")
    frozen = load_frozen(args.frozen)
    strategies = {
        "standard": (FastScan, {}),
        "control": (FastScan, {}),
        "baseline_forward": (frozen.CorridorScan, {"mode": "forward", "prune": True}),
        "baseline_auto": (frozen.CorridorScan, {"mode": "auto", "prune": True}),
        "ports_global": (CorridorScan, {"mode": "auto", "prune": True,
                                       "direction_policy": "ports", "scalar_engine": "global"}),
        "compressed": (CorridorScan, {"mode": "auto", "prune": True,
                                     "direction_policy": "ports", "scalar_engine": "components"}),
    }
    rng = random.Random(2026100822)
    result = dict(python=platform.python_version(), platform=platform.platform(),
                  seed=2026100822, rounds=args.rounds, scope=__doc__,
                  batch_target_seconds=args.sample_seconds, batch_repetition_cap=32,
                  per_scanner_seconds=args.scan_seconds,
                  garbage_collection="gc.collect before each measured batch; collector remains enabled",
                  benchmark_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  frozen_sha256=hashlib.sha256(args.frozen.read_bytes()).hexdigest(),
                  implementation_sha256={name: hashlib.sha256((Path(__file__).parent /
                      "fastunknot" / name).read_bytes()).hexdigest()
                      for name in ("graded.py", "binary_contraction.py", "corridor.py",
                                   "scalar_components.py")}, actual=[], kernels=[])

    def save():
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")

    if args.scope in ("all", "actual"):
        cases = [("two_strand_201", Diagram.from_braid(2, [1] * 201))]
        for name in ("conway", "hard_unknot_8"):
            path = Path(__file__).parent / "examples" / (name + ".json")
            cases.append((name, Diagram.from_json(json.loads(path.read_text()))))
        for name, diagram in cases:
            order = best_scan_order(diagram.pd)

            def run(arm):
                scan_type, options = strategies[arm]
                scan = scan_type(deadline=monotonic() + args.scan_seconds, **options)
                for crossing in order:
                    scan.add_crossing(diagram.pd[crossing])
                return scan

            repetitions = {}
            for arm in strategies:
                start = perf_counter()
                run(arm)
                elapsed = perf_counter() - start
                repetitions[arm] = min(32, max(1, ceil(args.sample_seconds / elapsed)))
            repetitions["standard"] = repetitions["control"] = max(
                repetitions["standard"], repetitions["control"])
            expected = expected_graded = None
            samples, metrics = [], {}
            for _ in range(args.rounds):
                arms = list(strategies)
                rng.shuffle(arms)
                sample = dict(order=arms)
                for arm in arms:
                    gc.collect()
                    start = perf_counter()
                    for _ in range(repetitions[arm]):
                        scan = run(arm)
                    elapsed = (perf_counter() - start) / repetitions[arm]
                    observed = scan.ranks_by_degree()
                    if expected is None:
                        expected = observed
                    if observed != expected:
                        raise ArithmeticError(f"actual homology disagreement: {name}, {arm}")
                    if hasattr(scan, "ranks_by_bidegree"):
                        bidegree = scan.ranks_by_bidegree()
                        if expected_graded is None:
                            expected_graded = bidegree
                        if bidegree != expected_graded:
                            raise ArithmeticError(f"quantum homology disagreement: {name}, {arm}")
                    sample[arm] = elapsed
                    metrics[arm] = dict(rank=scan.total_rank(), by_degree=observed, stats=dict(scan.stats))
                samples.append(sample)
            row = dict(name=name, pd=diagram.pd, order=order, repetitions=repetitions,
                       samples=samples, metrics=metrics, **report(samples, strategies))
            result["actual"].append(row)
            save()
            print("actual", name, json.dumps(row["paired_ratios"]), flush=True)
    if args.scope in ("all", "kernel"):
        families = [("shared_suffix", "shared_suffix_15", 15, 1, 15, 0),
                    ("shared_suffix", "shared_suffix_63", 63, 1, 63, 0),
                    ("shared_suffix", "shared_suffix_255", 255, 1, 255, 0),
                    ("dead_leaves", "dead_leaves_255", 1, 1, 0, 255)]
        for family, name, sources, sinks, core, dead in families:
            def prepare(arm):
                scan_type, options = strategies[arm]
                return make_kernel(family, scan_type, sources, sinks, core, dead, options=options)

            repetitions = {}
            for arm in strategies:
                scan = prepare(arm)
                scan.deadline = monotonic() + args.scan_seconds
                start = perf_counter()
                scan.eliminate()
                elapsed = perf_counter() - start
                repetitions[arm] = min(32, max(1, ceil(args.sample_seconds / elapsed)))
            repetitions["standard"] = repetitions["control"] = max(
                repetitions["standard"], repetitions["control"])
            samples, metrics = [], {}
            expected = None
            for _ in range(args.rounds):
                arms = list(strategies)
                rng.shuffle(arms)
                sample = dict(order=arms)
                for arm in arms:
                    batch = [prepare(arm) for _ in range(repetitions[arm])]
                    scan = batch[-1]
                    before = scan.live
                    GradedScan.check_grading(scan)
                    scan.check_d_squared()
                    gc.collect()
                    for scan in batch:
                        scan.deadline = monotonic() + args.scan_seconds
                    start = perf_counter()
                    for scan in batch:
                        scan.eliminate()
                    elapsed = (perf_counter() - start) / repetitions[arm]
                    observed = kernel_invariant(scan)
                    if observed["sources"] != sources or observed["sinks"] != sinks:
                        raise ArithmeticError("wrong planted survivor count")
                    if expected is None:
                        expected = observed
                    if observed != expected:
                        raise ArithmeticError(f"kernel disagreement: {name}, {arm}")
                    if observed["coefficient_rank"] != 1:
                        raise ArithmeticError("nonzero sparse family output disappeared")
                    sample[arm] = elapsed
                    metrics[arm] = dict(invariant=observed, stats=dict(scan.stats))
                samples.append(sample)
            row = dict(name=name, family=family, sources=sources, sinks=sinks, core=core, dead=dead,
                       objects=before, repetitions=repetitions, samples=samples, metrics=metrics,
                       **report(samples, strategies))
            result["kernels"].append(row)
            save()
            print("kernel", name, json.dumps(row["paired_ratios"]), flush=True)
    save()


if __name__ == "__main__":
    main()
