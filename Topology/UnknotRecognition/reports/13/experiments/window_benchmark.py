#!/usr/bin/env python3
"""Paired, reproducible timings of full scans and exact normalized-H0 windows.

Run from the archive root:
    python experiments/window_benchmark.py --repeats 7

Input orientation and scan order are identical in every pair.  Each variant
is warmed once; execution order alternates between pairs.  Cheap invariant
filters are deliberately absent because this measures the scanner kernel.
The full rank and selected homological rank are different outputs; this is
an obstruction cost comparison, not a claim to compute all homology faster.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import platform
from pathlib import Path
from statistics import median, quantiles
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "fast"))

from fastunknot.diagram import Diagram
from fastunknot.geometry import ScanLimit
from fastunknot.ordering import best_scan_order
from fastunknot.scan import khovanov_rank
from fastunknot.window_scan import khovanov_window


def summary(samples):
    quartiles = quantiles(samples, n=4, method="inclusive") if len(samples) > 1 else samples * 3
    return {
        "samples_seconds": samples,
        "median_seconds": median(samples),
        "q1_seconds": quartiles[0],
        "q3_seconds": quartiles[2],
        "minimum_seconds": min(samples),
        "maximum_seconds": max(samples),
    }


def load(name):
    return Diagram.from_json(json.loads((ROOT / "fast" / "examples" / f"{name}.json").read_text()))


def benchmark(name, diagram, repeats, seconds, mirrored=False):
    n = diagram.crossings
    target = diagram.signs().count(-1)
    order = best_scan_order(diagram.pd, tries=min(n, 12))
    runners = {
        "full": lambda: khovanov_rank(diagram.pd, order=order, seconds=seconds, race=1),
        "window": lambda: khovanov_window(diagram.pd, target, target,
                                            order=order, seconds=seconds),
    }
    outputs = {key: run() for key, run in runners.items()}
    expected = {h: dim for h, dim in outputs["full"]["by_degree"].items() if h == target}
    if outputs["window"]["by_degree"] != expected:
        raise ArithmeticError(f"window/full disagreement on {name}")
    samples = {key: [] for key in runners}
    for repetition in range(repeats):
        keys = ("full", "window") if repetition % 2 == 0 else ("window", "full")
        for key in keys:
            started = perf_counter()
            result = runners[key]()
            samples[key].append(perf_counter() - started)
            if result["by_degree"] != outputs[key]["by_degree"]:
                raise ArithmeticError(f"nondeterministic homological ranks on {name}")
    without_guard_pruning = khovanov_window(
        diagram.pd, target, target, order=order, seconds=seconds,
        prune_isolated_guards=False,
    )
    if without_guard_pruning["by_degree"] != expected:
        raise ArithmeticError(f"guard-pruning ablation disagreement on {name}")
    normalized = json.dumps(diagram.to_json(), sort_keys=True, separators=(",", ":")).encode()
    full_time = median(samples["full"])
    window_time = median(samples["window"])
    result = {
        "name": name,
        "crossings": n,
        "target_raw_degree": target,
        "target_normalized_degree": 0,
        "input_mirrored": mirrored,
        "pd": diagram.to_json()["pd"],
        "pd_sha256": hashlib.sha256(normalized).hexdigest(),
        "order": order,
        "full_rank": outputs["full"]["rank"],
        "window_rank": outputs["window"]["window_rank"],
        "is_nontriviality_certificate": outputs["window"]["window_rank"] != 2,
        "median_full_over_window": full_time / window_time,
        "full": {
            **summary(samples["full"]),
            "by_degree": outputs["full"]["by_degree"],
            "stats": outputs["full"]["stats"],
        },
        "window": {
            **summary(samples["window"]),
            "by_degree": outputs["window"]["by_degree"],
            "stats": outputs["window"]["stats"],
        },
        "window_without_isolated_guard_pruning": {
            "by_degree": without_guard_pruning["by_degree"],
            "stats": without_guard_pruning["stats"],
            "timed": False,
        },
    }
    print(f"{name:32} n={n:2} h={target:2} H0={result['window_rank']:4} "
          f"full={full_time:.6f}s window={window_time:.6f}s "
          f"ratio={result['median_full_over_window']:.3f}", flush=True)
    return result


def resource_comparison(seconds):
    """An identical ceiling blocks the full scan but permits an H0 witness."""
    diagram = load("stress_braid5_36")
    target = diagram.signs().count(-1)
    order = best_scan_order(diagram.pd, tries=min(diagram.crossings, 12))
    ceiling = 10000
    result = {"name": "stress_braid5_36", "max_objects": ceiling, "order": order}
    try:
        full = khovanov_rank(diagram.pd, order=order, max_objects=ceiling, seconds=seconds)
    except ScanLimit as exc:
        result["full"] = {"outcome": "limit", "reason": str(exc)}
    else:
        result["full"] = {"outcome": "completed", "rank": full["rank"]}
    window = khovanov_window(diagram.pd, target, target, order=order,
                             max_objects=ceiling, seconds=seconds)
    result["window"] = {
        "outcome": "completed",
        "target_raw_degree": target,
        "window_rank": window["window_rank"],
        "peak_retained_objects": window["stats"]["max_objects_before_elimination"],
        "is_nontriviality_certificate": window["window_rank"] != 2,
    }
    if result["full"]["outcome"] != "limit" or window["window_rank"] != 698:
        raise ArithmeticError("the recorded resource comparison no longer reproduces")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeats", type=int, default=7)
    parser.add_argument("--seconds", type=float, default=30.0,
                        help="per-call cap; a timeout aborts instead of fabricating a speed ratio")
    parser.add_argument("--out", type=Path, default=ROOT / "results" / "window_benchmark.json")
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    cases = [(name, load(name), False) for name in (
        "conway", "kinoshita_terasaka", "hard_unknot_8",
        "grid_determinant_one_knot", "stress_braid5_36",
    )]
    cases += [
        ("conway_mirrored_h0", load("conway").mirror(), True),
        ("kinoshita_terasaka_mirrored_h0", load("kinoshita_terasaka").mirror(), True),
        ("torus_4_7_filter_control", Diagram.from_braid(4, [-1, -2, -3] * 7), False),
        ("torus_2_31_peak_control", Diagram.from_braid(2, [-1] * 31), False),
    ]
    results = {
        "schema": "unknot-window-benchmark-v1",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "python": sys.version,
        "platform": platform.platform(),
        "repeats": args.repeats,
        "timing_protocol": "one warmup each; alternating paired order; identical PD and scan order",
        "scope": "core scans without cheap filters; full ranks versus exact normalized H0 only",
        "source_commit": "ca61a1a5f967999d778d6efd7c882e77a2eb379d",
        "cases": [benchmark(name, d, args.repeats, args.seconds, mirrored)
                  for name, d, mirrored in cases],
        "resource_comparison": resource_comparison(args.seconds),
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")


if __name__ == "__main__":
    main()
