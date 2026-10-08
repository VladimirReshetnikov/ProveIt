"""Reproducible paired timings and scaling experiment for braid shortcuts.

Run from fast/:
  python benchmark_braid.py --baseline /path/to/pinned/fast --output results/braid_benchmark.json

Without --baseline, the old side is a use_braid=False ablation of the current
general diagram pipeline.  Reported pipeline times include fresh PD conversion
but exclude Python startup/import and JSON parsing.  Raw-word timings avoid PD
conversion.  Exact operation counts accompany timings; measurements themselves
are never used as a proof of an asymptotic bound.
Any UNKNOWN sample suppresses the speed comparison for its entire case.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import math
import os
from pathlib import Path
import platform
import statistics
import sys
import time

import fastunknot
from hard_unknots import make


BASELINE_REVISION = "4e6fe879e5238ec0b134b6d33fdca0b8c7c1c711"


def load_baseline(path):
    init = Path(path).resolve() / "fastunknot" / "__init__.py"
    name = "pinned_baseline_fastunknot"
    spec = importlib.util.spec_from_file_location(name, init, submodule_search_locations=[str(init.parent)])
    if spec is None or spec.loader is None:
        raise ValueError(f"cannot load baseline package at {init}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def input_cases():
    result = []
    for family, generator in (("positive", (1, 2)), ("alternating", (1, -2))):
        for power in (5, 11, 23, 47, 95):
            result.append({"name": f"{family}_3braid_power_{power}", "family": family,
                           "data": {"braid": {"strands": 3, "word": list(generator) * power}},
                           "options": {}, "expected": "KNOTTED"})
    for seed in (0, 4, 5, 7, 14):
        word = make(3, conjugator_length=15, steps=500, seed=seed)
        for r3 in (True, False):
            result.append({"name": f"scrambled_unknot_seed_{seed}_r3_{int(r3)}",
                           "family": "scrambled_unknot", "seed": seed,
                           "data": {"braid": {"strands": 3, "word": word}},
                           "options": {"use_r3": r3}, "expected": "UNKNOT"})
    morton = [-3, -3, 2, -3, 2, 1, 1, 1, -2, 1, -2]
    result.append({"name": "morton_four_braid_unknot", "family": "fallback",
                   "data": {"braid": {"strands": 4, "word": morton}},
                   "options": {}, "expected": "UNKNOT"})
    for strands in (16, 64, 256):
        word = [1, -2] + list(range(3, strands))
        result.append({"name": f"stabilized_unknot_{strands}_strands", "family": "endpoint_descent",
                       "data": {"braid": {"strands": strands, "word": word}},
                       "options": {}, "expected": "UNKNOT"})
    examples = Path(__file__).parent / "examples"
    for name, expected in (("conway.json", "KNOTTED"), ("kinoshita_terasaka.json", "KNOTTED"),
                           ("hard_unknot_8.json", "UNKNOT"), ("grid_scrambled_unknot.json", "UNKNOT")):
        result.append({"name": name[:-5], "family": "general_input",
                       "data": json.loads((examples / name).read_text()), "options": {}, "expected": expected})
    return result


def run_pipeline(module, case, *, ablation=False):
    started = time.perf_counter()
    diagram = module.Diagram.from_json(case["data"])
    built = time.perf_counter()
    options = {**case["options"], "seconds": 10.0}
    if ablation:
        options["use_braid"] = False
    result = module.recognize(diagram, **options)
    finished = time.perf_counter()
    if result.status not in (case["expected"], "UNKNOWN"):
        raise AssertionError((case["name"], result.to_json()))
    return {"build_seconds": built - started, "recognize_seconds": finished - built,
            "total_seconds": finished - started, "status": result.status,
            "method": result.method, "input_crossings": result.input_crossings,
            "reduced_crossings": result.reduced_crossings}


def summarize(samples):
    result = {"samples": samples, "statuses": sorted({s["status"] for s in samples}),
              "methods": sorted({s["method"] for s in samples})}
    for key in ("build_seconds", "recognize_seconds", "total_seconds"):
        values = [sample[key] for sample in samples]
        result[key] = {"median": statistics.median(values), "min": min(values), "max": max(values)}
    return result


def paired_summary(samples):
    """The baseline project's A/A control and order-statistic comparison rule."""
    statuses = {sample["status"] for arm in samples.values() for sample in arm}
    all_decided = len(statuses) == 1 and statuses <= {"UNKNOT", "KNOTTED"}
    ratios = [new["total_seconds"] / old["total_seconds"]
              for new, old in zip(samples["new"], samples["baseline"])]
    controls = [other["total_seconds"] / old["total_seconds"]
                for other, old in zip(samples["baseline_control"], samples["baseline"])]
    ordered, aa = sorted(ratios), sorted(controls)
    count = len(ordered)
    tail, rank = 0.0, 0
    for candidate in range(1, count // 2 + 1):
        tail += math.comb(count, candidate - 1) / 2 ** count
        if 2 * tail <= 0.05:
            rank = candidate
        else:
            break
    interval = [ordered[rank - 1], ordered[count - rank]] if rank else None
    quartiles = [aa[count // 4], aa[-1 - count // 4]]
    median = statistics.median(ratios)
    conclusion = "no timing claim"
    if not all_decided:
        conclusion = "incomplete or inconsistent verdicts: no timing claim"
    elif interval is not None:
        if interval[1] < 1 and median < quartiles[0]:
            conclusion = "measured faster"
        elif interval[0] > 1 and median > quartiles[1]:
            conclusion = "measured slower"
    return {"new_over_old_ratios": ratios, "old2_over_old_ratios": controls,
            "all_samples_decided_consistently": all_decided,
            "median_new_over_old": median if all_decided else None,
            "median_speedup": 1 / median if all_decided else None,
            "ci95_median_new_over_old": interval if all_decided else None,
            "aa_median": statistics.median(controls), "aa_quartiles": quartiles,
            "comparison_rule_result": conclusion,
            "qualification": "Order-statistic interval assumes independent samples; A/A checks local timing noise."}


def raw_scaling(repetitions, largest):
    rows = []
    for requested in (1000, 2000, 4000, 8000, 16000, 32000, 64000, 128000, 256000, 512000, 1024000):
        if requested > largest:
            continue
        power = requested // 2
        if power % 3 == 0:
            power += 1
        word = [1, -2] * power
        for backend in ("free-product", "matrix"):
            if backend == "matrix" and requested > 128000:
                continue
            samples, witness = [], None
            for _ in range(repetitions):
                started = time.perf_counter()
                witness = fastunknot.braid_certificate(3, word, backend=backend)
                samples.append(time.perf_counter() - started)
            assert witness is not None and witness["status"] == "KNOTTED"
            row = {"family": "alternating_3braid", "letters": len(word), "backend": backend,
                   "samples_seconds": samples, "median_seconds": statistics.median(samples)}
            if backend == "free-product":
                row["stats"] = witness["free_product_stats"]
                row["certificate_cyclic_letters"] = len(witness["cyclic_word"])
            else:
                row["max_entry_bits"] = witness["max_entry_bits"]
            rows.append(row)
            print(f"raw {backend:12s} {len(word):8d} letters: {row['median_seconds']:.6f}s", flush=True)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--output", type=Path, default=Path("results/braid_benchmark.json"))
    parser.add_argument("--repetitions", type=int, default=15)
    parser.add_argument("--raw-repetitions", type=int, default=5)
    parser.add_argument("--largest-raw", type=int, default=1024000)
    args = parser.parse_args()
    if args.repetitions < 1 or args.raw_repetitions < 1:
        parser.error("repetitions must be positive")
    baseline = load_baseline(args.baseline) if args.baseline else fastunknot
    rows = []
    for case in input_cases():
        # Warm both paths; each subsequent run still builds a fresh Diagram.
        run_pipeline(baseline, case, ablation=args.baseline is None)
        run_pipeline(fastunknot, case)
        samples = {"baseline": [], "new": [], "baseline_control": []}
        for repeat in range(args.repetitions):
            order = ["baseline", "new", "baseline_control"]
            offset = repeat % 3
            order = order[offset:] + order[:offset]
            for side in order:
                samples[side].append(run_pipeline(fastunknot if side == "new" else baseline,
                                                  case, ablation=side != "new" and args.baseline is None))
        old, new = summarize(samples["baseline"]), summarize(samples["new"])
        comparison = paired_summary(samples)
        speedup = comparison["median_speedup"]
        row = {**case, "baseline": old, "new": new,
               "baseline_control": summarize(samples["baseline_control"]),
               "paired_comparison": comparison, "total_speedup": speedup}
        rows.append(row)
        shown_speedup = f"{speedup:.2f}" if speedup is not None else "not comparable"
        print(f"{case['name']:43s} old={old['total_seconds']['median']:.6f}s "
              f"new={new['total_seconds']['median']:.6f}s ratio={shown_speedup} "
              f"({comparison['comparison_rule_result']})", flush=True)
    output = {
        "baseline_revision": BASELINE_REVISION if args.baseline else None,
        "comparison": "pinned-source comparison" if args.baseline else "source-braid shortcut ablation",
        "python": platform.python_version(), "platform": platform.platform(),
        "processor": platform.processor(), "logical_cpus": os.cpu_count(),
        "repetitions": args.repetitions, "clock": "time.perf_counter",
        "raw_repetitions": args.raw_repetitions,
        "timing_scope": "fresh PD construction and recognize; excludes process startup, imports and JSON parsing",
        "pairing": "three rotating arms: baseline, new, baseline-control; one warm-up per implementation",
        "general_quasipolynomial_bound_established": False,
        "cases": rows,
        "raw_scaling": raw_scaling(args.raw_repetitions, args.largest_raw),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(f"saved {args.output}")


if __name__ == "__main__":
    main()

