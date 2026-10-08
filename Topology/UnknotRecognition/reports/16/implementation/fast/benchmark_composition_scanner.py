"""Paired full-scanner benchmark with fixed orders and isolated processes.

Each sample is run in a fresh child process, with one untimed warm-up of that
same configuration before one timed scan. Import, input parsing, validation,
and order selection are outside the timed region. The chosen order and shape
cache setting are shared by all modes. Pass --baseline-root to compare with an
immutable original fast/ checkout; otherwise baseline is this copy's legacy
mode. Raw timings, outputs, counters, and normalized PD inputs are retained.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import random
import statistics
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def worker():
    job = json.load(sys.stdin)
    # This insertion occurs before importing fastunknot. It lets an isolated
    # legacy worker genuinely use the immutable baseline package, not the copy.
    sys.path.insert(0, job["package_root"])
    from fastunknot import khovanov_rank
    from fastunknot.scan import ScanLimit
    options = {"order": job["order"], "shape_cache": job["shape_cache"],
               "race": 1, "seconds": job["seconds"]}
    if job["mode"] != "legacy" or not job["external_baseline"]:
        options["composition"] = job["mode"]
    try:
        warm = khovanov_rank(job["pd"], **options)
        started = time.perf_counter()
        result = khovanov_rank(job["pd"], **options)
        elapsed = time.perf_counter() - started
    except ScanLimit as exc:
        print(json.dumps({"status": "LIMIT", "reason": str(exc)}))
        return
    if (warm["rank"], warm["by_degree"]) != (result["rank"], result["by_degree"]):
        raise AssertionError("warm and timed scans disagree")
    print(json.dumps({"status": "OK", "seconds": elapsed,
                      "rank": result["rank"], "reduced_rank": result["reduced_rank"],
                      "by_degree": result["by_degree"], "stats": result["stats"],
                      "order": result["order"], "mode": job["mode"]}))


def main():
    if sys.argv[1:] == ["--worker"]:
        worker()
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "paired_scanner_benchmark.json")
    parser.add_argument("--baseline-root", type=Path)
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--seconds", type=float, default=20)
    args = parser.parse_args()
    if args.repeats < 1 or args.seconds <= 0:
        parser.error("repeats and seconds must be positive")
    sys.path.insert(0, str(ROOT))
    from fastunknot import Diagram
    from fastunknot.ordering import best_scan_order, repeated_stages
    from fastunknot.simplify import simplify
    import hard_unknots

    names = ("trefoil", "figure_eight", "conway", "kinoshita_terasaka", "hard_unknot_8",
             "torus_3_5", "torus_3_7", "hard_unknot_27", "stress_braid5_36")
    metadata = {"python": sys.version, "platform": platform.platform(), "repeats": args.repeats,
                "clock": "time.perf_counter", "one_process_per_sample": True,
                "warmups_per_sample": 1, "paired_same_order": True,
                "configuration_order": "deterministically shuffled per repetition, seed 10072026",
                "excludes": "imports, fixture parsing, validation, and order selection",
                "includes": "all crossing transfer, cancellation, rank, and stats work",
                "legacy_source": "immutable supplied baseline" if args.baseline_root else "integrated legacy",
                "scan_seconds_cap": args.seconds,
                "algorithm_comparison": {
                    "legacy": "original Planar composition and transfer",
                    "adaptive": "AdaptivePlanar; rigorous support/expansion switch, dense_factor=2",
                    "dense": "AdaptivePlanar(force_dense=True), with exact identity shortcuts"},
                "warning": "shared-container timings; does not establish a global pipeline improvement"}
    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.exists():
        metadata["cpu"] = next((line.split(":", 1)[1].strip() for line in cpuinfo.read_text().splitlines()
                                if line.startswith("model name")), "unknown")
    module_names = ("scan.py", "scan_fast.py", "planar.py", "dense_compose.py")
    metadata["integrated_source_sha256"] = {
        name: hashlib.sha256((ROOT / "fastunknot" / name).read_bytes()).hexdigest()
        for name in module_names}
    if args.baseline_root:
        metadata["baseline_source_sha256"] = {
            name: hashlib.sha256((args.baseline_root / "fastunknot" / name).read_bytes()).hexdigest()
            for name in module_names if name != "dense_compose.py"}
    output = {"metadata": metadata, "fixtures": []}
    rng = random.Random(10072026)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for name in names:
        if name == "hard_unknot_27":
            diagram = simplify(Diagram.from_braid(4, hard_unknots.make(4, seed=38)), r3=False)[0]
            if diagram.crossings != 27:
                raise AssertionError("hard-unknot generator fixture changed")
            source_input = {"generator": "simplify(Diagram.from_braid(4, hard_unknots.make(4, seed=38)), r3=False)[0]",
                            "generator_sha256": hashlib.sha256((ROOT / "hard_unknots.py").read_bytes()).hexdigest()}
        else:
            input_path = ROOT / "examples" / (name + ".json")
            diagram = Diagram.from_json(json.loads(input_path.read_text()))
            source_input = {"file": "examples/" + name + ".json",
                            "sha256": hashlib.sha256(input_path.read_bytes()).hexdigest()}
        pd = [list(row) for row in diagram.pd]
        order = best_scan_order(diagram.pd, tries=min(diagram.crossings, 12))
        shape_cache = len(order) >= 16 and 8 * repeated_stages(diagram.pd, order) >= len(order)
        row = {"name": name, "crossings": diagram.crossings, "pd": pd, "order": order,
               "pd_sha256": hashlib.sha256(json.dumps(pd, separators=(",", ":")).encode()).hexdigest(),
               "source_input": source_input,
               "shape_cache": shape_cache, "samples": [], "summary": {}}
        expected = None
        for repetition in range(args.repeats):
            modes = ["legacy", "adaptive", "dense"]
            rng.shuffle(modes)
            for mode in modes:
                external = mode == "legacy" and args.baseline_root is not None
                package_root = args.baseline_root.resolve() if external else ROOT
                job = {"pd": pd, "order": order, "shape_cache": shape_cache,
                       "mode": mode, "package_root": str(package_root),
                       "external_baseline": external, "seconds": args.seconds}
                run = subprocess.run([sys.executable, str(Path(__file__).resolve()), "--worker"],
                                     input=json.dumps(job), capture_output=True, text=True,
                                     cwd=ROOT, timeout=2 * args.seconds + 10)
                if run.returncode != 0:
                    raise RuntimeError(f"worker failed for {name}/{mode}: {run.stderr}")
                result = json.loads(run.stdout)
                result["repetition"] = repetition
                result["mode"] = mode
                row["samples"].append(result)
                if result["status"] == "OK":
                    answer = result["rank"], result["by_degree"]
                    if expected is None:
                        expected = answer
                    elif answer != expected:
                        raise AssertionError(f"scanner disagreement on {name}/{mode}")
                    if result["order"] != order:
                        raise AssertionError("a worker changed the fixed order")
        for mode in ("legacy", "adaptive", "dense"):
            samples = [item["seconds"] for item in row["samples"]
                       if item["mode"] == mode and item["status"] == "OK"]
            row["summary"][mode] = {"completed": len(samples),
                                    "median_seconds": statistics.median(samples) if samples else None,
                                    "min_seconds": min(samples) if samples else None,
                                    "max_seconds": max(samples) if samples else None}
        baseline = row["summary"]["legacy"]["median_seconds"]
        for mode in ("adaptive", "dense"):
            value = row["summary"][mode]["median_seconds"]
            row["summary"][mode]["ratio_to_legacy"] = value / baseline if value and baseline else None
        output["fixtures"].append(row)
        args.output.write_text(json.dumps(output, indent=2) + "\n")
        print(json.dumps({"name": name, "reduced_rank": expected[0] // 2 if expected else None,
                          **{mode: values["median_seconds"] for mode, values in row["summary"].items()}}),
              flush=True)


if __name__ == "__main__":
    main()
