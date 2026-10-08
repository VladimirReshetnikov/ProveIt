"""Portable rerun of the recorded finite-target benchmark.

The solver and independent checker are imported from ../../implementation/fast;
baseline invariant methods are loaded from ../../baseline/fast under a distinct
package name. No production implementation is duplicated here. Exact measured
fixture bytes are retained in this directory's fixtures/ subdirectory.

The recorded JSON is never overwritten by default. --smoke only checks imports,
one certificate, and all recorded fixture hashes; it does not rerun timings.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import importlib.util
import json
import platform
import statistics
import sys
import time
from pathlib import Path


HERE = Path(__file__).resolve().parent
BUNDLE = HERE.parents[1]


def load_implementations(implementation_root, baseline_root):
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(implementation_root))
    import fastunknot
    from fastunknot.finite_quotient import find_a5_by_seeds, find_a5_certificate, wirtinger_seed_plan
    from fastunknot.finite_quotient_check import verify_certificate

    package = baseline_root / "fastunknot"
    if not (package / "__init__.py").is_file():
        raise FileNotFoundError("baseline fastunknot package not found at " + str(package))
    alias = "quotient_benchmark_baseline"
    spec = importlib.util.spec_from_file_location(alias, package / "__init__.py",
                                                  submodule_search_locations=[str(package)])
    if spec is None or spec.loader is None:
        raise ImportError("could not load the baseline package")
    baseline = importlib.util.module_from_spec(spec)
    sys.modules[alias] = baseline
    spec.loader.exec_module(baseline)
    baseline_filters = importlib.import_module(alias + ".filters")
    return (fastunknot, baseline, baseline_filters, find_a5_by_seeds,
            find_a5_certificate, wirtinger_seed_plan, verify_certificate)


def image_group_order(certificate):
    """Independent closure of the explicitly given permutation generators."""
    generators = {tuple(p) for p in certificate["edge_images"]}
    identity = tuple(range(5))
    group, queue = {identity}, [identity]
    while queue:
        a = queue.pop()
        for b in generators:
            c = tuple(a[b[i]] for i in range(5))
            if c not in group:
                group.add(c)
                queue.append(c)
    return len(group)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "finite_quotient_benchmark_rerun.json")
    parser.add_argument("--repeats", type=int, default=9)
    parser.add_argument("--include-csp", action="store_true")
    parser.add_argument("--fixtures", type=Path, default=HERE / "fixtures")
    parser.add_argument("--implementation-root", type=Path, default=BUNDLE / "implementation/fast")
    parser.add_argument("--baseline-root", type=Path, default=BUNDLE / "baseline/fast")
    parser.add_argument("--smoke", action="store_true")
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("repeats must be positive")
    (production, baseline, baseline_filters, find_a5_by_seeds,
     find_a5_certificate, wirtinger_seed_plan, verify_certificate) = load_implementations(
         args.implementation_root.resolve(), args.baseline_root.resolve())
    if args.smoke:
        recorded = json.loads((HERE / "finite_quotient_benchmark.json").read_text())
        for row in recorded["fixtures"]:
            source = args.fixtures / (row["name"] + ".json")
            if hashlib.sha256(source.read_bytes()).hexdigest() != row["fixture_sha256"]:
                raise AssertionError("recorded fixture hash mismatch: " + row["name"])
        diagram = production.Diagram.from_json(json.loads((args.fixtures / "conway.json").read_text()))
        certificate = json.loads((HERE / "certificates/conway_certificate.json").read_text())
        checked = verify_certificate(diagram.pd, certificate)
        if not checked["valid"]:
            raise AssertionError(checked["reason"])
        print(json.dumps({"status": "PASS", "production": production.__file__,
                          "baseline": baseline.__file__, "recorded_fixture_hashes": 5,
                          "certificate": "conway"}, indent=2))
        return

    names = ("conway", "kinoshita_terasaka", "hard_unknot_8", "torus_3_5", "stress_braid5_36")
    metadata = {"python": sys.version, "platform": platform.platform(), "repeats": args.repeats,
                "clock": "time.perf_counter", "mode": "one warm-up then warm median",
                "includes": "extraction, seed finding/search, and independent replay",
                "excludes": "imports and fixture JSON parsing",
                "production_package": str(args.implementation_root),
                "baseline_package": str(args.baseline_root),
                "fixtures": str(args.fixtures),
                "warning": "microbenchmarks in a shared container; no universal speedup claim"}
    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.exists():
        metadata["cpu"] = next((line.split(":", 1)[1].strip() for line in cpuinfo.read_text().splitlines()
                                if line.startswith("model name")), "unknown")
    output = {"metadata": metadata, "fixtures": []}

    def timed(call):
        call()
        samples, result = [], None
        for _ in range(args.repeats):
            started = time.perf_counter()
            result = call()
            samples.append(time.perf_counter() - started)
        return result, {"median_seconds": statistics.median(samples),
                        "min_seconds": min(samples), "max_seconds": max(samples),
                        "samples_seconds": samples}

    for name in names:
        fixture = args.fixtures / (name + ".json")
        value = json.loads(fixture.read_text())
        diagram = production.Diagram.from_json(value)
        original = baseline.Diagram.from_json(value)
        if diagram.pd != original.pd:
            raise AssertionError("production and baseline normalization disagree")
        seed_plan = wirtinger_seed_plan(diagram)
        row = {"name": name, "crossings": diagram.crossings,
               "fixture_sha256": hashlib.sha256(fixture.read_bytes()).hexdigest(),
               "seeds": seed_plan["seed_arcs"], "measurements": {}}
        result, measurement = timed(lambda: find_a5_by_seeds(diagram, max_assignments=100000))
        measurement.update(status=result["status"], assignments=result["assignments"],
                           attempts=result["attempts"])
        if result["certificate"] is not None:
            measurement["image_group_order"] = image_group_order(result["certificate"])
            assert verify_certificate(diagram.pd, result["certificate"])["valid"]
        row["measurements"]["a5_seed"] = measurement
        if args.include_csp:
            result, measurement = timed(lambda: find_a5_certificate(diagram, max_nodes=10000))
            measurement.update(status=result["status"], **result["stats"])
            row["measurements"]["a5_csp"] = measurement
        result, measurement = timed(lambda: baseline.recognize(original))
        measurement.update(status=result.status, method=result.method)
        row["measurements"]["existing_default"] = measurement
        if diagram.crossings <= 11:
            result, measurement = timed(lambda: baseline_filters.jones_obstruction(original))
            measurement["status"] = "KNOTTED" if result else "INCONCLUSIVE"
            row["measurements"]["existing_jones_filter"] = measurement
            result, measurement = timed(lambda: baseline.khovanov_rank(original.pd))
            measurement["reduced_rank"] = result["reduced_rank"]
            row["measurements"]["existing_khovanov_raw"] = measurement
        if name in ("conway", "kinoshita_terasaka"):
            result, measurement = timed(lambda: baseline.recognize(original, use_jones=False))
            measurement.update(status=result.status, method=result.method)
            row["measurements"]["existing_no_jones"] = measurement
        output["fixtures"].append(row)
        print(json.dumps({"name": name,
                          **{key: round(value["median_seconds"] * 1000, 4)
                             for key, value in row["measurements"].items()}}), flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n")


if __name__ == "__main__":
    main()
