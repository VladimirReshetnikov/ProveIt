#!/usr/bin/env python3
"""Portable bounded shared-selector census. Python standard library + C++17.

This is a discovery experiment, not a verifier for the ZFC calibration.
No-survivor output is not a state lower bound or semantic inequivalence proof.
"""
from pathlib import Path
import argparse
import concurrent.futures
import hashlib
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parent
SOURCES = {"opposite": "shared_selector_joint.cpp", "same": "shared_selector_general.cpp"}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def verify_recorded():
    manifest = json.loads((ROOT / "manifest.json").read_text())
    for name, expected in manifest["files"].items():
        assert digest(ROOT / name) == expected, name
    assert digest(ROOT / "inputs/dr215.native.tm") == manifest["dr215_sha256"]
    assert digest(ROOT / "inputs/k215.native.tm") == manifest["k215_sha256"]
    rows = json.loads((ROOT / "inventory/marker_pairs.json").read_text())
    assert len(rows) == 21
    derived = {
        "opposite": [{"pairs": [[a["u"], a["v"]], [b["u"], b["v"]]], "exceptional_symbols": [0, 1]}
                     for a in rows if a["bit"] == 0 for b in rows
                     if b["bit"] == 1 and not {a["u"], a["v"]} & {b["u"], b["v"]}],
        "same": [{"pairs": [[a["u"], a["v"]], [b["u"], b["v"]]], "exceptional_symbols": [a["bit"], b["bit"]]}
                 for i, a in enumerate(rows) for b in rows[i + 1:]
                 if a["bit"] == b["bit"] and not {a["u"], a["v"]} & {b["u"], b["v"]}],
    }
    total = {key: 0 for key in ("pairs", "candidates", "evaluated", "uniformly_pruned", "survivors")}
    for suite, count in (("opposite", 105), ("same", 95)):
        inventory = json.loads((ROOT / f"inventory/{suite}.json").read_text())
        recorded = json.loads((ROOT / f"recorded/{suite}.json").read_text())
        assert inventory == derived[suite]
        assert len(inventory) == recorded["pairs"] == count
        assert len(recorded["results"]) == count
        assert recorded["table_sha256"] == manifest["dr215_sha256"]
        assert recorded["source_cpp_sha256"] == digest(ROOT / SOURCES[suite])
        assert [r["role_pairs"] for r in recorded["results"]] == [r["pairs"] for r in inventory]
        for r in recorded["results"]:
            assert r["radius"] == 7 and r["fuel"] == 97 and not r["all_first_directions"]
            assert r["candidates"] == 2 * 4 * (4 * 214) ** 2 == 5861888
            assert r["evaluated"] + r["uniformly_pruned"] == r["candidates"]
            assert r["survivors"] == 0
        for key in ("candidates", "evaluated", "uniformly_pruned", "survivors"):
            assert recorded[key] == sum(r[key] for r in recorded["results"])
        for key in total:
            total[key] += recorded[key]
    assert total == {"pairs": 200, "candidates": 1172377600, "evaluated": 707406332,
                     "uniformly_pruned": 464971268, "survivors": 0}
    print(json.dumps({"status": "RECORDED_HASHES_AND_ACCOUNTING_PASS", **total}, indent=2))


def compile_scanner(suite, build, compiler):
    build.mkdir(parents=True, exist_ok=True)
    executable = (build / ("selector_" + suite)).resolve()
    subprocess.run([compiler, "-std=c++17", "-O3", "-Wall", "-Wextra",
                    str(ROOT / SOURCES[suite]), "-o", str(executable)], check=True)
    return executable


def run_suite(suite, output, compiler, jobs, limit=None, all_directions=False):
    output = output.resolve()
    dest = output / suite
    dest.mkdir(parents=True, exist_ok=True)
    executable = compile_scanner(suite, output / "build", compiler)
    inventory = json.loads((ROOT / f"inventory/{suite}.json").read_text())
    if limit is not None:
        inventory = inventory[:limit]
    table = ROOT / "inputs/dr215.native.tm"

    def run(item):
        pair = [q for p in item["pairs"] for q in p]
        prefix = dest / "-".join(map(str, pair))
        command = [str(executable), str(table), "0", str(prefix),
                   "1" if all_directions else "0", *map(str, pair)]
        with prefix.with_suffix(".log").open("w") as log:
            subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, check=True)
        result = json.loads(prefix.with_suffix(".json").read_text())
        print(f"{suite}: {pair}; survivors={result['survivors']}", flush=True)
        return result

    start = time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        results = list(pool.map(run, inventory))
    result = {
        "status": "BOUNDED_DISCOVERY_REPLAY_COMPLETE",
        "suite": suite,
        "pairs": len(results),
        "results": results,
        "wall_seconds": time.monotonic() - start,
        "table_sha256": digest(table),
        "source_cpp_sha256": digest(ROOT / SOURCES[suite]),
        "all_first_directions": all_directions,
        "limit": limit,
        "scope": "Positive local common endpoints, radius7/fuel97. No state lower bound or semantic refutation.",
    }
    for key in ("candidates", "evaluated", "uniformly_pruned", "survivors"):
        result[key] = sum(r[key] for r in results)
    (dest / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    if limit is None and not all_directions:
        recorded = json.loads((ROOT / f"recorded/{suite}.json").read_text())
        for key in ("pairs", "candidates", "evaluated", "uniformly_pruned", "survivors"):
            assert result[key] == recorded[key], (suite, key, result[key], recorded[key])
    print(json.dumps({key: value for key, value in result.items() if key != "results"}, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-recorded", action="store_true")
    parser.add_argument("--suite", choices=("opposite", "same", "all"))
    parser.add_argument("--output", type=Path, default=ROOT / "replay")
    parser.add_argument("--compiler", default=os.environ.get("CXX", "g++"))
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--all-entry-directions", action="store_true")
    args = parser.parse_args()
    assert args.jobs > 0 and (args.limit is None or args.limit > 0)
    if args.verify_recorded or args.suite is None:
        verify_recorded()
    if args.suite:
        suites = ("opposite", "same") if args.suite == "all" else (args.suite,)
        for suite in suites:
            run_suite(suite, args.output, args.compiler, args.jobs, args.limit, args.all_entry_directions)


if __name__ == "__main__":
    main()
