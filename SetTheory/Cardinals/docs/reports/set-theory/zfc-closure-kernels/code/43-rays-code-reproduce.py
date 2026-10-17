#!/usr/bin/env python3
"""Replay the report's finite diagnostics, without overwriting supplied records.

Default: identities, support orbits, public table, fixed gap 36, exact
countertraces, and 1M blank moves. --full adds complete affine/fixed gap tables.
--long-run adds the recorded 100M blank moves. No proof assistant is invoked.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
MACHINE = ROOT / "code" / "machine"
DATA = ROOT / "data" / "machine"
sys.dont_write_bytecode = True


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def read_json(path):
    return json.loads(Path(path).read_text())


def no_times(value):
    if isinstance(value, dict):
        return {k: no_times(v) for k, v in value.items()
                if k not in {"elapsed", "elapsed_seconds"}}
    if isinstance(value, list):
        return [no_times(v) for v in value]
    return value


def identities():
    manifest = read_json(DATA / "machine_manifest.json")
    checked = 0
    for row in manifest["files"]:
        path = (ROOT / row["path"]).resolve()
        require(path.is_relative_to(ROOT), "Manifest path escaped bundle")
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        require(actual == row["sha256"], "Identity mismatch: " + row["path"])
        checked += 1
    archive_manifest = ROOT / "MANIFEST.json"
    if archive_manifest.exists():
        for row in read_json(archive_manifest)["files"]:
            path = (ROOT / row["path"]).resolve()
            require(path.is_relative_to(ROOT), "Archive path escaped bundle")
            require(hashlib.sha256(path.read_bytes()).hexdigest() == row["sha256"],
                    "Archive identity mismatch: " + row["path"])
            checked += 1
    return {"status": "passed", "identities_checked": checked}


def run_job(label, script, arguments, output):
    before = time.monotonic()
    proc = subprocess.run([sys.executable, "-B", str(script), *map(str, arguments)],
                          cwd=ROOT, text=True, capture_output=True)
    (output / (label + ".log")).write_text(proc.stdout + proc.stderr)
    require(proc.returncode == 0, f"{label} failed; inspect its log")
    return {"name": label, "status": "passed",
            "elapsed_seconds": time.monotonic() - before}


def compare_gap_rows(actual, expected):
    expected_by_gap = {r["gap"]: r for r in expected["gaps"]}
    for row in actual["gaps"]:
        require(no_times(row) == no_times(expected_by_gap[row["gap"]]),
                f"Gap {row['gap']} record changed")


def compare_blank(actual, expected):
    keys = ("steps", "state", "head", "ones", "dispatch_visits",
            "generic_gap_histogram", "final_all_ones")
    for key in keys:
        require(actual[key] == expected[key], f"Blank-run field changed: {key}")


def main():
    require(__debug__, "Run without -O; attributed inputs use assertions")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--full", action="store_true")
    parser.add_argument("--long-run", action="store_true")
    args = parser.parse_args()
    output = args.output.resolve()
    require(not output.is_relative_to(ROOT),
            "Use an output directory outside the immutable report bundle")
    output.mkdir(parents=True, exist_ok=True)
    jobs = []
    identity_result = identities()
    print(json.dumps(identity_result), flush=True)

    result_file = output / "support_orbits.json"
    jobs.append(run_job("support_orbits", ROOT / "code" / "support_orbits.py",
                        ["--output", result_file], output))
    require(read_json(result_file) == read_json(ROOT / "data/support_orbits.json"),
            "Finite support diagnostic changed")

    jobs.append(run_job("public_table",
                        MACHINE / "upstream/ZF/m253/tools/generate_candidate.py",
                        ["--check"], output))

    result_file = output / "exact_gaps.json"
    gaps = "32,33,34,35,36,37,38,40" if args.full else "36"
    jobs.append(run_job("exact_gaps", MACHINE / "exact_gap_audit.py",
                        ["--source35", MACHINE / "source35_runtime252_short_gap.py",
                         "--gaps", gaps, "--output", result_file], output))
    compare_gap_rows(read_json(result_file),
                     read_json(DATA / "runtime252_exact_gaps.json"))

    if args.full:
        result_file = output / "affine_gaps.json"
        jobs.append(run_job("affine_gaps", MACHINE / "affine_gap_audit.py",
                            ["--output", result_file], output))
        compare_gap_rows(read_json(result_file),
                         read_json(DATA / "runtime252_gaps.json"))

    result_file = output / "representative_gaps.json"
    jobs.append(run_job("representative_gaps",
                        MACHINE / "representative_gap_checks.py",
                        ["--source35", MACHINE / "source35_runtime252_short_gap.py",
                         "--census", DATA / "runtime252_exact_gaps.json",
                         "--output", result_file], output))
    actual = read_json(result_file)
    expected = read_json(DATA / "runtime252_representative_gaps.json")
    for key in ("prepared_traces", "prior_source35_affine_false_alarm", "counts"):
        require(no_times(actual[key]) == no_times(expected[key]),
                "Exact trace data changed: " + key)
    require(actual["counts"] == {"different_complete_frame": 16, "exact_target": 4},
            "Unexpected prepared-trace census")

    for limit, suffix in [(1000000, "1m")] + (
            [(100000000, "100m")] if args.long_run else []):
        result_file = output / f"runtime252_{suffix}.json"
        jobs.append(run_job(f"blank_{suffix}", MACHINE / "inspect_runtime252.py",
                            ["--start", "0", "--limit", limit,
                             "--output", result_file], output))
        compare_blank(read_json(result_file),
                      read_json(DATA / f"runtime252_seed0_{suffix}.json"))

    result = {"status": "passed",
              "scope": "Finite reproduction only; no new kernel proof or "
                       "consistency-equivalent sub-253-state machine.",
              "mode": {"full": args.full, "long_run": args.long_run},
              "identities": identity_result, "jobs": jobs}
    (output / "reproduction_result.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

