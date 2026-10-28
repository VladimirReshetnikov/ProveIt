#!/usr/bin/env python3
"""Replay exact certificates without changing the delivered results.

The default suite needs only Python's standard library. The optional --full
suite also replays the finite crossing-operator experiments and needs NumPy.
This program is a certificate verifier, not a SAT solver.
"""
from argparse import ArgumentParser
from pathlib import Path
import json
import subprocess
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true",
                        help="also repeat the NumPy crossing-operator probes")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    output = root / "replay_results"
    output.mkdir(exist_ok=True)
    summary = {"status": "PASS", "checks": {}, "operator_probes_run": args.full}
    jobs = [
        ("certificate", "verify_certificates.py", "certificate_normal.json"),
        ("independent_audit", "independent_audit.py", "independent_incoming_audit.json"),
        ("quadratic", "check_quadratic_rectangular.py", "quadratic_rectangular_checks.json"),
    ]
    for label, script, delivered_name in jobs:
        records = []
        print("Running", label, "(normal and -O)...", flush=True)
        for suffix, options in [("normal", []), ("optimized", ["-O"])]:
            command = [sys.executable, *options, str(root / "code" / script)]
            run = subprocess.run(command, check=True, capture_output=True, text=True)
            parsed = json.loads(run.stdout)
            (output / (label + "_" + suffix + ".json")).write_text(run.stdout)
            records.append(parsed)
        require(records[0] == records[1],
                label + ": normal and optimized mathematical outputs disagree")
        delivered = root / "results" / delivered_name
        require(delivered.is_file(), label + ": delivered result is absent")
        require(records[0] == json.loads(delivered.read_text()),
                label + ": replay differs from delivered mathematical result")
        summary["checks"][label] = {
            "normal_optimized_identical": True,
            "matches_delivered_result": True,
        }
        if label == "certificate":
            data = records[0]
            summary["safe_time"] = data["new_schedule"]["safe_time"]
            summary["safe_space"] = data["new_schedule"]["safe_space"]
            summary["old_backend_time_space_interval"] = data["old_schedule"]["branch_intervals"][0]
            summary["new_backend_time_interval"] = data["new_schedule"]["branch_intervals"][-1]
            summary["new_backend_space_interval"] = data["new_schedule"]["space_intervals"][0]
        print("PASS:", label, flush=True)
    if args.full:
        for name, h, all_s, delivered_name in [
            ("rank_probe_results", 6, True, "rank_probe_results.json"),
            ("rank_probe_central", 8, False, "rank_probe_central.json"),
        ]:
            target = output / (name + ".json")
            command = [
                sys.executable, str(root / "code" / "rank_probe.py"),
                "--max-h", str(h), "--out", str(target),
            ]
            if all_s:
                command.append("--all-s")
            print("Running", name, "...", flush=True)
            run = subprocess.run(command, check=True, capture_output=True, text=True)
            (output / (name + ".log")).write_text(run.stdout)
            require(json.loads(target.read_text()) ==
                    json.loads((root / "results" / delivered_name).read_text()),
                    name + ": finite operator result differs")
            summary["checks"][name] = {"matches_delivered_result": True}
            print("PASS:", name, flush=True)
    (output / "verification_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print("All requested checks passed.")
    print("Safe eventual time coefficient:", summary["safe_time"])
    print("Safe eventual space coefficient:", summary["safe_space"])
    print("Fresh results:", output)


if __name__ == "__main__":
    main()
