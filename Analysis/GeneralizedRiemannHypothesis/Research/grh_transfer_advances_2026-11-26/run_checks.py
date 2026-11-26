#!/usr/bin/env python3
"""Run the packaged exact mathematical checks; write a reviewable run manifest."""
from pathlib import Path
import argparse
import datetime
import json
import subprocess
import sys
import time


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled; do not use Python -O.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--new-only", action="store_true")
    parser.add_argument("--skip-hnf", action="store_true",
                        help="Skip the independent check requiring SymPy.")
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    logs = base / "rerun_logs"
    logs.mkdir(exist_ok=True)
    jobs = [
        ("six_graph_cases", "checks/graphs", ["verify_even_extensions.py"]),
        ("n50_main", "checks/graphs/n50", ["certify_n50.py"]),
        ("n50_independent", "checks/graphs/n50", ["verify_n50_independent.py"]),
        ("coefficient_window", "checks/local", ["verify_log_window.py"]),
        ("depth_p2", "checks/local", ["coefficient_depth.py", "--p", "2",
                                      "--cutoff", "48", "--out", "depth_p2_48.json"]),
        ("depth_p3", "checks/local", ["coefficient_depth.py", "--p", "3",
                                      "--cutoff", "100", "--out", "depth_p3_100.json"]),
        ("congruence", "checks/congruence", ["check_congruence_lengths.py"]),
    ]
    if not args.skip_hnf:
        jobs.append(("depth_hnf", "checks/local", ["verify_depth_hnf.py"]))
    if not args.new_only:
        jobs.extend((name, "checks/predecessors", [script]) for name, script in [
            ("prior_graph", "verify_graph.py"),
            ("prior_permutations", "verify_by_permutations.py"),
            ("prior_small_cycles", "verify_small_cycles.py"),
            ("prior_density_gap", "check_integer_gap.py"),
            ("prior_density_prefix", "check_integer_prefix.py"),
        ])
    manifest = {
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "python": sys.version,
        "new_only": args.new_only,
        "hnf_skipped": args.skip_hnf,
        "status": "running",
        "checks": [],
        "scope": "Exact arithmetic checks; no Lean kernel verification.",
    }
    for name, directory, command in jobs:
        print(f"Running {name} ...", flush=True)
        start = time.monotonic()
        log_path = logs / f"{name}.log"
        with log_path.open("w") as output:
            result = subprocess.run([sys.executable, *command], cwd=base / directory,
                                    stdout=output, stderr=subprocess.STDOUT)
        manifest["checks"].append({
            "name": name, "directory": directory, "command": command,
            "exit_code": result.returncode,
            "seconds": round(time.monotonic() - start, 3),
            "log": str(log_path.relative_to(base)),
        })
        manifest["status"] = "failed" if result.returncode else "running"
        (logs / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        if result.returncode:
            print(f"FAILED: see {log_path}", file=sys.stderr)
            return result.returncode
        print(f"Passed {name}.", flush=True)
    manifest["status"] = "all requested checks passed"
    manifest["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    (logs / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(manifest["status"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
