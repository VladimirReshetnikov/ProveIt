#!/usr/bin/env python3
"""Reproduce the package's finite certificates; optionally replay inherited checks."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay-inherited", action="store_true")
    parser.add_argument("--upstream", type=Path, help="Optional full pinned grh-lean checkout")
    args = parser.parse_args()
    base = Path(__file__).resolve().parents[1]
    certificates = base/"certificates"
    certificates.mkdir(exist_ok=True)
    tasks = [
        ("checks/verify_trace_depth.py", "trace_depth.json", []),
        ("checks/verify_transfer_extensions.py", "transfer_extensions.json", []),
        ("checks/euler_factor_check.py", "euler_factor.json", []),
        ("checks/verify_density_gap_independent.py", "density_gap_independent.json", []),
    ]
    if args.upstream:
        tasks.append(("checks/upstream_audit.py", "upstream_audit.json",
                      [str(args.upstream.resolve())]))
    if args.replay_inherited:
        tasks.extend([
            ("evidence/prior_density/checks/check_integer_gap.py", "inherited_integer_gap.txt", []),
            ("evidence/prior_density/checks/check_integer_prefix.py", "inherited_integer_prefix.txt", []),
        ])
    results = []
    for script, filename, extra in tasks:
        completed = subprocess.run([sys.executable, str(base/script), *extra],
                                   cwd=base, capture_output=True, text=True, check=True)
        if filename.endswith(".json"):
            json.loads(completed.stdout)
        (certificates/filename).write_text(completed.stdout)
        if completed.stderr:
            (certificates/(filename+".stderr")).write_text(completed.stderr)
        results.append({"script":script, "status":"passed", "certificate":filename})
        print("PASS", script, flush=True)
    (certificates/"check_summary.json").write_text(json.dumps({
        "meaning":"Exact finite checks and optional static audit; not a Lean kernel replay.",
        "results":results}, indent=2)+"\n")

if __name__ == "__main__":
    main()
