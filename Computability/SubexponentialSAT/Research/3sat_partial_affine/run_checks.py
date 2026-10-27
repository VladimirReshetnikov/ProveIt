#!/usr/bin/env python3
"""Replay all delivered exact certificates and finite algebra checks."""
from pathlib import Path
import argparse
import ast
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
CHECKS = [
    ("audit_round5_new15.py", "round5_new15_audit.json"),
    ("check_partial_affine_joint.py", "partial_affine_joint_result.json"),
    ("round5_affine_certificate.py", "round5_affine_certificate_results.json"),
    ("check_rectangular_joint.py", "rectangular_joint_result.json"),
    ("audit_round5_baseline.py", "round5_baseline_audit.json"),
    ("check_tensor_regrouping.py", "tensor_regrouping.json"),
    ("verify_occurrence_bridge.py", "occurrence_bridge_checks.json"),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--optimized", action="store_true",
                        help="run every checker under python -O")
    args = parser.parse_args()
    for path in (ROOT / "code").glob("*.py"):
        if any(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(path.read_text()))):
            raise RuntimeError("A checker contains an assertion disabled by -O: " + path.name)
    (ROOT / "results").mkdir(exist_ok=True)
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    records = []
    for script, destination in CHECKS:
        command = [sys.executable] + (["-O"] if args.optimized else [])
        command.append(str(ROOT / "code" / script))
        run = subprocess.run(command, cwd=ROOT, env=env,
                             capture_output=True, text=True)
        if run.returncode:
            print(run.stdout[-8000:])
            print(run.stderr[-8000:], file=sys.stderr)
            raise SystemExit("FAILED: " + script)
        path = ROOT / "results" / destination
        data = path.read_bytes()
        json.loads(data)
        records.append({"checker": script, "result": "results/" + destination,
                        "sha256": hashlib.sha256(data).hexdigest(), "status": "PASS"})
        print("PASS " + script, flush=True)
    mode = "optimized" if args.optimized else "ordinary"
    opposite = "ordinary" if args.optimized else "optimized"
    other = ROOT / "results" / ("validation_" + opposite + ".json")
    if other.exists() and json.loads(other.read_text())["checks"] != records:
        raise RuntimeError("Ordinary and optimized replay produced different results")
    summary = {"status": "PASS", "mode": mode,
               "checks_use_explicit_exceptions": True, "checks": records}
    (ROOT / "results" / ("validation_" + mode + ".json")).write_text(
        json.dumps(summary, indent=2) + "\n")
    print("All seven checks passed (" + mode + ").")


if __name__ == "__main__":
    main()
